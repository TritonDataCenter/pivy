/*
 * Newly written portions Copyright 2018 Joyent, Inc.
 * Author: Alex Wilson <alex.wilson@joyent.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Partially derived from the original OpenSSH agent.c.
 *
 * Original copyright and license from OpenSSH:
 *
 * Author: Tatu Ylonen <ylo@cs.hut.fi>
 * Copyright (c) 1995 Tatu Ylonen <ylo@cs.hut.fi>, Espoo, Finland
 *                    All rights reserved
 * The authentication agent program.
 *
 * As far as I am concerned, the code I have written for this software
 * can be used freely for any purpose.  Any derived versions of this
 * software must be clearly marked as such, and if the derived work is
 * incompatible with the protocol description in the RFC file, it must be
 * called by a name other than "ssh" or "Secure Shell".
 *
 * Copyright (c) 2000, 2001 Markus Friedl.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/types.h>
#include <sys/param.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/un.h>
#include <sys/mman.h>

#include <openssl/evp.h>

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <paths.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <unistd.h>

#include "libssh/ssh2.h"
#include "libssh/sshbuf.h"
#include "libssh/sshkey.h"
#include "libssh/authfd.h"
#include "libssh/ssherr.h"

#include "utils.h"
#include "bunyan.h"
#include "debug.h"
#include "tlv.h"
#include "piv.h"
#include "errf.h"

#if defined(__APPLE__)
#include <PCSC/wintypes.h>
#include <PCSC/winscard.h>
#else
#include <wintypes.h>
#include <winscard.h>
#endif

#if defined(__sun)
#include <ucred.h>
#include <procfs.h>
#endif

#include "libssh/digest.h"
#include "libssh/cipher.h"
#include "libssh/ssherr.h"

#define	MINIMUM(a,b) (((a) < (b)) ? (a) : (b))

/*
 * Name of the environment variable containing the process ID of the
 * authentication agent.
 */
#define SSH_AGENTPID_ENV_NAME	"SSH_AGENT_PID"

/*
 * Name of the environment variable containing the pathname of the
 * authentication socket.
 */
#define SSH_AUTHSOCKET_ENV_NAME "SSH_AUTH_SOCK"

/* Listen backlog for sshd, ssh-agent and forwarding sockets */
#define SSH_LISTEN_BACKLOG		128

#define	MAX_PIN_LEN	16

#define	parserrf(sshfunc, rc)	\
    errf("ParseError", ssherrf(sshfunc, rc), \
    "failed to parse request in %s", __func__)
#define	nopinerrf(cause)		\
    errf("NoPINError", cause, "no PIN has been supplied to the agent " \
    "(try ssh-add -X)")
#define	flagserrf(val)		\
    errf("FlagsError", NULL, "unsupported flags value: %x", val)

static struct piv_token *ks = NULL;
static struct piv_token *selk = NULL;
static boolean_t txnopen = B_FALSE;
static uint64_t txntimeout = 0;
static SCARDCONTEXT ctx;
static uint64_t last_update;
static uint64_t last_op;
static uint8_t *guid = NULL;
static size_t guid_len = 0;
static boolean_t sign_9d = B_FALSE;
static boolean_t check_client_uid = B_TRUE;
#if defined(__sun)
static boolean_t check_client_zoneid = B_TRUE;
#endif

static char *pinmem = NULL;
static char *pin = NULL;
static size_t pin_len = 0;

static struct sshkey *cak = NULL;

static struct bunyan_frame *msg_log_frame;

/* Maximum accepted message length */
#define AGENT_MAX_LEN	(256*1024)

typedef enum {
	AUTH_UNUSED,
	AUTH_SOCKET,
	AUTH_CONNECTION
} sock_type;

typedef struct {
	int fd;
	sock_type type;
	pid_t pid;
	gid_t gid;
	char *exepath;
	struct sshbuf *input;
	struct sshbuf *output;
	struct sshbuf *request;
} SocketEntry;

u_int sockets_alloc = 0;
SocketEntry *sockets = NULL;

int max_fd = 0;

const time_t card_probe_interval_nopin = 120;
const time_t card_probe_interval_pin = 30;
const uint card_probe_limit = 3;

time_t card_probe_interval = 120; /* card_probe_interval_nopin */
uint card_probe_fails = 0;

/* pid of shell == parent of agent */
pid_t parent_pid = -1;
time_t parent_alive_interval = 0;

/* pid of process for which cleanup_socket is applicable */
pid_t cleanup_pid = 0;

/* pathname and directory for AUTH_SOCKET */
char socket_name[PATH_MAX + 20];
char socket_dir[PATH_MAX];


/* locking */
#define LOCK_SIZE	32
#define LOCK_SALT_SIZE	16
#define LOCK_ROUNDS	1
int locked = 0;
u_char lock_pwhash[LOCK_SIZE];
u_char lock_salt[LOCK_SALT_SIZE];

extern char *__progname;

/* Default lifetime in seconds (0 == forever) */
//static long lifetime = 0;

static int fingerprint_hash = SSH_FP_HASH_DEFAULT;

extern void bunyan_timestamp(char *, size_t);
static int ssh_dbglevel = BNY_WARN;
static void
sdebug(const char *fmt, ...)
{
	va_list args;
	char ts[128];
	if (ssh_dbglevel > BNY_TRACE)
		return;
	bunyan_timestamp(ts, sizeof (ts));
	va_start(args, fmt);
	fprintf(stderr, "[%s] TRACE: ", ts);
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);
}
static void
error(const char *fmt, ...)
{
	va_list args;
	char ts[128];
	if (ssh_dbglevel > BNY_ERROR)
		return;
	bunyan_timestamp(ts, sizeof (ts));
	va_start(args, fmt);
	fprintf(stderr, "[%s] ERROR: ", ts);
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);
}
static void
fatal(const char *fmt, ...)
{
	va_list args;
	char ts[128];
	va_start(args, fmt);
	bunyan_timestamp(ts, sizeof (ts));
	fprintf(stderr, "[%s] FATAL: ", ts);
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);
	exit(1);
}

static uint64_t
monotime(void)
{
	struct timeval tv;
	uint64_t msec;
	gettimeofday(&tv, NULL);
	msec = tv.tv_sec * 1000;
	msec += tv.tv_usec / 1000;
	return (msec);
}

static void
agent_piv_close(boolean_t force)
{
	uint64_t now = monotime();
	VERIFY(txnopen);
	if (force || now >= txntimeout) {
		bunyan_log(BNY_TRACE, "closing txn",
		    "now", BNY_UINT64, now,
		    "txntimeout", BNY_UINT64, txntimeout, NULL);
		piv_txn_end(selk);
		txnopen = B_FALSE;
	}
}

static void
drop_pin(void)
{
	if (pin_len != 0) {
		bunyan_log(BNY_INFO, "clearing PIN from memory", NULL);
		explicit_bzero(pin, pin_len);
	}
	pin_len = 0;
	card_probe_interval = card_probe_interval_nopin;
}

static errf_t *
auth_cak(void)
{
	struct piv_slot *slot;
	errf_t *err;
	slot = piv_get_slot(selk, PIV_SLOT_CARD_AUTH);
	if (slot == NULL) {
		err = errf("CAKAuthError", NULL, "No key was found in the "
		    "CARD_AUTH (CAK) slot");
		return (err);
	}
	err = piv_auth_key(selk, slot, cak);
	if (err) {
		err = errf("CAKAuthError", err, "Key in CARD_AUTH slot (CAK) "
		    "does not match the configured CAK: this card may be "
		    "a fake!");
		return (err);
	}
	return (NULL);
}

static errf_t *
agent_piv_open(void)
{
	struct piv_slot *slot;
	errf_t *err = NULL;

	if (txnopen) {
		txntimeout = monotime() + 2000;
		return (NULL);
	}

	if (selk == NULL || (err = piv_txn_begin(selk))) {
		errf_free(err);

		selk = NULL;
		if (ks != NULL)
			piv_release(ks);

		err = piv_find(ctx, guid, guid_len, &ks);
		if (err) {
			ks = NULL;
			err = errf("EnumerationError", err, "Failed to "
			    "find specified PIV token on the system");
			return (err);
		}
		selk = ks;

		if (selk == NULL) {
			err = errf("NotFoundError", NULL, "PIV card with "
			    "given GUID is not present on the system");
			if (monotime() - last_update > 5000)
				drop_pin();
			return (err);
		}

		if ((err = piv_txn_begin(selk))) {
			return (err);
		}

		if ((err = piv_select(selk))) {
			piv_txn_end(selk);
			return (err);
		}

		err = piv_read_all_certs(selk);
		if (err && !errf_caused_by(err, "NotFoundError") &&
		    !errf_caused_by(err, "NotSupportedError")) {
			piv_txn_end(selk);
			return (err);
		}
		if (cak != NULL && (err = auth_cak())) {
			piv_txn_end(selk);
			drop_pin();
			return (err);
		}
		last_update = monotime();

	} else {
		if ((err = piv_select(selk))) {
			piv_txn_end(selk);
			return (err);
		}
	}
	if (cak == NULL) {
		slot = piv_get_slot(selk, PIV_SLOT_CARD_AUTH);
		if (slot != NULL)
			VERIFY0(sshkey_demote(piv_slot_pubkey(slot), &cak));
	}
	bunyan_log(BNY_TRACE, "opened new txn", NULL);
	txnopen = B_TRUE;
	txntimeout = monotime() + 2000;
	card_probe_fails = 0;
	return (NULL);
}

static void
probe_card(void)
{
	errf_t *err;
	if (card_probe_fails > card_probe_limit)
		return;
	bunyan_log(BNY_TRACE, "doing idle probe", NULL);

	last_op = monotime();
	if ((err = agent_piv_open())) {
		bunyan_log(BNY_TRACE, "error opening for idle probe",
		    "error", BNY_ERF, err, NULL);
		errf_free(err);
		/*
		 * Allow one failure due to connectivity issues before we
		 * drop the PIN (so that transient glitches aren't so
		 * inconvenient).
		 */
		if (card_probe_fails++ > 0)
			drop_pin();
		selk = NULL;
		return;
	}
	if (cak != NULL && (err = auth_cak())) {
		bunyan_log(BNY_WARN, "CAK authentication failed",
		    "error", BNY_ERF, err, NULL);
		agent_piv_close(B_TRUE);
		/* Always drop PIN on a CAK failure. */
		drop_pin();
		selk = NULL;
		card_probe_fails++;
		return;
	}
	agent_piv_close(B_FALSE);
	card_probe_fails = 0;
}

static errf_t *
wrap_pin_error(errf_t *err, int retries)
{
	if (errf_caused_by(err, "PermissionError")) {
		if (retries == 0) {
			err = errf("TokenLocked", err,
			    "PIV token is locked due to too many "
			    "invalid PIN code attempts");
		} else {
			err = errf("InvalidPIN", err,
			    "Invalid PIN code supplied (%d attempts "
			    "remaining)", retries);
			drop_pin();
		}
	} else if (errf_caused_by(err, "MinRetriesError")) {
		err = errf("TokenLocked", err,
		    "Refusing to use up the last PIN code attempt: "
		    "unlock the token with another tool to clear "
		    "the counter");
		drop_pin();
	}
	return (err);
}

static errf_t *
agent_piv_try_pin(boolean_t canskip)
{
	errf_t *err = NULL;
	uint retries = 1;
	if (pin_len != 0) {
		err = piv_verify_pin(selk, piv_token_default_auth(selk),
		    pin, &retries, canskip);
		err = wrap_pin_error(err, retries);
	}
	return (err);
}

static void
close_socket(SocketEntry *e)
{
	close(e->fd);
	e->fd = -1;
	e->type = AUTH_UNUSED;
	sshbuf_free(e->input);
	sshbuf_free(e->output);
	sshbuf_free(e->request);
	if (e->exepath != NULL)
		free(e->exepath);
}

static int
set_nonblock(int fd)
{
	int val;

	val = fcntl(fd, F_GETFL);
	if (val < 0) {
		error("fcntl(%d, F_GETFL): %s", fd, strerror(errno));
		return (-1);
	}
	if (val & O_NONBLOCK) {
		sdebug("fd %d is O_NONBLOCK", fd);
		return (0);
	}
	sdebug("fd %d setting O_NONBLOCK", fd);
	val |= O_NONBLOCK;
	if (fcntl(fd, F_SETFL, val) == -1) {
		sdebug("fcntl(%d, F_SETFL, O_NONBLOCK): %s", fd,
		    strerror(errno));
		return (-1);
	}
	return (0);
}

static void
sanitise_stdfd(void)
{
	int nullfd, dupfd;

	if ((nullfd = dupfd = open(_PATH_DEVNULL, O_RDWR)) == -1) {
		fprintf(stderr, "Couldn't open /dev/null: %s\n",
		    strerror(errno));
		exit(1);
	}
	while (++dupfd <= STDERR_FILENO) {
		/* Only populate closed fds. */
		if (fcntl(dupfd, F_GETFL) == -1 && errno == EBADF) {
			if (dup2(nullfd, dupfd) == -1) {
				fprintf(stderr, "dup2: %s\n", strerror(errno));
				exit(1);
			}
		}
	}
	if (nullfd > STDERR_FILENO)
		close(nullfd);
}

static void
send_status(SocketEntry *e, int success)
{
	int r;

	if ((r = sshbuf_put_u32(e->output, 1)) != 0 ||
	    (r = sshbuf_put_u8(e->output, success ?
	    SSH_AGENT_SUCCESS : SSH_AGENT_FAILURE)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
}

static void
send_extfail(SocketEntry *e)
{
	int r;

	if ((r = sshbuf_put_u32(e->output, 1)) != 0 ||
	    (r = sshbuf_put_u8(e->output, SSH2_AGENT_EXT_FAILURE)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
}

/* send list of supported public keys to 'client' */
static errf_t *
process_request_identities(SocketEntry *e)
{
	struct sshbuf *msg;
	struct piv_slot *slot = NULL;
	char comment[256];
	uint64_t now;
	int r, n;
	errf_t *err = NULL;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);

	if ((err = agent_piv_open()))
		goto out;

	now = monotime();
	if ((now - last_update) >= card_probe_interval * 1000) {
		last_update = now;
		err = piv_read_all_certs(selk);
		errf_free(err);
		if (cak != NULL && (err = auth_cak())) {
			agent_piv_close(B_TRUE);
			drop_pin();
			goto out;
		}
	}
	agent_piv_close(B_FALSE);

	n = 0;
	while ((slot = piv_slot_next(selk, slot)) != NULL)
		++n;

	if ((r = sshbuf_put_u8(msg, SSH2_AGENT_IDENTITIES_ANSWER)) != 0 ||
	    (r = sshbuf_put_u32(msg, n)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

	while ((slot = piv_slot_next(selk, slot)) != NULL) {
		if (piv_slot_id(slot) == PIV_SLOT_KEY_MGMT)
			continue;
		comment[0] = 0;
		snprintf(comment, sizeof (comment), "PIV_slot_%02X %s",
		    piv_slot_id(slot), piv_slot_subject(slot));
		if ((r = sshkey_puts(piv_slot_pubkey(slot), msg)) != 0 ||
		    (r = sshbuf_put_cstring(msg, comment)) != 0) {
			fatal("%s: put key/comment: %s", __func__,
			    ssh_err(r));
		}
	}
	/*
	 * Always put key mgmt last so that SSH clients not aware of the fact
	 * that this slot is not used for signing by default will be unlikely
	 * to try using it.
	 */
	if ((slot = piv_get_slot(selk, PIV_SLOT_KEY_MGMT)) != NULL) {
		comment[0] = 0;
		snprintf(comment, sizeof (comment), "PIV_slot_%02X %s",
		    piv_slot_id(slot), piv_slot_subject(slot));
		if ((r = sshkey_puts(piv_slot_pubkey(slot), msg)) != 0 ||
		    (r = sshbuf_put_cstring(msg, comment)) != 0) {
			fatal("%s: put key/comment: %s", __func__,
			    ssh_err(r));
		}
	}
	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

out:
	sshbuf_free(msg);
	return (err);
}

/* ssh2 only */
static errf_t *
process_sign_request2(SocketEntry *e)
{
	const u_char *data;
	u_char *signature = NULL;
	u_char *rawsig = NULL;
	size_t dlen, rslen = 0, slen = 0;
	u_int flags;
	int r;
	errf_t *err = NULL;
	struct sshbuf *msg;
	struct sshbuf *buf;
	struct sshkey *key = NULL;
	struct piv_slot *slot = NULL;
	int found = 0;
	enum sshdigest_types hashalg, ohashalg;
	boolean_t canskip = B_TRUE;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((r = sshkey_froms(e->request, &key)) != 0 ||
	    (r = sshbuf_get_string_direct(e->request, &data, &dlen)) != 0 ||
	    (r = sshbuf_get_u32(e->request, &flags)) != 0) {
		err = parserrf("sshbuf_get_string", r);
		goto out;
	}

	if ((err = agent_piv_open()))
		goto out;

	while ((slot = piv_slot_next(selk, slot)) != NULL) {
		if (sshkey_equal(piv_slot_pubkey(slot), key)) {
			found = 1;
			break;
		}
	}
	if (!found || slot == NULL) {
		agent_piv_close(B_FALSE);
		err = errf("NotFoundError", NULL, "specified key not found");
		goto out;
	}
	bunyan_add_vars(msg_log_frame,
	    "slotid", BNY_UINT, (uint)piv_slot_id(slot), NULL);

	if (piv_slot_id(slot) == PIV_SLOT_KEY_MGMT && !sign_9d) {
		err = errf("PermissionError", NULL, "key management key (9d) "
		    "is not allowed to sign data without the -m option");
		goto out;
	}

	if (piv_slot_id(slot) == PIV_SLOT_SIGNATURE)
		canskip = B_FALSE;

pin_again:
	if ((err = agent_piv_try_pin(canskip))) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	if (key->type == KEY_RSA) {
		hashalg = SSH_DIGEST_SHA1;
		if (flags & SSH_AGENT_RSA_SHA2_256)
			hashalg = SSH_DIGEST_SHA256;
		else if (flags & SSH_AGENT_RSA_SHA2_512)
			hashalg = SSH_DIGEST_SHA512;
	} else if (key->type == KEY_ECDSA) {
		switch (sshkey_curve_nid_to_bits(key->ecdsa_nid)) {
		case 256:
			hashalg = SSH_DIGEST_SHA256;
			break;
		case 384:
			hashalg = SSH_DIGEST_SHA384;
			break;
		case 521:
			hashalg = SSH_DIGEST_SHA512;
			break;
		default:
			hashalg = SSH_DIGEST_SHA256;
		}
	}
	ohashalg = hashalg;
	err = piv_sign(selk, slot, data, dlen, &hashalg, &rawsig, &rslen);

	if (errf_caused_by(err, "PermissionError") && pin_len != 0 &&
	    piv_token_is_ykpiv(selk) && canskip) {
		/*
		 * On a YubiKey, slots other than 9C (SIGNATURE) can also be
		 * set to "PIN Always" mode. We might have one, so try again
		 * with forced PIN entry.
		 */
		canskip = B_FALSE;
		goto pin_again;
	} else if (errf_caused_by(err, "PermissionError")) {
		agent_piv_close(B_TRUE);
		err = nopinerrf(err);
		goto out;
	} else if (err) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	agent_piv_close(B_FALSE);

	if (hashalg != ohashalg) {
		err = errf("HashMismatch", NULL,
		    "PIV device signed with a different hash algorithm to "
		    "the one requested (wanted %d, got %d)",
		    (int)ohashalg, (int)hashalg);
		goto out;
	}

	buf = sshbuf_new();
	VERIFY(buf != NULL);
	VERIFY0(sshkey_sig_from_asn1(piv_slot_pubkey(slot), hashalg,
	    rawsig, rslen, buf));
	explicit_bzero(rawsig, rslen);
	free(rawsig);

	signature = calloc(1, sshbuf_len(buf));
	slen = sshbuf_len(buf);
	VERIFY0(sshbuf_get(buf, signature, slen));
	sshbuf_free(buf);

	if ((r = sshbuf_put_u8(msg, SSH2_AGENT_SIGN_RESPONSE)) != 0 ||
	    (r = sshbuf_put_string(msg, signature, slen)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

out:
	sshkey_free(key);
	sshbuf_free(msg);
	explicit_bzero(signature, slen);
	free(signature);
	return (err);
}

static errf_t *
valid_pin(const char *pin)
{
	int i;
	if (strlen(pin) < 6 || strlen(pin) > 8) {
		return (errf("InvalidPIN", NULL, "PIN must be 6-8 characters "
		    "(was given %d)", strlen(pin)));
	}
	for (i = 0; pin[i] != 0; ++i) {
		if (!(pin[i] >= '0' && pin[i] <= '9') &&
		    !(pin[i] >= 'a' && pin[i] <= 'z') &&
		    !(pin[i] >= 'A' && pin[i] <= 'Z')) {
			return (errf("InvalidPIN", NULL, "PIN contains "
			    "invalid characters: '%c'", pin[i]));
		}
	}
	return (NULL);
}

static errf_t *
process_remove_all_identities(SocketEntry *e)
{
	drop_pin();
	send_status(e, 1);
	return (NULL);
}

struct exthandler {
	const char *eh_name;
	errf_t *(*eh_handler)(SocketEntry *, struct sshbuf *);
};
struct exthandler exthandlers[];

static errf_t *
process_ext_ecdh(SocketEntry *e, struct sshbuf *buf)
{
	int r;
	errf_t *err;
	struct sshbuf *msg;
	struct sshkey *key = NULL;
	struct sshkey *partner = NULL;
	struct piv_slot *slot = NULL;
	uint8_t *secret;
	size_t seclen;
	uint flags;
	int found = 0;
	boolean_t canskip = B_TRUE;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((r = sshkey_froms(buf, &key)) ||
	    (r = sshkey_froms(buf, &partner))) {
		err = parserrf("sshkey_froms", r);
		goto out;
	}
	if ((r = sshbuf_get_u32(buf, &flags))) {
		err = parserrf("sshbuf_get_u32(flags)", r);
		goto out;
	}

	if (flags != 0) {
		err = flagserrf(flags);
		goto out;
	}

	if ((err = agent_piv_open()))
		goto out;

	while ((slot = piv_slot_next(selk, slot)) != NULL) {
		if (sshkey_equal(piv_slot_pubkey(slot), key) == 1) {
			found = 1;
			break;
		}
	}
	if (!found) {
		agent_piv_close(B_FALSE);
		err = errf("NotFoundError", NULL, "specified key not found");
		goto out;
	}
	bunyan_add_vars(msg_log_frame,
	    "slotid", BNY_UINT, (uint)piv_slot_id(slot), NULL);

	if (key->type != KEY_ECDSA || partner->type != KEY_ECDSA) {
		agent_piv_close(B_FALSE);
		err = errf("InvalidKeysError", NULL,
		    "keys are not both EC keys (%s and %s)",
		    sshkey_type(key), sshkey_type(partner));
		goto out;
	}

	if (piv_slot_id(slot) == PIV_SLOT_SIGNATURE)
		canskip = B_FALSE;

pin_again:
	if ((err = agent_piv_try_pin(canskip))) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	err = piv_ecdh(selk, slot, partner, &secret, &seclen);
	if (errf_caused_by(err, "PermissionError") && pin_len != 0 &&
	    piv_token_is_ykpiv(selk) && canskip) {
		/* YubiKey can have slots other than 9C as "PIN Always" */
		canskip = B_FALSE;
		goto pin_again;
	} else if (errf_caused_by(err, "PermissionError")) {
		agent_piv_close(B_TRUE);
		err = nopinerrf(err);
		goto out;
	} else if (err) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	agent_piv_close(B_FALSE);

	if ((r = sshbuf_put_u8(msg, SSH_AGENT_SUCCESS)) != 0 ||
	    (r = sshbuf_put_string(msg, secret, seclen)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	explicit_bzero(secret, seclen);
	free(secret);

	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

out:
	sshbuf_free(msg);
	sshkey_free(key);
	sshkey_free(partner);
	return (err);
}

static errf_t *
process_ext_rebox(SocketEntry *e, struct sshbuf *buf)
{
	int r;
	errf_t *err;
	struct sshbuf *msg, *boxbuf = NULL, *guidb = NULL;
	struct sshkey *partner = NULL;
	struct piv_ecdh_box *box = NULL, *newbox = NULL;
	uint8_t slotid;
	uint flags;
	struct piv_slot *slot;
	struct piv_token *tk;
	uint8_t *secret = NULL, *out = NULL;
	size_t seclen, outlen;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((r = sshbuf_froms(buf, &boxbuf)) != 0 ||
	    (r = sshbuf_froms(buf, &guidb)) != 0) {
		err = parserrf("sshbuf_froms", r);
		goto out;
	}
	if ((r = sshbuf_get_u8(buf, &slotid)) != 0) {
		err = parserrf("sshbuf_get_u8(slotid)", r);
		goto out;
	}
	if ((r = sshkey_froms(buf, &partner)) != 0) {
		err = parserrf("sshkey_froms(partner)", r);
		goto out;
	}
	if ((r = sshbuf_get_u32(buf, &flags)) != 0) {
		err = parserrf("sshbuf_get_u32(flags)", r);
		goto out;
	}

	if (flags != 0) {
		err = flagserrf(flags);
		goto out;
	}

	err = sshbuf_get_piv_box(boxbuf, &box);
	if (err)
		goto out;

	err = piv_box_find_token(selk, box, &tk, &slot);
	if (err)
		goto out;
	if (tk != selk) {
		err = errf("WrongTokenError", NULL, "box can only be unlocked "
		    "by a different PIV device");
		goto out;
	}

	if ((err = agent_piv_open()))
		goto out;
	if ((err = agent_piv_try_pin(B_FALSE))) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	if ((err = piv_box_open(selk, slot, box))) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	VERIFY0(piv_box_take_data(box, &secret, &seclen));
	agent_piv_close(B_FALSE);

	newbox = piv_box_new();
	VERIFY(newbox != NULL);

	if (sshbuf_len(guidb) > 0) {
		piv_box_set_guid(newbox, sshbuf_ptr(guidb), GUID_LEN);
		piv_box_set_slot(newbox, slotid);
	}
	VERIFY0(piv_box_set_data(newbox, secret, seclen));
	if ((err = piv_box_seal_offline(partner, newbox)))
		goto out;

	VERIFY0(piv_box_to_binary(newbox, &out, &outlen));

	if ((r = sshbuf_put_u8(msg, SSH_AGENT_SUCCESS)) != 0 ||
	    (r = sshbuf_put_string(msg, out, outlen)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

out:
	piv_box_free(box);
	piv_box_free(newbox);
	if (secret != NULL) {
		explicit_bzero(secret, seclen);
		free(secret);
	}
	if (out != NULL) {
		explicit_bzero(out, outlen);
		free(out);
	}
	sshbuf_free(msg);
	sshkey_free(partner);
	sshbuf_free(boxbuf);
	sshbuf_free(guidb);
	return (err);
}

static errf_t *
process_ext_x509_certs(SocketEntry *e, struct sshbuf *buf)
{
	/*int r;
	struct sshbuf *msg;*/
	return (errf("NotImplementedError", NULL,
	    "x509 certs ext not implemented yet"));
}

static errf_t *
process_ext_attest(SocketEntry *e, struct sshbuf *buf)
{
	int r;
	errf_t *err;
	struct sshbuf *msg;
	struct sshkey *key = NULL;
	struct piv_slot *slot = NULL;
	uint8_t *cert = NULL, *chain = NULL, *ptr;
	size_t certlen, chainlen = 0, len;
	uint flags;
	int found = 0;
	uint tag;
	struct tlv_state *tlv = NULL;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((r = sshkey_froms(buf, &key)) != 0 ||
	    (r = sshbuf_get_u32(buf, &flags)) != 0) {
		err = parserrf("sshkey_froms", r);
		goto out;
	}

	if (flags != 0) {
		err = flagserrf(flags);
		goto out;
	}

	if ((err = agent_piv_open()))
		goto out;

	while ((slot = piv_slot_next(selk, slot)) != NULL) {
		if (sshkey_equal(piv_slot_pubkey(slot), key)) {
			found = 1;
			break;
		}
	}
	if (!found) {
		agent_piv_close(B_FALSE);
		err = errf("NotFoundError", NULL, "specified key not found");
		goto out;
	}
	bunyan_add_vars(msg_log_frame,
	    "slotid", BNY_UINT, (uint)piv_slot_id(slot), NULL);

	err = ykpiv_attest(selk, slot, &cert, &certlen);
	if (err) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	err = piv_read_file(selk, PIV_TAG_CERT_YK_ATTESTATION, &chain, &chainlen);
	if (err) {
		agent_piv_close(B_TRUE);
		goto out;
	}
	agent_piv_close(B_FALSE);

	tlv = tlv_init(chain, 0, chainlen);
	if ((err = tlv_read_tag(tlv, &tag)))
		goto out;
	if (tag != 0x70) {
		err = errf("InvalidDataError", NULL, "PIV device returned "
		    "wrong tag at start of attestation cert");
		goto out;
	}
	ptr = tlv_ptr(tlv);
	len = tlv_rem(tlv);
	tlv_skip(tlv);

	if ((r = sshbuf_put_u8(msg, SSH_AGENT_SUCCESS)) != 0 ||
	    (r = sshbuf_put_u32(msg, 2)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

	if ((r = sshbuf_put_string(msg, cert, certlen)) != 0 ||
	    (r = sshbuf_put_string(msg, ptr, len)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));

out:
	if (tlv != NULL)
		tlv_free(tlv);
	free(cert);
	piv_file_data_free(chain, chainlen);
	sshbuf_free(msg);
	sshkey_free(key);
	return (err);
}

static errf_t *
process_ext_query(SocketEntry *e, struct sshbuf *buf)
{
	int r, n = 0;
	struct exthandler *h;
	struct sshbuf *msg;

	if ((msg = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);

	for (h = exthandlers; h->eh_name != NULL; ++h)
		++n;

	if ((r = sshbuf_put_u8(msg, SSH_AGENT_SUCCESS)) != 0 ||
	    (r = sshbuf_put_u32(msg, n)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	for (h = exthandlers; h->eh_name != NULL; ++h) {
		if ((r = sshbuf_put_cstring(msg, h->eh_name)) != 0)
			fatal("%s: buffer error: %s", __func__, ssh_err(r));
	}

	if ((r = sshbuf_put_stringb(e->output, msg)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	sshbuf_free(msg);

	return (NULL);
}

struct exthandler exthandlers[] = {
	{ "query", process_ext_query },
	{ "ecdh@joyent.com", process_ext_ecdh },
	{ "ecdh-rebox@joyent.com", process_ext_rebox },
	{ "x509-certs@joyent.com", process_ext_x509_certs },
	{ "ykpiv-attest@joyent.com", process_ext_attest },
	{ NULL, NULL }
};

static errf_t *
process_extension(SocketEntry *e)
{
	errf_t *err;
	int r;
	char *extname = NULL;
	size_t enlen;
	struct sshbuf *inner = NULL;
	struct exthandler *h, *hdlr = NULL;

	if ((r = sshbuf_get_cstring(e->request, &extname, &enlen)))
		return (parserrf("sshbuf_get_cstring", r));

	if ((r = sshbuf_froms(e->request, &inner))) {
		err = parserrf("sshbuf_froms", r);
		goto out;
	}
	VERIFY(extname != NULL);
	VERIFY(inner != NULL);

	for (h = exthandlers; h->eh_name != NULL; ++h) {
		if (strcmp(h->eh_name, extname) == 0) {
			hdlr = h;
			break;
		}
	}
	if (hdlr == NULL) {
		err = errf("UnknownExtension", NULL,
		    "unsupported extension '%s'", extname);
		goto out;
	}

	bunyan_add_vars(msg_log_frame,
	    "extension", BNY_STRING, h->eh_name, NULL);
	err = hdlr->eh_handler(e, inner);

	if (err) {
		send_extfail(e);
		bunyan_log(BNY_WARN, "failed to process extension command",
		    "error", BNY_ERF, err, NULL);
		if (errf_caused_by(err, "NoPINError") &&
		    bunyan_get_level() > BNY_WARN) {
			warnfx(err, "denied command due to lack of PIN");
		}
		errf_free(err);
		err = ERRF_OK;
	}

out:
	sshbuf_free(inner);
	free(extname);
	return (err);
}

static errf_t *
process_lock_agent(SocketEntry *e, int lock)
{
	int r;
	char *passwd;
	size_t pwlen;
	uint retries = 1;
	errf_t *err = NULL;

	/*
	 * This is deliberately fatal: the user has requested that we lock,
	 * but we can't parse their request properly. The only safe thing to
	 * do is abort.
	 */
	if ((r = sshbuf_get_cstring(e->request, &passwd, &pwlen)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	VERIFY(passwd != NULL);

	if (lock) {
		drop_pin();
		send_status(e, 1);
	} else {
		if ((err = valid_pin(passwd)))
			goto out;

		if ((err = agent_piv_open()))
			goto out;

		err = piv_verify_pin(selk, piv_token_default_auth(selk),
		    passwd, &retries, B_FALSE);

		if (err == ERRF_OK) {
			agent_piv_close(B_FALSE);
			if (pin_len != 0)
				explicit_bzero(pin, pin_len);
			pin_len = pwlen;
			bcopy(passwd, pin, pwlen + 1);
			send_status(e, 1);
			bunyan_log(BNY_INFO, "storing PIN in memory", NULL);
			card_probe_interval = card_probe_interval_pin;
			goto out;
		}
		agent_piv_close(B_TRUE);

		err = wrap_pin_error(err, retries);
	}
out:
	explicit_bzero(passwd, pwlen);
	free(passwd);
	return (err);
}

static const char *
msg_type_to_name(int msg)
{
	switch (msg) {
	case SSH_AGENTC_LOCK:
		return ("LOCK");
	case SSH_AGENTC_UNLOCK:
		return ("UNLOCK");
	case SSH2_AGENTC_SIGN_REQUEST:
		return ("SIGN_REQUEST");
	case SSH2_AGENTC_ADD_IDENTITY:
		return ("ADD_IDENTITY");
	case SSH2_AGENTC_REMOVE_IDENTITY:
		return ("REMOVE_IDENTITY");
	case SSH2_AGENTC_REQUEST_IDENTITIES:
		return ("REQUEST_IDENTITIES");
	case SSH2_AGENTC_REMOVE_ALL_IDENTITIES:
		return ("REMOVE_ALL_IDENTITIES");
	case SSH_AGENTC_ADD_SMARTCARD_KEY:
		return ("ADD_SMARTCARD_KEY");
	case SSH_AGENTC_REMOVE_SMARTCARD_KEY:
		return ("REMOVE_SMARTCARD_KEY");
	case SSH2_AGENTC_EXTENSION:
		return ("EXTENSION");
	default:
		return ("UNKNOWN");
	}
}

/* dispatch incoming messages */
static int
process_message(u_int socknum)
{
	u_int msg_len;
	u_char type;
	const u_char *cp;
	int r;
	errf_t *err;
	SocketEntry *e;

	if (socknum >= sockets_alloc) {
		fatal("%s: socket number %u >= allocated %u",
		    __func__, socknum, sockets_alloc);
	}
	e = &sockets[socknum];

	if (sshbuf_len(e->input) < 5)
		return 0;		/* Incomplete message header. */
	cp = sshbuf_ptr(e->input);
	msg_len = PEEK_U32(cp);
	if (msg_len > AGENT_MAX_LEN) {
		sdebug("%s: socket %u (fd=%d) message too long %u > %u",
		    __func__, socknum, e->fd, msg_len, AGENT_MAX_LEN);
		return -1;
	}
	if (sshbuf_len(e->input) < msg_len + 4)
		return 0;		/* Incomplete message body. */

	/* move the current input to e->request */
	sshbuf_reset(e->request);
	if ((r = sshbuf_get_stringb(e->input, e->request)) != 0 ||
	    (r = sshbuf_get_u8(e->request, &type)) != 0) {
		if (r == SSH_ERR_MESSAGE_INCOMPLETE ||
		    r == SSH_ERR_STRING_TOO_LARGE) {
			sdebug("%s: buffer error: %s", __func__, ssh_err(r));
			return -1;
		}
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	}

	msg_log_frame = bunyan_push(
	    "fd", BNY_INT, e->fd,
	    "msg_type", BNY_INT, (int)type,
	    "msg_type_name", BNY_STRING, msg_type_to_name(type),
	    "remote_pid", BNY_INT, (int)e->pid,
	    "remote_cmd", BNY_STRING, (e->exepath == NULL) ? "???" : e->exepath,
	    NULL);
	bunyan_log(BNY_DEBUG, "received ssh-agent message", NULL);

	last_op = monotime();

	switch (type) {
	case SSH_AGENTC_LOCK:
	case SSH_AGENTC_UNLOCK:
		err = process_lock_agent(e, type == SSH_AGENTC_LOCK);
		break;
	/* ssh2 */
	case SSH2_AGENTC_SIGN_REQUEST:
		err = process_sign_request2(e);
		break;
	case SSH2_AGENTC_REQUEST_IDENTITIES:
		err = process_request_identities(e);
		break;
	case SSH2_AGENTC_REMOVE_ALL_IDENTITIES:
		err = process_remove_all_identities(e);
		break;
	case SSH2_AGENTC_EXTENSION:
		err = process_extension(e);
		break;
	default:
		/* Unknown message.  Respond with failure. */
		err = errf("UnknownMessageError", NULL,
		    "unknown/unsupported agent protocol message %d", type);
		break;
	}

	if (err) {
		bunyan_log(BNY_WARN, "failed to process command",
		    "error", BNY_ERF, err, NULL);
		if (errf_caused_by(err, "NoPINError") &&
		    bunyan_get_level() > BNY_WARN) {
			warnfx(err, "denied command due to lack of PIN");
		}
		sshbuf_reset(e->request);
		send_status(e, 0);
		errf_free(err);
	} else {
		bunyan_log(BNY_INFO, "processed ssh-agent message", NULL);
	}

	bunyan_pop(msg_log_frame);
	return 0;
}

extern void *reallocarray(void *ptr, size_t nmemb, size_t size);

static SocketEntry *
new_socket(sock_type type, int fd)
{
	u_int i, old_alloc, new_alloc;

	set_nonblock(fd);

	if (fd > max_fd)
		max_fd = fd;

	for (i = 0; i < sockets_alloc; i++)
		if (sockets[i].type == AUTH_UNUSED) {
			sockets[i].fd = fd;
			if ((sockets[i].input = sshbuf_new()) == NULL)
				fatal("%s: sshbuf_new failed", __func__);
			if ((sockets[i].output = sshbuf_new()) == NULL)
				fatal("%s: sshbuf_new failed", __func__);
			if ((sockets[i].request = sshbuf_new()) == NULL)
				fatal("%s: sshbuf_new failed", __func__);
			sockets[i].type = type;
			return (&sockets[i]);
		}
	old_alloc = sockets_alloc;
	new_alloc = sockets_alloc + 10;
	sockets = reallocarray(sockets, new_alloc, sizeof(SocketEntry));
	VERIFY(sockets != NULL);
	for (i = old_alloc; i < new_alloc; i++)
		sockets[i].type = AUTH_UNUSED;
	sockets_alloc = new_alloc;
	sockets[old_alloc].fd = fd;
	if ((sockets[old_alloc].input = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((sockets[old_alloc].output = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	if ((sockets[old_alloc].request = sshbuf_new()) == NULL)
		fatal("%s: sshbuf_new failed", __func__);
	sockets[old_alloc].type = type;
	return (&sockets[old_alloc]);
}

static int
handle_socket_read(u_int socknum)
{
	struct sockaddr_un sunaddr;
	socklen_t slen;
	uid_t euid;
	gid_t egid;
	int fd;
	pid_t pid = 0;
	char *exepath = NULL;
	SocketEntry *ent;
#if defined(__sun)
	ucred_t *peer;
	struct psinfo *psinfo;
	zoneid_t zid;
	char fn[128];
	FILE *f;
#endif
#if defined(__OpenBSD__)
	struct sockpeercred *peer;
	socklen_t len;
#elif defined(SO_PEERCRED)
	struct ucred *peer;
	socklen_t len;
	char fn[128], ln[128];
#endif
	slen = sizeof(sunaddr);
	fd = accept(sockets[socknum].fd, (struct sockaddr *)&sunaddr, &slen);
	if (fd < 0) {
		error("accept from AUTH_SOCKET: %s", strerror(errno));
		return -1;
	}
#if defined(__sun)
	if (getpeerucred(fd, &peer) != 0) {
		error("getpeerucred %d failed: %s", fd, strerror(errno));
		close(fd);
		return -1;
	}
	euid = ucred_geteuid(peer);
	egid = ucred_getegid(peer);
	pid = ucred_getpid(peer);
	zid = ucred_getzoneid(peer);
	ucred_free(peer);
	psinfo = calloc(1, sizeof (struct psinfo));
	snprintf(fn, sizeof (fn), "/proc/%d/psinfo", (int)pid);
	f = fopen(fn, "r");
	if (f != NULL) {
		if (fread(psinfo, sizeof (struct psinfo), 1, f) == 1) {
			exepath = strdup(psinfo->pr_fname);
		}
		fclose(f);
	}
	free(psinfo);
	if (check_client_zoneid && zid != getzoneid()) {
		error("zoneid mismatch: peer zoneid %u != zoneid %u",
		    (u_int) zid, (u_int) getzoneid());
		close(fd);
		return -1;
	}
#elif defined(__OpenBSD__)
	peer = calloc(1, sizeof (struct sockpeercred));
	len = sizeof (struct sockpeercred);
	if (getsockopt(fd, SOL_SOCKET, SO_PEERCRED, peer, &len)) {
		error("getsockopts(SO_PEERCRED) %d failed: %s", fd, strerror(errno));
		close(fd);
		return -1;
	}
	euid = peer->uid;
	egid = peer->gid;
	pid = peer->pid;
	free(peer);
#elif defined(SO_PEERCRED)
	peer = calloc(1, sizeof (struct ucred));
	len = sizeof (struct ucred);
	if (getsockopt(fd, SOL_SOCKET, SO_PEERCRED, peer, &len)) {
		error("getsockopts(SO_PEERCRED) %d failed: %s", fd, strerror(errno));
		close(fd);
		return -1;
	}
	euid = peer->uid;
	egid = peer->gid;
	pid = peer->pid;
	free(peer);
	snprintf(fn, sizeof (fn), "/proc/%d/exe", (int)pid);
	len = readlink(fn, ln, sizeof (ln));
	if (len > 0 && len < sizeof (ln)) {
		exepath = strndup(ln, len);
	}
#else
	if (getpeereid(fd, &euid, &egid) < 0) {
		error("getpeereid %d failed: %s", fd, strerror(errno));
		close(fd);
		return -1;
	}
#endif
	if (check_client_uid && (euid != 0) && (getuid() != euid)) {
		error("uid mismatch: peer euid %u != uid %u",
		    (u_int) euid, (u_int) getuid());
		close(fd);
		return -1;
	}
	ent = new_socket(AUTH_CONNECTION, fd);
	ent->pid = pid;
	ent->gid = egid;
	ent->exepath = exepath;
	return 0;
}

static int
handle_conn_read(u_int socknum)
{
	char buf[1024];
	ssize_t len;
	int r;

	if ((len = read(sockets[socknum].fd, buf, sizeof(buf))) <= 0) {
		if (len == -1) {
			if (errno == EAGAIN || errno == EINTR)
				return 0;
			error("%s: read error on socket %u (fd %d): %s",
			    __func__, socknum, sockets[socknum].fd,
			    strerror(errno));
		}
		return -1;
	}
	if ((r = sshbuf_put(sockets[socknum].input, buf, len)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	explicit_bzero(buf, sizeof(buf));
	process_message(socknum);
	return 0;
}

static int
handle_conn_write(u_int socknum)
{
	ssize_t len;
	int r;

	if (sshbuf_len(sockets[socknum].output) == 0)
		return 0; /* shouldn't happen */
	if ((len = write(sockets[socknum].fd,
	    sshbuf_ptr(sockets[socknum].output),
	    sshbuf_len(sockets[socknum].output))) <= 0) {
		if (len == -1) {
			if (errno == EAGAIN || errno == EINTR)
				return 0;
			error("%s: read error on socket %u (fd %d): %s",
			    __func__, socknum, sockets[socknum].fd,
			    strerror(errno));
		}
		return -1;
	}
	if ((r = sshbuf_consume(sockets[socknum].output, len)) != 0)
		fatal("%s: buffer error: %s", __func__, ssh_err(r));
	return 0;
}

static void
after_poll(struct pollfd *pfd, size_t npfd)
{
	size_t i;
	u_int socknum;

	for (i = 0; i < npfd; i++) {
		if (pfd[i].revents == 0)
			continue;
		/* Find sockets entry */
		for (socknum = 0; socknum < sockets_alloc; socknum++) {
			if (sockets[socknum].type != AUTH_SOCKET &&
			    sockets[socknum].type != AUTH_CONNECTION)
				continue;
			if (pfd[i].fd == sockets[socknum].fd)
				break;
		}
		if (socknum >= sockets_alloc) {
			error("%s: no socket for fd %d", __func__, pfd[i].fd);
			continue;
		}
		/* Process events */
		switch (sockets[socknum].type) {
		case AUTH_SOCKET:
			if ((pfd[i].revents & (POLLIN|POLLERR)) != 0 &&
			    handle_socket_read(socknum) != 0)
				close_socket(&sockets[socknum]);
			break;
		case AUTH_CONNECTION:
			if ((pfd[i].revents & (POLLIN|POLLERR)) != 0 &&
			    handle_conn_read(socknum) != 0) {
				close_socket(&sockets[socknum]);
				break;
			}
			if ((pfd[i].revents & (POLLOUT|POLLHUP)) != 0 &&
			    handle_conn_write(socknum) != 0)
				close_socket(&sockets[socknum]);
			break;
		default:
			break;
		}
	}
}

static int
prepare_poll(struct pollfd **pfdp, size_t *npfdp, int *timeoutp)
{
	struct pollfd *pfd = *pfdp;
	size_t i, j, npfd = 0;
	uint64_t now, deadline;

	/* Count active sockets */
	for (i = 0; i < sockets_alloc; i++) {
		switch (sockets[i].type) {
		case AUTH_SOCKET:
		case AUTH_CONNECTION:
			npfd++;
			break;
		case AUTH_UNUSED:
			break;
		default:
			fatal("Unknown socket type %d", sockets[i].type);
			break;
		}
	}
	if (npfd != *npfdp &&
	    (pfd = recallocarray(pfd, *npfdp, npfd, sizeof(struct pollfd))) == NULL)
		fatal("%s: recallocarray failed", __func__);
	*pfdp = pfd;
	*npfdp = npfd;

	for (i = j = 0; i < sockets_alloc; i++) {
		switch (sockets[i].type) {
		case AUTH_SOCKET:
		case AUTH_CONNECTION:
			pfd[j].fd = sockets[i].fd;
			pfd[j].revents = 0;
			/* XXX backoff when input buffer full */
			pfd[j].events = POLLIN;
			if (sshbuf_len(sockets[i].output) > 0)
				pfd[j].events |= POLLOUT;
			j++;
			break;
		default:
			break;
		}
	}
	now = monotime();
	deadline = txnopen ? (txntimeout - now) : 0;
	if (parent_alive_interval != 0)
		deadline = (deadline == 0) ? parent_alive_interval * 1000 :
		    MINIMUM(deadline, parent_alive_interval * 1000);
	if (card_probe_interval != 0)
		deadline = (deadline == 0) ? card_probe_interval * 1000 :
		    MINIMUM(deadline, card_probe_interval * 1000);
	if (deadline == 0) {
		*timeoutp = -1; /* INFTIM */
	} else {
		if (deadline > INT_MAX)
			*timeoutp = INT_MAX;
		else
			*timeoutp = deadline;
	}
	return (1);
}

static void
cleanup_socket(void)
{
	if (cleanup_pid != 0 && getpid() != cleanup_pid)
		return;
	sdebug("%s: cleanup", __func__);
	if (socket_name[0])
		unlink(socket_name);
	if (socket_dir[0])
		rmdir(socket_dir);
}

void
cleanup_exit(int i)
{
	cleanup_socket();
	_exit(i);
}

/*ARGSUSED*/
static void
cleanup_handler(int sig)
{
	cleanup_socket();
	if (selk != NULL && piv_token_in_txn(selk))
		piv_txn_end(selk);
	piv_release(ks);
	SCardReleaseContext(ctx);
	_exit(2);
}

static void
check_parent_exists(void)
{
	/*
	 * If our parent has exited then getppid() will return (pid_t)1,
	 * so testing for that should be safe.
	 */
	if (parent_pid != -1 && getppid() != parent_pid) {
		bunyan_log(BNY_INFO,
		    "Parent has died - Authentication agent exiting.", NULL);
		cleanup_socket();
		_exit(2);
	}
}

static void
usage(void)
{
	fprintf(stderr,
	    "usage: pivy-agent [-c | -s] [-Ddim] [-a bind_address] [-E fingerprint_hash]\n"
	    "                  [-K cak] -g guid [command [arg ...]]\n"
	    "       pivy-agent [-c | -s] -k\n"
	    "\n"
	    "An ssh-agent work-alike which always contains the keys stored on\n"
	    "a PIV token and supports other PIV-related extensions.\n"
	    "\n"
	    "Options:\n"
	    "  -a bind_address       Bind to a specific UNIX domain socket\n"
	    "  -c                    Generate csh style commands on stdout\n"
	    "  -s                    Generate Bourne shell style commands\n"
	    "  -D                    Foreground mode; do not fork\n"
	    "  -d                    Debug mode\n"
	    "  -i                    Foreground + command logging\n"
	    "  -m                    Allow signing with 9D (KEY_MGMT) key\n"
	    "  -E fp_hash            Set hash algo for fingerprints\n"
	    "  -g guid               GUID or GUID prefix of PIV token to use\n"
	    "  -K cak                9E (card auth) key to authenticate PIV token\n"
	    "  -k                    Kill an already-running agent\n"
	    "  -U                    Don't check client UID (allow any uid to connect)\n"
#if defined(__sun)
	    "  -Z                    Don't check client zoneid (allow any zone to connect)\n"
#endif
	    );
	exit(1);
}

static uint8_t *
parse_hex(const char *str, uint *outlen)
{
	const uint len = strlen(str);
	uint8_t *data = calloc(1, len / 2 + 1);
	uint idx = 0;
	uint shift = 4;
	uint i;
	for (i = 0; i < len; ++i) {
		const char c = str[i];
		int skip = 0;
		if (c >= '0' && c <= '9') {
			data[idx] |= (c - '0') << shift;
		} else if (c >= 'a' && c <= 'f') {
			data[idx] |= (c - 'a' + 0xa) << shift;
		} else if (c >= 'A' && c <= 'F') {
			data[idx] |= (c - 'A' + 0xA) << shift;
		} else if (c == ':' || c == ' ' || c == '\t' ||
		    c == '\n' || c == '\r') {
			skip = 1;
		} else {
			fprintf(stderr, "error: invalid hex digit: '%c'\n", c);
			exit(1);
		}
		if (skip == 0) {
			if (shift == 4) {
				shift = 0;
			} else if (shift == 0) {
				++idx;
				shift = 4;
			}
		}
	}
	if (shift == 0) {
		fprintf(stderr, "error: odd number of hex digits "
		    "(incomplete)\n");
		exit(1);
	}
	*outlen = idx;
	return (data);
}

static int
unix_listener(const char *path, int backlog, int unlink_first)
{
	struct sockaddr_un sunaddr;
	int saved_errno, sock;

	memset(&sunaddr, 0, sizeof(sunaddr));
	sunaddr.sun_family = AF_UNIX;
	if (strlcpy(sunaddr.sun_path, path,
	    sizeof(sunaddr.sun_path)) >= sizeof(sunaddr.sun_path)) {
		error("%s: path \"%s\" too long for Unix domain socket",
		    __func__, path);
		errno = ENAMETOOLONG;
		return -1;
	}

	sock = socket(PF_UNIX, SOCK_STREAM, 0);
	if (sock < 0) {
		saved_errno = errno;
		error("%s: socket: %.100s", __func__, strerror(errno));
		errno = saved_errno;
		return -1;
	}
	if (unlink_first == 1) {
		if (unlink(path) != 0 && errno != ENOENT)
			error("unlink(%s): %.100s", path, strerror(errno));
	}
	if (bind(sock, (struct sockaddr *)&sunaddr, sizeof(sunaddr)) < 0) {
		saved_errno = errno;
		error("%s: cannot bind to path %s: %s",
		    __func__, path, strerror(errno));
		close(sock);
		errno = saved_errno;
		return -1;
	}
	if (listen(sock, backlog) < 0) {
		saved_errno = errno;
		error("%s: cannot listen on path %s: %s",
		    __func__, path, strerror(errno));
		close(sock);
		unlink(path);
		errno = saved_errno;
		return -1;
	}
	return sock;
}

/* Make a template filename for mk[sd]temp() */
static void
mktemp_proto(char *s, size_t len)
{
	const char *tmpdir;
	int r;

	if ((tmpdir = getenv("TMPDIR")) != NULL) {
		r = snprintf(s, len, "%s/ssh-XXXXXXXXXXXX", tmpdir);
		if (r > 0 && (size_t)r < len)
			return;
	}
	r = snprintf(s, len, "/tmp/ssh-XXXXXXXXXXXX");
	if (r < 0 || (size_t)r >= len)
		fatal("%s: template string too short", __func__);
}

#if defined(__APPLE__)
#define INVALID 	1
#define TOOSMALL 	2
#define TOOLARGE 	3

static long long
strtonum(const char *numstr, long long minval, long long maxval,
    const char **errstrp)
{
	long long ll = 0;
	char *ep;
	int error = 0;
	struct errval {
		const char *errstr;
		int err;
	} ev[4] = {
		{ NULL,		0 },
		{ "invalid",	EINVAL },
		{ "too small",	ERANGE },
		{ "too large",	ERANGE },
	};

	ev[0].err = errno;
	errno = 0;
	if (minval > maxval)
		error = INVALID;
	else {
		ll = strtoll(numstr, &ep, 10);
		if (numstr == ep || *ep != '\0')
			error = INVALID;
		else if ((ll == LLONG_MIN && errno == ERANGE) || ll < minval)
			error = TOOSMALL;
		else if ((ll == LLONG_MAX && errno == ERANGE) || ll > maxval)
			error = TOOLARGE;
	}
	if (errstrp != NULL)
		*errstrp = ev[error].errstr;
	errno = ev[error].err;
	if (error)
		ll = 0;

	return (ll);
}
#endif

int
main(int ac, char **av)
{
	int c_flag = 0, d_flag = 0, D_flag = 0, k_flag = 0, s_flag = 0;
	int i_flag = 0;
	int sock, ch, result, saved_errno;
	char *shell, *format, *pidstr, *agentsocket = NULL;
	extern int optind;
	extern char *optarg;
	pid_t pid;
	char pidstrbuf[1 + 3 * sizeof pid];
	uint len = 0;
	mode_t prev_mask;
	int timeout = -1; /* INFTIM */
	struct pollfd *pfd = NULL;
	size_t npfd = 0;
	uint64_t now;
	char *ptr;
	int r;
	errf_t *err;

#if !defined(__APPLE__)
	int fd;
#endif

	/* Ensure that fds 0, 1 and 2 are open or directed to /dev/null */
	sanitise_stdfd();

	/* drop */
	VERIFY0(setegid(getgid()));
	VERIFY0(setgid(getgid()));

	OpenSSL_add_all_algorithms();

	bunyan_init();
	bunyan_set_name("pivy-agent");

	__progname = "pivy-agent";

	while ((ch = getopt(ac, av, "cDdkisE:a:P:g:K:mZU")) != -1) {
		switch (ch) {
		case 'g':
			guid = parse_hex(optarg, &len);
			guid_len = len;
			if (len > 16) {
				fprintf(stderr, "error: GUID must be <=16 bytes"
				    " in length (you gave %u)\n", len);
				exit(3);
			}
			break;
		case 'U':
			check_client_uid = B_FALSE;
			break;
#if defined(__sun)
		case 'Z':
			check_client_zoneid = B_FALSE;
			break;
#endif
		case 'K':
			cak = sshkey_new(KEY_UNSPEC);
			VERIFY(cak != NULL);
			ptr = optarg;
			r = sshkey_read(cak, &ptr);
			if (r != 0)
				fatal("Invalid CAK key given: %ld", r);
			break;
		case 'E':
			fingerprint_hash = ssh_digest_alg_by_name(optarg);
			if (fingerprint_hash == -1)
				fatal("Invalid hash algorithm \"%s\"", optarg);
			break;
		case 'c':
			if (s_flag)
				usage();
			c_flag++;
			break;
		case 'k':
			k_flag++;
			break;
		case 'P':
			fatal("pkcs11 options not supported");
			break;
		case 'm':
			sign_9d = B_TRUE;
			break;
		case 's':
			if (c_flag)
				usage();
			s_flag++;
			break;
		case 'd':
			d_flag++;
			break;
		case 'D':
			if (d_flag || D_flag)
				usage();
			D_flag++;
			break;
		case 'i':
			i_flag++;
			break;
		case 'a':
			agentsocket = optarg;
			break;
		default:
			usage();
		}
	}
	ac -= optind;
	av += optind;

	if (ac > 0 && (c_flag || k_flag || s_flag || d_flag || D_flag))
		usage();

	if (ac == 0 && !c_flag && !s_flag) {
		shell = getenv("SHELL");
		if (shell != NULL && (len = strlen(shell)) > 2 &&
		    strncmp(shell + len - 3, "csh", 3) == 0)
			c_flag = 1;
	}
	if (guid == NULL)
		usage();
	if (k_flag) {
		const char *errstr = NULL;

		pidstr = getenv(SSH_AGENTPID_ENV_NAME);
		if (pidstr == NULL) {
			fprintf(stderr, "%s not set, cannot kill agent\n",
			    SSH_AGENTPID_ENV_NAME);
			exit(1);
		}
		pid = (int)strtonum(pidstr, 2, INT_MAX, &errstr);
		if (errstr) {
			fprintf(stderr,
			    "%s=\"%s\", which is not a good PID: %s\n",
			    SSH_AGENTPID_ENV_NAME, pidstr, errstr);
			exit(1);
		}
		if (kill(pid, SIGTERM) == -1) {
			perror("kill");
			exit(1);
		}
		format = c_flag ? "unsetenv %s;\n" : "unset %s;\n";
		printf(format, SSH_AUTHSOCKET_ENV_NAME);
		printf(format, SSH_AGENTPID_ENV_NAME);
		printf("echo Agent pid %ld killed;\n", (long)pid);
		exit(0);
	}
	parent_pid = getpid();

	if (agentsocket == NULL) {
		/* Create private directory for agent socket */
		mktemp_proto(socket_dir, sizeof(socket_dir));
		if (mkdtemp(socket_dir) == NULL) {
			perror("mkdtemp: private socket dir");
			exit(1);
		}
		snprintf(socket_name, sizeof socket_name, "%s/agent.%ld", socket_dir,
		    (long)parent_pid);
	} else {
		/* Try to use specified agent socket */
		socket_dir[0] = '\0';
		strlcpy(socket_name, agentsocket, sizeof socket_name);
	}

	prev_mask = umask(0177);
	sock = unix_listener(socket_name, SSH_LISTEN_BACKLOG, 0);
	if (sock < 0) {
		/* XXX - unix_listener() calls error() not perror() */
		*socket_name = '\0'; /* Don't unlink any existing file */
		cleanup_exit(1);
	}
	umask(prev_mask);

	if (d_flag) {
		ssh_dbglevel = BNY_TRACE;
		bunyan_set_level(BNY_TRACE);
	} else if (D_flag) {
		ssh_dbglevel = BNY_DEBUG;
		bunyan_set_level(BNY_DEBUG);
	} else if (i_flag) {
		ssh_dbglevel = BNY_INFO;
		bunyan_set_level(BNY_INFO);
	}

	if (d_flag >= 2) {
		piv_full_apdu_debug = B_TRUE;
	}

	/*
	 * Fork, and have the parent execute the command, if any, or present
	 * the socket data.  The child continues as the authentication agent.
	 */
	if (D_flag || d_flag || i_flag) {
		format = c_flag ? "setenv %s %s;\n" : "%s=%s; export %s;\n";
		printf(format, SSH_AUTHSOCKET_ENV_NAME, socket_name,
		    SSH_AUTHSOCKET_ENV_NAME);
		printf("echo Agent pid %ld;\n", (long)parent_pid);
		fflush(stdout);
		goto skip;
	}
#if defined(__APPLE__)
	ssh_dbglevel = BNY_INFO;
	bunyan_set_level(BNY_INFO);
	if (ac != 0) {
		bunyan_log(BNY_FATAL, "OSX does not support fork() inside "
		    "applications which use smartcards, and you have "
		    "specified a command to run. It is not possible to "
		    "execute it and remain in the foreground", NULL);
		exit(1);
	}
	bunyan_log(BNY_WARN, "OSX does not support fork() inside applications "
	    "which use smartcards; this agent will operate in the foreground",
	    NULL);
	format = c_flag ? "setenv %s %s;\n" : "%s=%s; export %s;\n";
	printf(format, SSH_AUTHSOCKET_ENV_NAME, socket_name,
	    SSH_AUTHSOCKET_ENV_NAME);
	printf(format, SSH_AGENTPID_ENV_NAME, pidstrbuf,
	    SSH_AGENTPID_ENV_NAME);
	printf("echo Agent pid %ld;\n", (long)parent_pid);
	fflush(stdout);

#else
	pid = fork();
	if (pid == -1) {
		perror("fork");
		cleanup_exit(1);
	}
	if (pid != 0) {		/* Parent - execute the given command. */
		close(sock);
		snprintf(pidstrbuf, sizeof pidstrbuf, "%ld", (long)pid);
		if (ac == 0) {
			format = c_flag ? "setenv %s %s;\n" : "%s=%s; export %s;\n";
			printf(format, SSH_AUTHSOCKET_ENV_NAME, socket_name,
			    SSH_AUTHSOCKET_ENV_NAME);
			printf(format, SSH_AGENTPID_ENV_NAME, pidstrbuf,
			    SSH_AGENTPID_ENV_NAME);
			printf("echo Agent pid %ld;\n", (long)pid);
			exit(0);
		}
		if (setenv(SSH_AUTHSOCKET_ENV_NAME, socket_name, 1) == -1 ||
		    setenv(SSH_AGENTPID_ENV_NAME, pidstrbuf, 1) == -1) {
			perror("setenv");
			exit(1);
		}
		execvp(av[0], av);
		perror(av[0]);
		exit(1);
	}
	/* child */
	ssh_dbglevel = BNY_WARN;
	bunyan_set_level(BNY_WARN);

	if (setsid() == -1) {
		error("setsid: %s", strerror(errno));
		cleanup_exit(1);
	}

	VERIFY0(chdir("/"));
	if ((fd = open(_PATH_DEVNULL, O_RDWR, 0)) != -1) {
		/* XXX might close listen socket */
		(void)dup2(fd, STDIN_FILENO);
		(void)dup2(fd, STDOUT_FILENO);
		//(void)dup2(fd, STDERR_FILENO);
		if (fd > 2)
			close(fd);
	}
#endif

skip:

	r = mlockall(MCL_CURRENT | MCL_FUTURE);
	if (r != 0) {
		bunyan_log(BNY_WARN, "mlockall() failed, sensitive data (e.g. PIN) "
		    "may be swapped out to disk if system is low on memory",
		    "error", BNY_STRING, strerror(r), NULL);
	}

	long pgsz = sysconf(_SC_PAGESIZE);
	pinmem = mmap(NULL, 3*pgsz, PROT_READ | PROT_WRITE,
	    MAP_PRIVATE | MAP_ANON, -1, 0);
	VERIFY(pinmem != MAP_FAILED);
#if defined(MADV_DONTDUMP)
	r = madvise(pinmem, 3*pgsz, MADV_DONTDUMP);
	if (r != 0) {
		bunyan_log(BNY_WARN, "madvice(MADV_DONTDUMP) failed, sensitive "
		    "data (e.g. PIN) may be contined in core dumps",
		    "error", BNY_STRING, strerror(errno), NULL);
	}
#endif
	VERIFY0(mprotect(pinmem, pgsz, PROT_NONE));
	VERIFY0(mprotect(pinmem + 2*pgsz, pgsz, PROT_NONE));
	pin = pinmem + pgsz;
	explicit_bzero(pin, MAX_PIN_LEN);

	cleanup_pid = getpid();

	new_socket(AUTH_SOCKET, sock);
	if (ac > 0)
		parent_alive_interval = 10;
	signal(SIGPIPE, SIG_IGN);
#if defined(__APPLE__)
	signal(SIGINT, cleanup_handler);
#else
	signal(SIGINT, (d_flag | D_flag | i_flag) ? cleanup_handler : SIG_IGN);
#endif
	signal(SIGHUP, cleanup_handler);
	signal(SIGTERM, cleanup_handler);

	r = SCardEstablishContext(SCARD_SCOPE_SYSTEM, NULL, NULL, &ctx);
	if (r != SCARD_S_SUCCESS) {
		bunyan_log(BNY_ERROR, "SCardEstablishContext failed",
		    "error", BNY_STRING, pcsc_stringify_error(r), NULL);
		return (1);
	}

	err = agent_piv_open();
	if (err) {
		errf_free(err);
	} else {
		agent_piv_close(B_TRUE);
	}
	last_op = monotime();

	while (1) {
		prepare_poll(&pfd, &npfd, &timeout);
		result = poll(pfd, npfd, timeout);
		saved_errno = errno;
		if (parent_alive_interval != 0)
			check_parent_exists();
		now = monotime();
		if (card_probe_interval != 0 &&
		    (now - last_op) >= card_probe_interval * 1000) {
			probe_card();
		}
		if (txnopen && now >= txntimeout)
			agent_piv_close(B_TRUE);
		/*(void) reaper();*/	/* remove expired keys */
		if (result < 0) {
			if (saved_errno == EINTR)
				continue;
			fatal("poll: %s", strerror(saved_errno));
		} else if (result > 0)
			after_poll(pfd, npfd);
	}
	/* NOTREACHED */
}
