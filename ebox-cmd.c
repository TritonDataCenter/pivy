/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright (c) 2019, Joyent Inc
 * Author: Alex Wilson <alex.wilson@joyent.com>
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <stdint.h>
#include <stddef.h>
#include <errno.h>
#include <strings.h>
#include <limits.h>
#include <err.h>

#if defined(__APPLE__)
#include <PCSC/wintypes.h>
#include <PCSC/winscard.h>
#else
#include <wintypes.h>
#include <winscard.h>
#endif

#include <sys/types.h>
#include <sys/errno.h>
#include "debug.h"
#if defined(__sun)
#include <sys/fork.h>
#endif
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/mman.h>

#include "libssh/sshkey.h"
#include "libssh/sshbuf.h"
#include "libssh/digest.h"
#include "libssh/ssherr.h"
#include "libssh/authfd.h"

#include "sss/hazmat.h"

#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>

#include "tlv.h"
#include "errf.h"
#include "ebox.h"
#include "piv.h"
#include "bunyan.h"
#include "ebox-cmd.h"

#include "words.h"

int ebox_authfd;
SCARDCONTEXT ebox_ctx;
boolean_t ebox_ctx_init = B_FALSE;
char *ebox_pin;
uint ebox_min_retries = 1;
boolean_t ebox_batch = B_FALSE;

#if defined(__sun)
static GetLine *sungl = NULL;
static FILE *devterm = NULL;

char *
readline(const char *prompt)
{
	char *line;
	size_t len;
	if (sungl == NULL)
		qa_term_setup();
	line = gl_get_line(sungl, prompt, NULL, -1);
	if (line != NULL) {
		line = strdup(line);
		len = strlen(line);
		while (line[len - 1] == '\n' || line[len - 1] == '\r')
			line[--len] = '\0';
	}
	return (line);
}
#endif

void
qa_term_setup(void)
{
#if defined(RL_READLINE_VERSION)
	rl_instream = fopen("/dev/tty", "w+");
	rl_outstream = rl_instream;
#endif
#if defined(__sun)
	sungl = new_GetLine(1024, 2048);
	devterm = fopen("/dev/tty", "w+");
	gl_change_terminal(sungl, devterm, devterm, getenv("TERM"));
#endif
}

void
printwrap(FILE *stream, const char *data, size_t col)
{
	size_t offset = 0;
	size_t len = strlen(data);
	char *buf = malloc(col + 1);

	while (offset < len) {
		size_t rem = len - offset;
		if (rem > col)
			rem = col;
		bcopy(&data[offset], buf, rem);
		buf[rem] = 0;
		fprintf(stream, "%s\n", buf);
		offset += rem;
	}

	free(buf);
}

char *
piv_token_shortid(struct piv_token *pk)
{
	char *guid;
	guid = strdup(piv_token_guid_hex(pk));
	guid[8] = '\0';
	return (guid);
}

const char *
pin_type_to_name(enum piv_pin type)
{
	switch (type) {
	case PIV_PIN:
		return ("PIV PIN");
	case PIV_GLOBAL_PIN:
		return ("Global PIN");
	case PIV_PUK:
		return ("PUK");
	default:
		VERIFY(0);
		return (NULL);
	}
}

void
assert_pin(struct piv_token *pk, const char *partname, boolean_t prompt)
{
	errf_t *er;
	uint retries;
	boolean_t read_pin_env = B_FALSE;
	enum piv_pin auth = piv_token_default_auth(pk);
	const char *fmt = "Enter %s for token %s (%s): ";
	if (partname == NULL)
		fmt = "Enter %s for token %s: ";

again:
	if ( read_pin_env == B_TRUE ) {
		// get here after PIN has been read from enviroment
		errx(EXIT_PIN, "Invalid PIN in Enviroment-Varibale PIV_PIN");
		return;
	}
	if ((ebox_pin = getenv("PIV_PIN")) != NULL) {
		read_pin_env = B_TRUE;
		if (strlen(ebox_pin) < 6 || strlen(ebox_pin) > 8) {
			const char *charType = "digits";
			if (piv_token_is_ykpiv(pk))
				charType = "characters";
			free(ebox_pin);
			ebox_pin = NULL;
			errx(EXIT_PIN, "a valid PIN must be 6-8 %s in length",
			    charType);
			return;
		}
		ebox_pin = strdup(ebox_pin);
	}
	if (ebox_pin == NULL && !prompt) {
		return;
	}
	if (ebox_pin == NULL && prompt) {
		char prompt[64];
		char *guid = piv_token_shortid(pk);
		snprintf(prompt, 64, fmt,
		    pin_type_to_name(auth), guid, partname);
		do {
			ebox_pin = getpass(prompt);
		} while (ebox_pin == NULL && errno == EINTR);
		if ((ebox_pin == NULL && errno == ENXIO) ||
		    strlen(ebox_pin) < 1) {
			piv_txn_end(pk);
			errx(EXIT_PIN, "a PIN is required to unlock "
			    "token %s", guid);
		} else if (ebox_pin == NULL) {
			piv_txn_end(pk);
			err(EXIT_PIN, "failed to read PIN");
		} else if (strlen(ebox_pin) < 6 || strlen(ebox_pin) > 8) {
			const char *charType = "digits";
			if (piv_token_is_ykpiv(pk))
				charType = "characters";
			warnx("a valid PIN must be 6-8 %s in length",
			    charType);
			free(ebox_pin);
			free(guid);
			ebox_pin = NULL;
			goto again;
		}
		ebox_pin = strdup(ebox_pin);
		free(guid);
	}
	retries = ebox_min_retries;
	er = piv_verify_pin(pk, auth, ebox_pin, &retries, B_FALSE);
	if (errf_caused_by(er, "PermissionError")) {
		if (retries == 0) {
			piv_txn_end(pk);
			errx(EXIT_PIN_LOCKED, "token is locked due to too "
			    "many invalid PIN attempts");
		}
		warnx("invalid PIN (%d attempts remaining)", retries);
		free(ebox_pin);
		ebox_pin = NULL;
		errf_free(er);
		goto again;
	} else if (errf_caused_by(er, "MinRetriesError")) {
		piv_txn_end(pk);
		if (retries == 0) {
			errx(EXIT_PIN_LOCKED, "token is locked due to too "
			    "many invalid PIN attempts");
		}
		errx(EXIT_PIN, "insufficient PIN retries remaining (%d left)",
		    retries);
	} else if (er) {
		piv_txn_end(pk);
		errfx(EXIT_PIN, er, "failed to verify PIN");
	}
}

errf_t *
local_unlock_agent(struct piv_ecdh_box *box)
{
	struct piv_ecdh_box *rebox = NULL;
	struct sshkey *pubkey, *temp = NULL, *temppub = NULL;
	errf_t *err;
	int rc;
	uint i;
	uint8_t code;
	struct ssh_identitylist *idl = NULL;
	struct sshbuf *req = NULL, *buf = NULL, *boxbuf = NULL, *reply = NULL;
	struct sshbuf *datab = NULL;
	boolean_t found = B_FALSE;

	pubkey = piv_box_pubkey(box);

	rc = ssh_fetch_identitylist(ebox_authfd, &idl);
	if (rc) {
		err = ssherrf("ssh_fetch_identitylist", rc);
		goto out;
	}

	for (i = 0; i < idl->nkeys; ++i) {
		if (sshkey_equal_public(idl->keys[i], pubkey)) {
			found = B_TRUE;
			break;
		}
	}
	if (!found) {
		err = errf("KeyNotFound", NULL, "No matching key found in "
		    "ssh agent");
		goto out;
	}

	rc = sshkey_generate(KEY_ECDSA, sshkey_size(pubkey), &temp);
	if (rc) {
		err = ssherrf("sshkey_generate", rc);
		goto out;
	}
	if ((rc = sshkey_demote(temp, &temppub))) {
		err = ssherrf("sshkey_demote", rc);
		goto out;
	}

	req = sshbuf_new();
	reply = sshbuf_new();
	buf = sshbuf_new();
	boxbuf = sshbuf_new();
	if (req == NULL || reply == NULL || buf == NULL || boxbuf == NULL) {
		err = ERRF_NOMEM;
		goto out;
	}

	if ((rc = sshbuf_put_u8(req, SSH2_AGENTC_EXTENSION))) {
		err = ssherrf("sshbuf_put_u8", rc);
		goto out;
	}
	if ((rc = sshbuf_put_cstring(req, "ecdh-rebox@joyent.com"))) {
		err = ssherrf("sshbuf_put_cstring", rc);
		goto out;
	}

	if ((err = sshbuf_put_piv_box(boxbuf, box)))
		goto out;
	if ((rc = sshbuf_put_stringb(buf, boxbuf))) {
		err = ssherrf("sshbuf_put_stringb", rc);
		goto out;
	}
	if ((rc = sshbuf_put_u32(buf, 0)) ||
	    (rc = sshbuf_put_u8(buf, 0))) {
		err = ssherrf("sshbuf_put_u32", rc);
		goto out;
	}
	sshbuf_reset(boxbuf);
	if ((rc = sshkey_putb(temppub, boxbuf))) {
		err = ssherrf("sshkey_putb", rc);
		goto out;
	}
	if ((rc = sshbuf_put_stringb(buf, boxbuf))) {
		err = ssherrf("sshbuf_put_stringb", rc);
		goto out;
	}
	if ((rc = sshbuf_put_u32(buf, 0))) {
		err = ssherrf("sshbuf_put_u32", rc);
		goto out;
	}

	if ((rc = sshbuf_put_stringb(req, buf))) {
		err = ssherrf("sshbuf_put_stringb", rc);
		goto out;
	}

	rc = ssh_request_reply(ebox_authfd, req, reply);
	if (rc) {
		err = ssherrf("ssh_request_reply", rc);
		goto out;
	}

	if ((rc = sshbuf_get_u8(reply, &code))) {
		err = ssherrf("sshbuf_get_u8", rc);
		goto out;
	}
	if (code != SSH_AGENT_SUCCESS) {
		err = errf("SSHAgentError", NULL, "SSH agent returned "
		    "message code %d to rebox request", (int)code);
		goto out;
	}
	sshbuf_reset(boxbuf);
	if ((rc = sshbuf_get_stringb(reply, boxbuf))) {
		err = ssherrf("sshbuf_get_stringb", rc);
		goto out;
	}

	if ((err = sshbuf_get_piv_box(boxbuf, &rebox)))
		goto out;

	if ((err = piv_box_open_offline(temp, rebox)))
		goto out;

	if ((err = piv_box_take_datab(rebox, &datab)))
		goto out;

	if ((err = piv_box_set_datab(box, datab)))
		goto out;

	err = ERRF_OK;

out:
	sshbuf_free(req);
	sshbuf_free(reply);
	sshbuf_free(buf);
	sshbuf_free(boxbuf);
	sshbuf_free(datab);

	sshkey_free(temp);
	sshkey_free(temppub);

	ssh_free_identitylist(idl);
	piv_box_free(rebox);
	return (err);
}

errf_t *
local_unlock(struct piv_ecdh_box *box, struct sshkey *cak, const char *name)
{
	errf_t *err, *agerr = NULL;
	int rc;
	struct piv_slot *slot, *cakslot;
	struct piv_token *tokens = NULL, *token;

	if (ssh_get_authentication_socket(&ebox_authfd) != -1) {
		agerr = local_unlock_agent(box);
		if (agerr == ERRF_OK)
			return (ERRF_OK);
	}

	if (!piv_box_has_guidslot(box)) {
		if (agerr) {
			return (errf("AgentError", agerr, "ssh-agent unlock "
			    "failed, and box does not have GUID/slot info"));
		}
		return (errf("NoGUIDSlot", NULL, "box does not have GUID "
		    "and slot information, can't unlock with local hardware"));
	}

	if (!ebox_ctx_init) {
		rc = SCardEstablishContext(SCARD_SCOPE_SYSTEM, NULL, NULL,
		    &ebox_ctx);
		if (rc != SCARD_S_SUCCESS) {
			errfx(EXIT_ERROR, pcscerrf("SCardEstablishContext", rc),
			    "failed to initialise libpcsc");
		}
	}

	err = piv_find(ebox_ctx, piv_box_guid(box), GUID_LEN, &tokens);
	if (errf_caused_by(err, "NotFoundError")) {
		errf_free(err);
		err = piv_enumerate(ebox_ctx, &tokens);
		if (err && agerr) {
			err = errf("AgentError", agerr, "ssh-agent unlock "
			    "failed, and no PIV tokens were detected on "
			    "the local system");
		}
	}
	errf_free(agerr);
	if (err)
		goto out;

	err = piv_box_find_token(tokens, box, &token, &slot);
	if (err) {
		err = errf("LocalUnlockError", err, "failed to find token "
		    "with GUID %s and key for box",
		    piv_box_guid_hex(box));
		goto out;
	}

	if ((err = piv_txn_begin(token)))
		goto out;
	if ((err = piv_select(token))) {
		piv_txn_end(token);
		goto out;
	}

	if (cak != NULL) {
		cakslot = piv_get_slot(token, PIV_SLOT_CARD_AUTH);
		if (cakslot == NULL) {
			err = piv_read_cert(token, PIV_SLOT_CARD_AUTH);
			if (err) {
				err = errf("CardAuthenticationError", err,
				    "Failed to validate CAK");
				goto out;
			}
			cakslot = piv_get_slot(token, PIV_SLOT_CARD_AUTH);
		}
		if (cakslot == NULL) {
			err = errf("CardAuthenticationError", NULL,
			    "Failed to validate CAK");
			goto out;
		}
		err = piv_auth_key(token, cakslot, cak);
		if (err) {
			err = errf("CardAuthenticationError", err,
			    "Failed to validate CAK");
			goto out;
		}
	}

	boolean_t prompt = B_FALSE;
pin:
	assert_pin(token, name, prompt);
	err = piv_box_open(token, slot, box);
	if (errf_caused_by(err, "PermissionError") && !prompt && !ebox_batch) {
		errf_free(err);
		prompt = B_TRUE;
		goto pin;
	} else if (err) {
		piv_txn_end(token);
		err = errf("LocalUnlockError", err, "failed to unlock box");
		goto out;
	}

	piv_txn_end(token);
	err = ERRF_OK;

out:
	piv_release(tokens);
	return (err);
}

void
add_answer(struct question *q, struct answer *a)
{
	if (a->a_prev != NULL || a->a_next != NULL || q->q_lastans == a)
		return;
	if (q->q_lastans == NULL) {
		q->q_ans = a;
	} else {
		q->q_lastans->a_next = a;
		a->a_prev = q->q_lastans;
	}
	q->q_lastans = a;
}

void
add_spacer(struct question *q)
{
	struct answer *a;

	a = calloc(1, sizeof (struct answer));
	add_answer(q, a);
}

void
remove_answer(struct question *q, struct answer *a)
{
	if (a->a_prev != NULL) {
		a->a_prev->a_next = a->a_next;
	} else {
		if (q->q_ans != a && a->a_next == NULL)
			return;
		VERIFY(q->q_ans == a);
		q->q_ans = a->a_next;
	}
	if (a->a_next != NULL) {
		a->a_next->a_prev = a->a_prev;
	} else {
		if (q->q_lastans != a && a->a_prev == NULL)
			return;
		VERIFY(q->q_lastans == a);
		q->q_lastans = a->a_prev;
	}
}

void
answer_printf(struct answer *ans, const char *fmt, ...)
{
	va_list ap;
	int wrote;

	va_start(ap, fmt);
	wrote = vsnprintf(&ans->a_text[ans->a_used],
	    sizeof (ans->a_text) - ans->a_used, fmt, ap);
	VERIFY(wrote >= 0);
	va_end(ap);
	ans->a_used += wrote;
	if (ans->a_used >= sizeof (ans->a_text))
		ans->a_text[sizeof (ans->a_text) - 1] = '\0';
}

struct answer *
make_answer(char key, const char *fmt, ...)
{
	va_list ap;
	int wrote;
	struct answer *ans;

	ans = calloc(1, sizeof (struct answer));
	if (ans == NULL)
		err(EXIT_ERROR, "failed to allocate memory");
	ans->a_key = key;

	va_start(ap, fmt);
	wrote = vsnprintf(&ans->a_text[ans->a_used],
	    sizeof (ans->a_text) - ans->a_used, fmt, ap);
	VERIFY(wrote >= 0);
	va_end(ap);
	ans->a_used += wrote;
	if (ans->a_used >= sizeof (ans->a_text))
		ans->a_text[sizeof (ans->a_text) - 1] = '\0';

	return (ans);
}

void
add_command(struct question *q, struct answer *a)
{
	if (q->q_lastcom == NULL) {
		q->q_coms = a;
	} else {
		q->q_lastcom->a_next = a;
		a->a_prev = q->q_lastcom;
	}
	q->q_lastcom = a;
}

void
question_printf(struct question *q, const char *fmt, ...)
{
	va_list ap;
	int wrote;

	va_start(ap, fmt);
	wrote = vsnprintf(&q->q_prompt[q->q_used],
	    sizeof (q->q_prompt) - q->q_used, fmt, ap);
	VERIFY(wrote >= 0);
	va_end(ap);
	q->q_used += wrote;
	if (q->q_used >= sizeof (q->q_prompt))
		q->q_prompt[sizeof (q->q_prompt) - 1] = '\0';
}

void
question_free(struct question *q)
{
	struct answer *a, *na;

	if (q == NULL)
		return;

	for (a = q->q_ans; a != NULL; a = na) {
		na = a->a_next;
		if (a->a_priv == NULL)
			free(a);
	}
	for (a = q->q_coms; a != NULL; a = na) {
		na = a->a_next;
		if (a->a_priv == NULL)
			free(a);
	}

	free(q);
}

void
question_prompt(struct question *q, struct answer **ansp)
{
	struct answer *ans;
	char *line = NULL;

again:
	fprintf(stderr, "%s\n", q->q_prompt);
	for (ans = q->q_ans; ans != NULL; ans = ans->a_next) {
		if (ans->a_key == '\0') {
			fprintf(stderr, "\n");
			continue;
		}
		fprintf(stderr, "  [%c] %s\n", ans->a_key, ans->a_text);
	}
	fprintf(stderr, "\nCommands:\n");
	for (ans = q->q_coms; ans != NULL; ans = ans->a_next) {
		if (ans->a_key == '\0') {
			fprintf(stderr, "\n");
			continue;
		}
		fprintf(stderr, "  [%c] %s\n", ans->a_key, ans->a_text);
	}
	free(line);
	line = readline("Choice? ");
	if (line == NULL)
		exit(EXIT_ERROR);
	for (ans = q->q_ans; ans != NULL; ans = ans->a_next) {
		if (ans->a_key != '\0' &&
		    line[0] == ans->a_key && line[1] == '\0') {
			free(line);
			*ansp = ans;
			return;
		}
	}
	for (ans = q->q_coms; ans != NULL; ans = ans->a_next) {
		if (ans->a_key != '\0' &&
		    line[0] == ans->a_key && line[1] == '\0') {
			free(line);
			*ansp = ans;
			return;
		}
	}
	fprintf(stderr, "Invalid choice.\n");
	goto again;
}

enum part_intent {
	INTENT_NONE,
	INTENT_LOCAL,
	INTENT_CHAL_RESP
};

struct part_state {
	struct ebox_part *ps_part;
	struct answer *ps_ans;
	enum part_intent ps_intent;
};

static void
make_answer_text_for_pstate(struct part_state *state)
{
	struct ebox_tpl_part *tpart;
	struct answer *a;
	const char *name;
	char *guidhex = NULL;

	a = state->ps_ans;

	a->a_text[0] = '\0';
	a->a_used = 0;

	tpart = ebox_part_tpl(state->ps_part);

	guidhex = buf_to_hex(ebox_tpl_part_guid(tpart), 4, B_FALSE);
	answer_printf(a, "%s", guidhex);
	free(guidhex);

	name = ebox_tpl_part_name(tpart);
	if (name != NULL)
		answer_printf(a, " (%s)", name);

	switch (state->ps_intent) {
	case INTENT_NONE:
		break;
	case INTENT_LOCAL:
		answer_printf(a, "* [local]");
		break;
	case INTENT_CHAL_RESP:
		answer_printf(a, "* [remote/challenge-response]");
		break;
	}
}

static errf_t *
interactive_part_state(struct part_state *state)
{
	struct ebox_tpl_part *tpart;
	struct question *q = NULL;
	struct answer *a;
	char *guidhex = NULL;
	struct sshbuf *buf = NULL;
	int rc;

	tpart = ebox_part_tpl(state->ps_part);

	buf = sshbuf_new();
	if (buf == NULL)
		err(EXIT_ERROR, "memory allocation failed");

	q = calloc(1, sizeof (struct question));
	if (q == NULL)
		err(EXIT_ERROR, "memory allocation failed");
	question_printf(q, "-- Select recovery method for part %c --\n",
	    state->ps_ans->a_key);

	guidhex = buf_to_hex(ebox_tpl_part_guid(tpart), GUID_LEN, B_FALSE);
	question_printf(q, "GUID: %s\n", guidhex);
	free(guidhex);
	guidhex = NULL;

	question_printf(q, "Name: %s\n", ebox_tpl_part_name(tpart));

	if ((rc = sshkey_format_text(ebox_tpl_part_pubkey(tpart), buf))) {
		errfx(EXIT_ERROR, ssherrf("sshkey_format_text", rc),
		    "failed to write part public key");
	}
	if ((rc = sshbuf_put_u8(buf, '\0'))) {
		errfx(EXIT_ERROR, ssherrf("sshbuf_put_u8", rc),
		    "failed to write part public key (null)");
	}
	question_printf(q, "Public key (9d): %s", (char *)sshbuf_ptr(buf));
	sshbuf_reset(buf);

	a = make_answer('x', "Do not use%s",
	    (state->ps_intent == INTENT_NONE) ? "*" : "");
	add_answer(q, a);
	a = make_answer('l',
	    "Use locally (directly attached to this machine)%s",
	    (state->ps_intent == INTENT_LOCAL) ? "*" : "");
	add_answer(q, a);
	a = make_answer('r', "Use remotely (via challenge-response)%s",
	    (state->ps_intent == INTENT_CHAL_RESP) ? "*" : "");
	add_answer(q, a);

	question_prompt(q, &a);
	switch (a->a_key) {
	case 'x':
		state->ps_intent = INTENT_NONE;
		break;
	case 'l':
		state->ps_intent = INTENT_LOCAL;
		break;
	case 'r':
		state->ps_intent = INTENT_CHAL_RESP;
		break;
	}

	free(guidhex);
	sshbuf_free(buf);
	question_free(q);

	return (NULL);
}

static void
read_b64_box(struct piv_ecdh_box **outbox)
{
	char *linebuf, *p, *line;
	size_t len = 1024, pos = 0, llen;
	struct piv_ecdh_box *box = NULL;
	struct sshbuf *buf;

	linebuf = malloc(len);
	buf = sshbuf_new();
	VERIFY(linebuf != NULL);
	VERIFY(buf != NULL);

	do {
		if (len - pos < 128) {
			len *= 2;
			p = malloc(len);
			VERIFY(p != NULL);
			bcopy(linebuf, p, pos + 1);
			free(linebuf);
			linebuf = p;
		}
		line = readline("> ");
		if (line == NULL)
			exit(EXIT_ERROR);
		llen = strlen(line);
		if (llen >= 2 && line[0] == '-' && line[1] == '-')
			continue;
		while (pos + llen > len) {
			char *nlinebuf;
			len *= 2;
			nlinebuf = malloc(len);
			nlinebuf[0] = 0;
			strcpy(nlinebuf, linebuf);
			free(linebuf);
			linebuf = nlinebuf;
		}
		strcpy(&linebuf[pos], line);
		pos += llen;
		if (sshbuf_b64tod(buf, linebuf) == 0) {
			struct sshbuf *pbuf = sshbuf_fromb(buf);
			pos = 0;
			linebuf[0] = 0;
			if (sshbuf_get_piv_box(pbuf, &box) == 0)
				sshbuf_free(buf);
			sshbuf_free(pbuf);
		}
	} while (box == NULL);

	*outbox = box;
}

errf_t *
interactive_recovery(struct ebox_config *config, const char *what)
{
	struct ebox_part *part;
	struct ebox_tpl_config *tconfig;
	struct ebox_tpl_part *tpart;
	struct part_state *state;
	struct question *q;
	struct answer *a, *adone;
	struct sshbuf *buf;
	struct piv_ecdh_box *box;
	const struct ebox_challenge *chal;
	char k = '0';
	uint n, ncur;
	uint i;
	char *line;
	char *b64;
	errf_t *error;
	const uint8_t *words;
	size_t wordlen;

	tconfig = ebox_config_tpl(config);
	n = ebox_tpl_config_n(tconfig);

	if (ebox_batch) {
		error = errf("InteractiveError", NULL,
		    "interactive recovery is required but the -b batch option "
		    "was provided");
		return (error);
	}

	q = calloc(1, sizeof (struct question));
	a = (struct answer *)ebox_config_private(config);
	question_printf(q, "-- Recovery config %c --\n", a->a_key);
	question_printf(q, "Select %u parts to use for recovery", n);

	part = NULL;
	while ((part = ebox_config_next_part(config, part)) != NULL) {
		tpart = ebox_part_tpl(part);
		state = ebox_part_alloc_private(part,
		    sizeof (struct part_state));
		VERIFY(state != NULL);
		state->ps_part = part;
		state->ps_ans = (a = calloc(1, sizeof (struct answer)));
		a->a_key = ++k;
		a->a_priv = state;
		VERIFY(state->ps_ans != NULL);
		state->ps_intent = INTENT_NONE;
		make_answer_text_for_pstate(state);
		add_answer(q, a);
	}

	adone = make_answer('r', "begin recovery");

again:
	question_prompt(q, &a);
	if (a->a_key == 'r') {
		goto recover;
	}
	state = (struct part_state *)a->a_priv;
	interactive_part_state(state);
	make_answer_text_for_pstate(state);
	ncur = 0;
	part = NULL;
	while ((part = ebox_config_next_part(config, part)) != NULL) {
		state = (struct part_state *)ebox_part_private(part);
		if (state->ps_intent != INTENT_NONE)
			++ncur;
	}
	if (ncur >= n) {
		add_answer(q, adone);
	} else {
		remove_answer(q, adone);
	}
	goto again;

recover:
	fprintf(stderr,
	    "-- Beginning recovery --\n"
	    "Local devices will be attempted in order before remote "
	    "challenge-responses are processed.\n\n");
	ncur = 0;

	part = NULL;
	while ((part = ebox_config_next_part(config, part)) != NULL) {
		state = (struct part_state *)ebox_part_private(part);
		part = state->ps_part;
		tpart = ebox_part_tpl(part);
		if (state->ps_intent != INTENT_LOCAL)
			continue;
		state->ps_intent = INTENT_NONE;
		make_answer_text_for_pstate(state);
		fprintf(stderr, "-- Local device %s --\n",
		    state->ps_ans->a_text);
partagain:
		error = local_unlock(ebox_part_box(part),
		    ebox_tpl_part_cak(tpart), ebox_tpl_part_name(tpart));
		if (error && !errf_caused_by(error, "NotFoundError"))
			return (error);
		if (error) {
			warnfx(error, "failed to find device");
			line = readline("Retry? ");
			free(line);
			goto partagain;
		}
		fprintf(stderr, "Device box decrypted ok.\n");
		++ncur;
		/*
		 * Forget any PIN the user entered, we'll be talking to a
		 * different device next.
		 */
		free(ebox_pin);
		ebox_pin = NULL;
	}

	buf = sshbuf_new();
	VERIFY(buf != NULL);

	part = NULL;
	while ((part = ebox_config_next_part(config, part)) != NULL) {
		state = (struct part_state *)ebox_part_private(part);
		if (state->ps_intent != INTENT_CHAL_RESP)
			continue;
		state->ps_intent = INTENT_NONE;
		make_answer_text_for_pstate(state);
		state->ps_intent = INTENT_CHAL_RESP;
		error = ebox_gen_challenge(config, part,
		    "Recovering %s with part %s", what, state->ps_ans->a_text);
		if (error) {
			sshbuf_free(buf);
			return (error);
		}
		chal = ebox_part_challenge(part);
		sshbuf_reset(buf);
		error = sshbuf_put_ebox_challenge(buf, chal);
		if (error) {
			sshbuf_free(buf);
			return (error);
		}
		b64 = sshbuf_dtob64(buf);
		VERIFY(b64 != NULL);
		fprintf(stderr, "-- Begin challenge for remote device %s --\n",
		    state->ps_ans->a_text);
		printwrap(stderr, b64, BASE64_LINE_LEN);
		fprintf(stderr, "-- End challenge for remote device %s --\n",
		    state->ps_ans->a_text);
		free(b64);
		b64 = NULL;

		words = ebox_challenge_words(chal, &wordlen);
		fprintf(stderr, "\nVERIFICATION WORDS for %s:",
		    state->ps_ans->a_text);
		for (i = 0; i < wordlen; ++i)
			fprintf(stderr, " %s", wordlist[words[i]]);
		fprintf(stderr, "\n\n");
	}

	while (ncur < n) {
		fprintf(stderr, "\nRemaining responses required:\n");
		part = NULL;
		while ((part = ebox_config_next_part(config, part)) != NULL) {
			state = (struct part_state *)ebox_part_private(part);
			if (state->ps_intent != INTENT_CHAL_RESP)
				continue;
			fprintf(stderr, "  * %s\n", state->ps_ans->a_text);
		}
		fprintf(stderr, "\n-- Enter response followed by newline --\n");
		read_b64_box(&box);
		fprintf(stderr, "-- End response --\n");
		error = ebox_challenge_response(config, box, &part);
		if (error) {
			warnfx(error, "failed to parse input data as a "
			    "valid response");
			continue;
		}
		state = (struct part_state *)ebox_part_private(part);
		if (state->ps_intent != INTENT_CHAL_RESP) {
			fprintf(stderr, "Response already processed for "
			    "device %s!\n", state->ps_ans->a_text);
			continue;
		}
		fprintf(stderr, "Device box for %s decrypted ok.\n",
		    state->ps_ans->a_text);
		state->ps_intent = INTENT_NONE;
		++ncur;
	}
	sshbuf_free(buf);
	return (NULL);
}

struct ebox_tpl *
read_tpl_file(const char *tpl)
{
	errf_t *error;
	FILE *tplf;
	struct stat st;
	char *buf;
	struct sshbuf *sbuf;
	size_t len;
	int rc;
	struct ebox_tpl *stpl;
	char pathTpl[PATH_MAX] = { 0 };

again:
	tplf = fopen(tpl, "r");
	rc = errno;
	if (tplf == NULL && tpl != pathTpl && errno == ENOENT) {
		const char *home;
		home = getenv("HOME");
		if (home == NULL) {
			errno = rc;
			err(EXIT_ERROR, "failed to open template file '%s' "
			    "for reading", tpl);
		}
		snprintf(pathTpl, sizeof (pathTpl), TPL_DEFAULT_PATH,
		    home, tpl);
		tpl = pathTpl;
		goto again;
	} else if (tplf == NULL) {
		err(EXIT_ERROR, "failed to open template file '%s' for reading",
		    tpl);
	}
	bzero(&st, sizeof (st));
	if (fstat(fileno(tplf), &st))
		err(EXIT_ERROR, "failed to get size of '%s'", tpl);
	if (!S_ISREG(st.st_mode))
		err(EXIT_ERROR, "'%s' is not a regular file", tpl);
	if (st.st_size > TPL_MAX_SIZE)
		err(EXIT_ERROR, "'%s' is too large for an ebox template", tpl);
	buf = malloc(st.st_size + 1);
	if (buf == NULL) {
		err(EXIT_ERROR, "out of memory while allocating template "
		    "read buffer");
	}
	len = fread(buf, 1, st.st_size, tplf);
	if (len < st.st_size && feof(tplf)) {
		errx(EXIT_ERROR, "short read while processing template '%s'",
		    tpl);
	}
	buf[len] = '\0';
	if (ferror(tplf))
		err(EXIT_ERROR, "error reading from template file '%s'", tpl);
	if (fclose(tplf))
		err(EXIT_ERROR, "error closing file '%s'", tpl);
	sbuf = sshbuf_new();
	if (sbuf == NULL) {
		err(EXIT_ERROR, "out of memory while allocating template "
		    "processing buffer");
	}
	if ((rc = sshbuf_b64tod(sbuf, buf))) {
		error = ssherrf("sshbuf_b64tod", rc);
		errfx(EXIT_ERROR, error, "failed to parse contents of '%s' as "
		    "base64-encoded data", tpl);
	}
	if ((error = sshbuf_get_ebox_tpl(sbuf, &stpl))) {
		errfx(EXIT_ERROR, error, "failed to parse contents of '%s' as "
		    "a base64-encoded ebox template", tpl);
	}
	sshbuf_free(sbuf);
	free(buf);

	return (stpl);
}

void
interactive_select_local_token(struct ebox_tpl_part **ppart)
{
	int rc;
	errf_t *error;
	struct piv_token *tokens = NULL, *token;
	struct piv_slot *slot;
	struct ebox_tpl_part *part;
	struct question *q;
	struct answer *a;
	char *shortid;
	enum piv_slotid slotid = PIV_SLOT_KEY_MGMT;
	char k = '0';
	char *line, *p;
	unsigned long parsed;

	if (!ebox_ctx_init) {
		rc = SCardEstablishContext(SCARD_SCOPE_SYSTEM, NULL, NULL,
		    &ebox_ctx);
		if (rc != SCARD_S_SUCCESS) {
			errfx(EXIT_ERROR, pcscerrf("SCardEstablishContext", rc),
			    "failed to initialise libpcsc");
		}
	}

reenum:
	error = piv_enumerate(ebox_ctx, &tokens);
	if (error) {
		warnfx(error, "failed to enumerate PIV tokens on the system");
		*ppart = NULL;
		errf_free(error);
		return;
	}

	q = calloc(1, sizeof (struct question));
	question_printf(q, "-- Selecting local PIV token --\n");
	question_printf(q, "Select a token to use:");

	for (token = tokens; token != NULL; token = piv_token_next(token)) {
		shortid = piv_token_shortid(token);
		if (piv_token_is_ykpiv(token) &&
		    ykpiv_token_has_serial(token)) {
			a = make_answer(++k, "%s (in %s) [serial# %u]",
			    shortid, piv_token_rdrname(token),
			    ykpiv_token_serial(token));
		} else {
			a = make_answer(++k, "%s (in %s)",
			    shortid, piv_token_rdrname(token));
		}
		free(shortid);
		a->a_priv = token;
		add_answer(q, a);
	}

	a = make_answer('s', "change key slot (%02X)", slotid);
	add_command(q, a);

	a = make_answer('r', "re-scan");
	add_command(q, a);

	a = make_answer('x', "cancel");
	add_command(q, a);

again:
	question_prompt(q, &a);
	if (a->a_key == 'x') {
		*ppart = NULL;
		question_free(q);
		piv_release(tokens);
		return;
	} else if (a->a_key == 'r') {
		*ppart = NULL;
		k = '0';
		question_free(q);
		piv_release(tokens);
		goto reenum;
	} else if (a->a_key == 's') {
		line = readline("Slot ID (hex)? ");
		if (line == NULL)
			exit(EXIT_ERROR);
		errno = 0;
		parsed = strtoul(line, &p, 16);
		if (errno != 0 || *p != '\0') {
			error = errfno("strtoul", errno, NULL);
			warnfx(error, "error parsing '%s' as hex number",
			    line);
			errf_free(error);
			free(line);
			goto again;
		}
		if (parsed > 0xFF) {
			warnx("slot '%02X' is not a valid PIV slot id",
			    (uint)parsed);
			free(line);
			goto again;
		}
		slotid = parsed;
		a->a_used = 0;
		answer_printf(a, "change key slot (%02X)", slotid);
		free(line);
		goto again;
	}
	token = (struct piv_token *)a->a_priv;

	if ((error = piv_txn_begin(token)))
		errfx(EXIT_ERROR, error, "failed to open token");
	if ((error = piv_select(token)))
		errfx(EXIT_ERROR, error, "failed to select PIV applet");
	if ((error = piv_read_cert(token, slotid))) {
		warnfx(error, "failed to read key management (9d) slot");
		errf_free(error);
		piv_txn_end(token);
		goto again;
	}
	slot = piv_get_slot(token, slotid);
	VERIFY(slot != NULL);
	part = ebox_tpl_part_alloc(piv_token_guid(token), GUID_LEN,
	    piv_slot_id(slot), piv_slot_pubkey(slot));
	VERIFY(part != NULL);
	error = piv_read_cert(token, PIV_SLOT_CARD_AUTH);
	if (error == NULL) {
		slot = piv_get_slot(token, PIV_SLOT_CARD_AUTH);
		ebox_tpl_part_set_cak(part, piv_slot_pubkey(slot));
	} else {
		errf_free(error);
	}
	piv_txn_end(token);

	*ppart = part;
	piv_release(tokens);
}

void
make_answer_text_for_part(struct ebox_tpl_part *part, struct answer *a)
{
	const char *name;
	char *guidhex = NULL;

	a->a_text[0] = '\0';
	a->a_used = 0;

	guidhex = buf_to_hex(ebox_tpl_part_guid(part),
	    4, B_FALSE);
	answer_printf(a, "%s", guidhex);
	name = ebox_tpl_part_name(part);
	if (name != NULL) {
		answer_printf(a, " (%s)", name);
	}

	free(guidhex);
}

void
make_answer_text_for_config(struct ebox_tpl_config *config, struct answer *a)
{
	struct ebox_tpl_part *part, *npart;
	const char *name;
	char *guidhex = NULL;

	a->a_text[0] = '\0';
	a->a_used = 0;

	switch (ebox_tpl_config_type(config)) {
	case EBOX_PRIMARY:
		part = ebox_tpl_config_next_part(config, NULL);
		if (part == NULL) {
			answer_printf(a, "primary: none");
			break;
		}
		free(guidhex);
		guidhex = buf_to_hex(ebox_tpl_part_guid(part),
		    4, B_FALSE);
		answer_printf(a, "primary: %s", guidhex);
		name = ebox_tpl_part_name(part);
		if (name != NULL) {
			answer_printf(a, " (%s)", name);
		}
		break;
	case EBOX_RECOVERY:
		answer_printf(a, "recovery: any %u of: ",
		    ebox_tpl_config_n(config));
		part = ebox_tpl_config_next_part(config, NULL);
		while (part != NULL) {
			npart = ebox_tpl_config_next_part(
			    config, part);
			free(guidhex);
			guidhex = buf_to_hex(
			    ebox_tpl_part_guid(part), 4,
			    B_FALSE);
			answer_printf(a, "%s", guidhex);
			name = ebox_tpl_part_name(part);
			if (name != NULL) {
				answer_printf(a, " (%s)", name);
			}
			if (npart != NULL) {
				answer_printf(a, ", ");
			}
			part = npart;
		}
		break;
	}
	free(guidhex);
}
