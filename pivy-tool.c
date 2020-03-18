/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright (c) 2017, Joyent Inc
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
#if defined(__sun)
#include <sys/fork.h>
#endif
#include <sys/wait.h>

#include "libssh/sshkey.h"
#include "libssh/sshbuf.h"
#include "libssh/digest.h"
#include "libssh/ssherr.h"

#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/x509v3.h>

int PEM_write_X509(FILE *fp, X509 *x);

#include "ed25519/crypto_api.h"

#include "utils.h"
#include "tlv.h"
#include "piv.h"
#include "bunyan.h"
#include "utils.h"
#include "debug.h"

/* We need the piv_cert_comp enum */
#include "piv-internal.h"

#if defined(__sun) || defined(__APPLE__)
#include <netinet/in.h>
#define	be16toh(v)	(ntohs(v))
#else
#include <endian.h>
#endif

boolean_t debug = B_FALSE;
static boolean_t parseable = B_FALSE;
static const char *cn = NULL;
static uint8_t *guid = NULL;
static size_t guid_len = 0;
static uint min_retries = 1;
static struct sshkey *opubkey = NULL;
static const char *pin = NULL;
static const uint8_t DEFAULT_ADMIN_KEY[] = {
	0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
	0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
	0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
};
static const uint8_t *admin_key = DEFAULT_ADMIN_KEY;

static enum ykpiv_pin_policy pinpolicy = YKPIV_PIN_DEFAULT;
static enum ykpiv_touch_policy touchpolicy = YKPIV_TOUCH_DEFAULT;

static struct piv_token *ks = NULL;
static struct piv_token *selk = NULL;
//static struct piv_token *sysk = NULL;
static struct piv_slot *override = NULL;

SCARDCONTEXT ctx;

#ifndef LINT
#define	funcerrf(cause, fmt, ...)	\
    errf(__func__, cause, fmt , ##__VA_ARGS__)
#define pcscerrf(call, rv)	\
    errf("PCSCError", NULL, call " failed: %d (%s)", \
    rv, pcsc_stringify_error(rv))
#endif

enum pivtool_exit_status {
	EXIT_OK = 0,
	EXIT_IO_ERROR = 1,
	EXIT_BAD_ARGS = 2,
	EXIT_NO_CARD = 3,
	EXIT_PIN = 4,
	EXIT_PIN_LOCKED = 5,
};

static boolean_t
sniff_hex(uint8_t *buf, uint len)
{
	uint i, count = 0;
	len = len > 16 ? 16 : len;
	for (i = 0; i < len; ++i) {
		char c;
		if (buf[i] > CHAR_MAX)
			return (B_FALSE);
		c = buf[i];
		if (c >= '0' && c <= '9') {
			++count;
			continue;
		}
		if (c >= 'a' && c <= 'f') {
			++count;
			continue;
		}
		if (c == ':' || c == ' ' || c == '\t' || c == '\n' ||
		    c == '\r') {
			++count;
			continue;
		}
		return (B_FALSE);
	}
	if (count >= 8)
		return (B_TRUE);
	return (B_FALSE);
}

static boolean_t
buf_is_zero(const uint8_t *buf, size_t len)
{
	uint8_t v = 0;
	size_t i;
	for (i = 0; i < len; ++i)
		v |= buf[i];
	return (v == 0);
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
		boolean_t skip = B_FALSE;
		if (c >= '0' && c <= '9') {
			data[idx] |= (c - '0') << shift;
		} else if (c >= 'a' && c <= 'f') {
			data[idx] |= (c - 'a' + 0xa) << shift;
		} else if (c >= 'A' && c <= 'F') {
			data[idx] |= (c - 'A' + 0xA) << shift;
		} else if (c == ':' || c == ' ' || c == '\t' ||
		    c == '\n' || c == '\r') {
			skip = B_TRUE;
		} else {
			errx(EXIT_BAD_ARGS, "invalid hex digit: '%c'", c);
		}
		if (skip == B_FALSE) {
			if (shift == 4) {
				shift = 0;
			} else if (shift == 0) {
				++idx;
				shift = 4;
			}
		}
	}
	if (shift == 0)
		errx(EXIT_BAD_ARGS, "odd number of hex digits (incomplete)");
	*outlen = idx;
	return (data);
}

#define	MAX_KEYFILE_LEN		(1024)

static uint8_t *
read_key_file(const char *fname, uint *outlen)
{
	FILE *f;
	uint len;
	uint8_t *buf;

	f = fopen(fname, "r");
	if (f == NULL)
		err(EXIT_BAD_ARGS, "failed to open '%s'", fname);

	buf = calloc(1, MAX_KEYFILE_LEN);
	VERIFY(buf != NULL);

	len = fread(buf, 1, MAX_KEYFILE_LEN, f);
	if (len == 0)
		errx(EXIT_BAD_ARGS, "keyfile '%s' is too short", fname);
	if (!feof(f))
		errx(EXIT_BAD_ARGS, "keyfile '%s' is too long", fname);

	*outlen = len;

	fclose(f);

	return (buf);
}

static uint8_t *
read_stdin(size_t limit, size_t *outlen)
{
	uint8_t *buf = calloc(1, limit * 3);
	size_t n;

	n = fread(buf, 1, limit * 3 - 1, stdin);
	if (!feof(stdin))
		errx(EXIT_BAD_ARGS, "input too long (max %zu bytes)", limit);

	if (n > limit)
		errx(EXIT_BAD_ARGS, "input too long (max %zu bytes)", limit);

	*outlen = n;
	return (buf);
}

static char *
piv_token_shortid(struct piv_token *pk)
{
	char *guid;
	if (piv_token_has_chuid(pk)) {
		guid = strdup(piv_token_guid_hex(pk));
	} else {
		guid = strdup("0000000000");
	}
	guid[8] = '\0';
	return (guid);
}

static void
assert_select(struct piv_token *tk)
{
	errf_t *err;

	err = piv_select(tk);
	if (err) {
		piv_txn_end(tk);
		errfx(1, err, "error while selecting applet");
	}
}

static const char *
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

static void
assert_slotid(uint slotid)
{
	if (slotid >= 0x9A && slotid <= 0x9E && slotid != 0x9B)
		return;
	if (slotid >= PIV_SLOT_RETIRED_1 && slotid <= PIV_SLOT_RETIRED_20)
		return;
	errx(EXIT_BAD_ARGS, "PIV slot %02X cannot be used for asymmetric "
	    "signing", slotid);
}

static void
assert_pin(struct piv_token *pk, boolean_t prompt)
{
	errf_t *er;
	uint retries = min_retries;
	enum piv_pin auth = piv_token_default_auth(pk);

#if 0
	if (pin == NULL && pk == sysk) {
		rv = piv_system_token_auth(pk);
		if (rv == 0)
			return;
	}
#endif

	if (pin == NULL && !prompt)
		return;

	if (pin == NULL && prompt) {
		char prompt[64];
		char *guid = piv_token_shortid(pk);
		snprintf(prompt, 64, "Enter %s for token %s: ",
		    pin_type_to_name(auth), guid);
		do {
			pin = getpass(prompt);
		} while (pin == NULL && errno == EINTR);
		if ((pin == NULL && errno == ENXIO) || strlen(pin) < 1) {
			piv_txn_end(pk);
			errx(EXIT_PIN, "a PIN is required to unlock "
			    "token %s", guid);
		} else if (pin == NULL) {
			piv_txn_end(pk);
			err(EXIT_PIN, "failed to read PIN");
		} else if (strlen(pin) < 6 || strlen(pin) > 8) {
			const char *charType = "digits";
			if (piv_token_is_ykpiv(selk))
				charType = "characters";
			errx(EXIT_PIN, "a valid PIN must be 6-8 %s in length",
			    charType);
		}
		pin = strdup(pin);
		free(guid);
	}
	er = piv_verify_pin(pk, auth, pin, &retries, B_FALSE);
	if (errf_caused_by(er, "PermissionError")) {
		piv_txn_end(pk);
		if (retries == 0) {
			errx(EXIT_PIN_LOCKED, "token is locked due to too "
			    "many invalid PIN attempts");
		}
		errx(EXIT_PIN, "invalid PIN (%d attempts remaining)", retries);
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


static const char *
alg_to_string(uint alg)
{
	switch (alg) {
	case PIV_ALG_3DES:
		return ("3DES");
	case PIV_ALG_RSA1024:
		return ("RSA1024");
	case PIV_ALG_RSA2048:
		return ("RSA2048");
	case PIV_ALG_AES128:
		return ("AES128");
	case PIV_ALG_AES192:
		return ("AES192");
	case PIV_ALG_AES256:
		return ("AES256");
	case PIV_ALG_ECCP256:
		return ("ECCP256");
	case PIV_ALG_ECCP384:
		return ("ECCP384");
	case PIV_ALG_ECCP256_SHA1:
		return ("ECCP256-SHA1");
	case PIV_ALG_ECCP256_SHA256:
		return ("ECCP256-SHA256");
	default:
		return ("?");
	}
}

static errf_t *
cmd_list(void)
{
	struct piv_token *pk;
	struct piv_slot *slot = NULL;
	uint i;
	char *buf = NULL;
	const uint8_t *temp;
	size_t len;
	enum piv_pin defauth;
	errf_t *err;

	for (pk = ks; pk != NULL; pk = piv_token_next(pk)) {
		const uint8_t *tguid = piv_token_guid(pk);
		if (guid != NULL &&
		    bcmp(tguid, guid, guid_len) != 0) {
			continue;
		}

		if ((err = piv_txn_begin(pk)))
			return (err);
		assert_select(pk);
		if ((err = piv_read_all_certs(pk))) {
			piv_txn_end(pk);
			return (err);
		}
		piv_txn_end(pk);

		if (parseable) {
			uint8_t nover[] = { 0, 0, 0 };
			const uint8_t *ver = nover;
			if (piv_token_is_ykpiv(pk))
				ver = ykpiv_token_version(pk);
			printf("%s:%s:%s:%s:%d.%d.%d:",
			    piv_token_rdrname(pk),
			    piv_token_guid_hex(pk),
			    piv_token_has_chuid(pk) ? "true" : "false",
			    piv_token_is_ykpiv(pk) ? "true" : "false",
			    ver[0], ver[1], ver[2]);
			for (i = 0; i < piv_token_nalgs(pk); ++i) {
				enum piv_alg alg = piv_token_alg(pk, i);
				printf("%s%s", alg_to_string(alg),
				    (i + 1 < piv_token_nalgs(pk)) ? "," : "");
			}
			for (i = 0x9A; i < 0x9F; ++i) {
				slot = piv_get_slot(pk, i);
				if (slot == NULL) {
					printf(":%02X", i);
				} else {
					struct sshkey *key =
					    piv_slot_pubkey(slot);
					printf(":%02X;%s;%s;%u",
					    i, piv_slot_subject(slot),
					    sshkey_type(key),
					    sshkey_size(key));
				}
			}
			printf("\n");
			continue;
		}

		if (piv_token_has_chuid(pk)) {
			buf = piv_token_shortid(pk);
		} else {
			buf = strdup("00000000");
		}
		printf("%10s: %s\n", "card", buf);
		free(buf);
		printf("%10s: %s\n", "device", piv_token_rdrname(pk));
		if (!piv_token_has_chuid(pk)) {
			printf("%10s: %s\n", "chuid", "not set "
			    "(needs initialization)");
		} else if (piv_token_has_signed_chuid(pk)) {
			printf("%10s: %s\n", "chuid", "ok, signed");
		} else {
			printf("%10s: %s\n", "chuid", "ok");
		}
		printf("%10s: %s\n", "guid", piv_token_guid_hex(pk));
		temp = piv_token_chuuid(pk);
		if (temp != NULL) {
			buf = buf_to_hex(temp, 16, B_FALSE);
			printf("%10s: %s\n", "owner", buf);
			free(buf);
		}
		temp = piv_token_fascn(pk, &len);
		if (temp != NULL && len > 0) {
			buf = buf_to_hex(temp, len, B_FALSE);
			printf("%10s: %s\n", "fasc-n", buf);
			free(buf);
		}
		temp = piv_token_expiry(pk, &len);
		if (len == 8 && temp[0] >= '0' && temp[0] <= '9') {
			printf("%10s: %c%c%c%c-%c%c-%c%c\n", "expiry",
			    temp[0], temp[1], temp[2], temp[3],
			    temp[4], temp[5], temp[6], temp[7]);
		}
		if (piv_token_is_ykpiv(pk)) {
			temp = ykpiv_token_version(pk);
			printf("%10s: implements YubicoPIV extensions "
			    "(v%d.%d.%d)\n", "yubico", temp[0], temp[1],
			    temp[2]);
			if (ykpiv_token_has_serial(pk)) {
				printf("%10s: %u\n", "serial",
				    ykpiv_token_serial(pk));
			}
		}
		printf("%10s:", "auth");
		defauth = piv_token_default_auth(pk);
		if (piv_token_has_auth(pk, PIV_PIN)) {
			if (defauth == PIV_PIN)
				printf(" PIN*");
			else
				printf(" PIN");
		}
		if (piv_token_has_auth(pk, PIV_GLOBAL_PIN)) {
			if (defauth == PIV_GLOBAL_PIN)
				printf(" GlobalPIN*");
			else
				printf(" GlobalPIN");
		}
		if (piv_token_has_auth(pk, PIV_OCC)) {
			if (defauth == PIV_OCC)
				printf(" Biometrics*");
			else
				printf(" Biometrics");
		}
		printf("\n");
		if (piv_token_has_vci(pk)) {
			printf("%10s: supports VCI (secure contactless)\n",
			    "vci");
		}
		if (piv_token_nalgs(pk) > 0) {
			printf("%10s: ", "algos");
			for (i = 0; i < piv_token_nalgs(pk); ++i) {
				printf("%s ", alg_to_string(
				    piv_token_alg(pk, i)));
			}
			printf("\n");
		}
		if (!piv_token_has_chuid(pk)) {
			printf("%10s:\n", "action");
			printf("%10s Initialize this card using 'pivy-tool "
			    "init'\n", "");
			printf("%10s No keys can be stored on an uninitialized"
			    " card\n", "");
			printf("\n");
			continue;
		}
		printf("%10s:\n", "slots");
		printf("%10s %-3s  %-6s  %-4s  %-30s\n", "", "ID", "TYPE",
		    "BITS", "CERTIFICATE");
		while ((slot = piv_slot_next(pk, slot)) != NULL) {
			struct sshkey *pubkey = piv_slot_pubkey(slot);
			printf("%10s %-3x  %-6s  %-4u  %-30s\n", "",
			    piv_slot_id(slot), sshkey_type(pubkey),
			    sshkey_size(pubkey), piv_slot_subject(slot));
		}
		printf("\n");
	}

	return (ERRF_OK);
}

static errf_t *
cmd_init(void)
{
	errf_t *err;
	struct tlv_state *ccc, *chuid;
	uint8_t nguid[16];
	uint8_t fascn[25];
	uint8_t expiry[8] = { '2', '0', '5', '0', '0', '1', '0', '1' };
	uint8_t cardId[21] = {
		/* GSC-RID: GSC-IS data model */
		0xa0, 0x00, 0x00, 0x01, 0x16,
		/* Manufacturer: ff (unknown) */
		0xff,
		/* Card type: JavaCard */
		0x02,
		0x00
	};

	arc4random_buf(nguid, sizeof (nguid));
	arc4random_buf(&cardId[6], sizeof (cardId) - 6);
	bzero(fascn, sizeof (fascn));

	/* First, the CCC */
	ccc = tlv_init_write();

	/* Our card ID */
	tlv_push(ccc, 0xF0);
	tlv_write(ccc, cardId, sizeof (cardId));
	tlv_pop(ccc);

	/* Container version numbers */
	tlv_push(ccc, 0xF1);
	tlv_write_byte(ccc, 0x21);
	tlv_pop(ccc);
	tlv_push(ccc, 0xF2);
	tlv_write_byte(ccc, 0x21);
	tlv_pop(ccc);

	tlv_push(ccc, 0xF3);
	tlv_pop(ccc);
	tlv_push(ccc, 0xF4);
	tlv_pop(ccc);

	/* Data Model number */
	tlv_push(ccc, 0xF5);
	tlv_write_byte(ccc, 0x10);
	tlv_pop(ccc);

	tlv_push(ccc, 0xF6);
	tlv_pop(ccc);
	tlv_push(ccc, 0xF7);
	tlv_pop(ccc);
	tlv_push(ccc, 0xFA);
	tlv_pop(ccc);
	tlv_push(ccc, 0xFB);
	tlv_pop(ccc);
	tlv_push(ccc, 0xFC);
	tlv_pop(ccc);
	tlv_push(ccc, 0xFD);
	tlv_pop(ccc);
	tlv_push(ccc, 0xFE);
	tlv_pop(ccc);

	/* Now, set up the CHUID file */
	chuid = tlv_init_write();

	tlv_push(chuid, 0x30);
	tlv_write(chuid, fascn, sizeof (fascn));
	tlv_pop(chuid);

	tlv_push(chuid, 0x34);
	tlv_write(chuid, nguid, sizeof (nguid));
	tlv_pop(chuid);

	tlv_push(chuid, 0x35);
	tlv_write(chuid, expiry, sizeof (expiry));
	tlv_pop(chuid);

	tlv_push(chuid, 0x3E);
	tlv_pop(chuid);
	tlv_push(chuid, 0xFE);
	tlv_pop(chuid);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_auth_admin(selk, admin_key, 24);
	if (err == ERRF_OK) {
		err = piv_write_file(selk, PIV_TAG_CARDCAP,
		    tlv_buf(ccc), tlv_len(ccc));
	}
	if (err == ERRF_OK) {
		err = piv_write_file(selk, PIV_TAG_CHUID,
		    tlv_buf(chuid), tlv_len(chuid));
	}
	piv_txn_end(selk);

	tlv_free(ccc);
	tlv_free(chuid);

	if (errf_caused_by(err, "DeviceOutOfMemoryError")) {
		err = funcerrf(err, "out of EEPROM to write CHUID "
		    "and CARDCAP");
		return (err);
	} else if (errf_caused_by(err, "PermissionError")) {
		err = funcerrf(err, "cannot write init data due to failed "
		    "admin authentication");
		return (err);
	} else if (err) {
		err = funcerrf(err, "failed to write to card");
		return (err);
	}

	/* This is for cmd_setup */
	guid = malloc(16);
	bcopy(nguid, guid, sizeof (nguid));
	guid_len = 16;

	return (ERRF_OK);
}

static errf_t *
cmd_set_admin(uint8_t *new_admin_key)
{
	errf_t *err;

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_auth_admin(selk, admin_key, 24);
	if (err) {
		err = funcerrf(err, "Failed to authenticate with old admin key");
	} else {
		err = ykpiv_set_admin(selk, new_admin_key, 24, touchpolicy);
		if (err) {
			err = funcerrf(err, "Failed to set new admin key");
		}
	}
	piv_txn_end(selk);

	if (err)
		return (err);
	return (ERRF_OK);
}

#if 0
static void
cmd_set_system(void)
{
	int rv;
	char prompt[64];
	char *guid;
	uint retries = min_retries;

	if (pin == NULL) {
		guid = buf_to_hex(selk->pt_guid, 4, B_FALSE);
		snprintf(prompt, 64, "Enter PIV PIN for token %s: ", guid);
		do {
			pin = getpass(prompt);
		} while (pin == NULL && errno == EINTR);
		if (pin == NULL && errno == ENXIO) {
			fprintf(stderr, "error: a PIN code is required to "
			    "unlock token %s\n", guid);
			exit(4);
		} else if (pin == NULL) {
			perror("getpass");
			exit(3);
		}
		pin = strdup(pin);
		free(guid);
	}

	VERIFY0(piv_txn_begin(selk));
	assert_select(selk);
#if 0
	rv = piv_system_token_set(selk, pin, &retries);
#endif
	piv_txn_end(selk);

	if (rv == EACCES) {
		if (retries == 0) {
			fprintf(stderr, "error: token is locked due to too "
			    "many invalid PIN code entries\n");
			exit(10);
		}
		fprintf(stderr, "error: invalid PIN code (%d attempts "
		    "remaining)\n", retries);
		exit(4);
	} else if (rv == EAGAIN) {
		fprintf(stderr, "error: PIN code only has %d retries "
		    "remaining, refusing to attempt unlock\n", retries);
		exit(5);
	} else if (rv != 0) {
		fprintf(stderr, "error: failed to set system token (rv = %d)\n",
		    rv);
		exit(1);
	}

	exit(0);
}
#endif

static errf_t *
cmd_change_pin(enum piv_pin pintype)
{
	errf_t *err;
	char prompt[64];
	char *p, *newpin, *guidhex;
	const char *charType = "digits";
	if (piv_token_is_ykpiv(selk))
		charType = "characters";

	guidhex = piv_token_shortid(selk);

	if (pin == NULL) {
		snprintf(prompt, 64, "Enter current %s (%s): ",
		    pin_type_to_name(pintype), guidhex);
		do {
			p = getpass(prompt);
		} while (p == NULL && errno == EINTR);
		if (p == NULL) {
			err = errfno("getpass", errno, "");
			return (err);
		}
		pin = strdup(p);
	}
again:
	snprintf(prompt, 64, "Enter new %s (%s): ",
	    pin_type_to_name(pintype), guidhex);
	do {
		p = getpass(prompt);
	} while (p == NULL && errno == EINTR);
	if (p == NULL) {
		err = errfno("getpass", errno, "");
		return (err);
	}
	if (strlen(p) < 6 || strlen(p) > 8) {
		warnx("PIN must be 6-8 %s", charType);
		goto again;
	}
	newpin = strdup(p);
	snprintf(prompt, 64, "Confirm new %s (%s): ",
	    pin_type_to_name(pintype), guidhex);
	do {
		p = getpass(prompt);
	} while (p == NULL && errno == EINTR);
	if (p == NULL) {
		err = errfno("getpass", errno, "");
		return (err);
	}
	if (strcmp(p, newpin) != 0) {
		warnx("PINs do not match");
		goto again;
	}
	free(guidhex);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_change_pin(selk, pintype, pin, newpin);
	piv_txn_end(selk);

	if (errf_caused_by(err, "PermissionError")) {
		err = funcerrf(err, "current PIN was incorrect; PIN "
		    "change attempt failed");
		return (err);
	} else if (err) {
		err = funcerrf(err, "failed to set new PIN");
		return (err);
	}

	return (ERRF_OK);
}

static errf_t *
cmd_reset_pin(void)
{
	errf_t *err;
	char prompt[64];
	char *p, *newpin, *guidhex;
	const char *charType = "digits";
	if (piv_token_is_ykpiv(selk))
		charType = "characters";

	guidhex = piv_token_shortid(selk);
	snprintf(prompt, 64, "Enter PUK (%s): ", guidhex);
	do {
		p = getpass(prompt);
	} while (p == NULL && errno == EINTR);
	if (p == NULL) {
		err = errfno("getpass", errno, "");
		return (err);
	}
	pin = strdup(p);
again:
	snprintf(prompt, 64, "Enter new PIV PIN (%s): ", guidhex);
	do {
		p = getpass(prompt);
	} while (p == NULL && errno == EINTR);
	if (p == NULL) {
		err = errfno("getpass", errno, "");
		return (err);
	}
	if (strlen(p) < 6 || strlen(p) > 8) {
		warnx("PIN must be 6-8 %s", charType);
		goto again;
	}
	newpin = strdup(p);
	snprintf(prompt, 64, "Confirm new PIV PIN (%s): ", guidhex);
	do {
		p = getpass(prompt);
	} while (p == NULL && errno == EINTR);
	if (p == NULL) {
		err = errfno("getpass", errno, "");
		return (err);
	}
	if (strcmp(p, newpin) != 0) {
		warnx("PINs do not match");
		goto again;
	}
	free(guidhex);

	if ((err = piv_txn_begin(selk)))
		errfx(1, err, "failed to open transaction");
	assert_select(selk);
	err = piv_reset_pin(selk, PIV_PIN, pin, newpin);
	piv_txn_end(selk);

	if (errf_caused_by(err, "PermissionError")) {
		err = funcerrf(err, "PUK was incorrect; PIN reset "
		    "attempt failed");
		return (err);
	} else if (err) {
		err = funcerrf(err, "failed to set new PIN");
		return (err);
	}

	return (ERRF_OK);
}

static errf_t *
selfsign_slot(uint slotid, enum piv_alg alg, struct sshkey *pub)
{
	int rv;
	errf_t *err;
	X509 *cert;
	EVP_PKEY *pkey;
	X509_NAME *subj;
	const char *ku, *basic;
	char *name;
	enum sshdigest_types wantalg, hashalg;
	int nid;
	ASN1_TYPE null_parameter;
	uint8_t *tbs = NULL, *sig, *cdata = NULL;
	size_t tbslen, siglen, cdlen;
	uint flags;
	uint i;
	BIGNUM *serial;
	ASN1_INTEGER *serial_asn1;
	X509_EXTENSION *ext;
	X509V3_CTX x509ctx;
	const char *guidhex;

	guidhex = piv_token_guid_hex(selk);

	switch (slotid) {
	case 0x9A:
		name = "piv-auth";
		basic = "critical,CA:FALSE";
		ku = "critical,digitalSignature,nonRepudiation";
		break;
	case 0x9C:
		name = "piv-sign";
		basic = "critical,CA:TRUE";
		ku = "critical,digitalSignature,nonRepudiation,"
		    "keyCertSign,cRLSign";
		break;
	case 0x9D:
		name = "piv-key-mgmt";
		basic = "critical,CA:FALSE";
		ku = "critical,keyAgreement,keyEncipherment,dataEncipherment";
		break;
	case 0x9E:
		name = "piv-card-auth";
		basic = "critical,CA:FALSE";
		ku = "critical,digitalSignature,nonRepudiation";
		break;
	case 0x82:
	case 0x83:
	case 0x84:
	case 0x85:
	case 0x86:
	case 0x87:
	case 0x88:
	case 0x89:
	case 0x8A:
	case 0x8B:
	case 0x8C:
	case 0x8D:
	case 0x8E:
	case 0x8F:
	case 0x90:
	case 0x91:
	case 0x92:
	case 0x93:
	case 0x94:
	case 0x95:
		name = calloc(1, 64);
		snprintf(name, 64, "piv-retired-%u", slotid - 0x81);
		basic = "critical,CA:FALSE";
		ku = "critical,digitalSignature,nonRepudiation";
		if (slotid - 0x82 > piv_token_keyhistory_oncard(selk)) {
			err = funcerrf(NULL, "next available key history "
			    "slot is %02X (must be used in order)",
			    0x82 + piv_token_keyhistory_oncard(selk));
			return (err);
		}
		break;
	default:
		err = funcerrf(NULL, "PIV slot %02X cannot be "
		    "used for asymmetric crypto\n", slotid);
		return (err);
	}

	pkey = EVP_PKEY_new();
	VERIFY(pkey != NULL);
	if (pub->type == KEY_RSA) {
		RSA *copy = RSA_new();
		VERIFY(copy != NULL);
		copy->e = BN_dup(pub->rsa->e);
		VERIFY(copy->e != NULL);
		copy->n = BN_dup(pub->rsa->n);
		VERIFY(copy->n != NULL);
		rv = EVP_PKEY_assign_RSA(pkey, copy);
		VERIFY(rv == 1);
		nid = NID_sha256WithRSAEncryption;
		wantalg = SSH_DIGEST_SHA256;
	} else if (pub->type == KEY_ECDSA) {
		boolean_t haveSha256 = B_FALSE;
		boolean_t haveSha1 = B_FALSE;

		EC_KEY *copy = EC_KEY_dup(pub->ecdsa);
		rv = EVP_PKEY_assign_EC_KEY(pkey, copy);
		VERIFY(rv == 1);

		for (i = 0; i < piv_token_nalgs(selk); ++i) {
			enum piv_alg alg = piv_token_alg(selk, i);
			if (alg == PIV_ALG_ECCP256_SHA256) {
				haveSha256 = B_TRUE;
			} else if (alg == PIV_ALG_ECCP256_SHA1) {
				haveSha1 = B_TRUE;
			}
		}
		if (haveSha1 && !haveSha256) {
			nid = NID_ecdsa_with_SHA1;
			wantalg = SSH_DIGEST_SHA1;
		} else {
			nid = NID_ecdsa_with_SHA256;
			wantalg = SSH_DIGEST_SHA256;
		}
	} else {
		return (funcerrf(NULL, "invalid key type"));
	}

	serial = BN_new();
	serial_asn1 = ASN1_INTEGER_new();
	VERIFY(serial != NULL);
	VERIFY(BN_pseudo_rand(serial, 64, 0, 0) == 1);
	VERIFY(BN_to_ASN1_INTEGER(serial, serial_asn1) != NULL);

	cert = X509_new();
	VERIFY(cert != NULL);
	VERIFY(X509_set_version(cert, 2) == 1);
	VERIFY(X509_set_serialNumber(cert, serial_asn1) == 1);
	VERIFY(X509_gmtime_adj(X509_get_notBefore(cert), 0) != NULL);
	VERIFY(X509_gmtime_adj(X509_get_notAfter(cert), 315360000L) != NULL);

	subj = X509_NAME_new();
	VERIFY(subj != NULL);
	if (cn == NULL) {
		VERIFY(X509_NAME_add_entry_by_NID(subj, NID_title, MBSTRING_ASC,
		    (unsigned char *)name, -1, -1, 0) == 1);
		VERIFY(X509_NAME_add_entry_by_NID(subj, NID_commonName,
		    MBSTRING_ASC, (unsigned char *)guidhex, -1, -1, 0) == 1);
	} else {
		VERIFY(X509_NAME_add_entry_by_NID(subj, NID_commonName,
		    MBSTRING_ASC, (unsigned char *)cn, -1, -1, 0) == 1);
	}
	/*VERIFY(X509_NAME_add_entry_by_NID(subj, NID_organizationalUnitName,
	    MBSTRING_ASC, (unsigned char *)"tokens", -1, -1, 0) == 1);
	VERIFY(X509_NAME_add_entry_by_NID(subj, NID_organizationName,
	    MBSTRING_ASC, (unsigned char *)"triton", -1, -1, 0) == 1);*/
	VERIFY(X509_set_subject_name(cert, subj) == 1);
	VERIFY(X509_set_issuer_name(cert, subj) == 1);

	X509V3_set_ctx_nodb(&x509ctx);
	X509V3_set_ctx(&x509ctx, cert, cert, NULL, NULL, 0);

	ext = X509V3_EXT_conf_nid(NULL, &x509ctx, NID_basic_constraints,
	    (char *)basic);
	VERIFY(ext != NULL);
	X509_add_ext(cert, ext, -1);
	X509_EXTENSION_free(ext);

	ext = X509V3_EXT_conf_nid(NULL, &x509ctx, NID_key_usage, (char *)ku);
	VERIFY(ext != NULL);
	X509_add_ext(cert, ext, -1);
	X509_EXTENSION_free(ext);

	VERIFY(X509_set_pubkey(cert, pkey) == 1);

	cert->sig_alg->algorithm = OBJ_nid2obj(nid);
	cert->cert_info->signature->algorithm = cert->sig_alg->algorithm;
	if (pub->type == KEY_RSA) {
		bzero(&null_parameter, sizeof (null_parameter));
		null_parameter.type = V_ASN1_NULL;
		null_parameter.value.ptr = NULL;
		cert->sig_alg->parameter = &null_parameter;
		cert->cert_info->signature->parameter = &null_parameter;
	}

	cert->cert_info->enc.modified = 1;
	rv = i2d_X509_CINF(cert->cert_info, &tbs);
	if (tbs == NULL || rv <= 0) {
		make_sslerrf(err, "i2d_X509_CINF", "generating cert");
		err = funcerrf(err, "failed to generate new cert");
		return (err);
	}
	tbslen = (size_t)rv;

	hashalg = wantalg;

	assert_pin(selk, B_FALSE);

signagain:
	err = piv_sign(selk, override, tbs, tbslen, &hashalg, &sig, &siglen);

	if (errf_caused_by(err, "PermissionError")) {
		assert_pin(selk, B_TRUE);
		goto signagain;
	} else if (err) {
		err = funcerrf(err, "failed to sign cert with key");
		return (err);
	}

	if (hashalg != wantalg) {
		err = funcerrf(NULL, "card could not sign with the "
		    "requested hash algorithm");
		return (err);
	}

	M_ASN1_BIT_STRING_set(cert->signature, sig, siglen);
	cert->signature->flags = ASN1_STRING_FLAG_BITS_LEFT;

	rv = i2d_X509(cert, &cdata);
	if (cdata == NULL || rv <= 0) {
		make_sslerrf(err, "i2d_X509", "generating cert");
		err = errf("generate", err, "failed to generate signed cert");
		return (err);
	}
	cdlen = (size_t)rv;

	flags = PIV_COMP_NONE;
	err = piv_write_cert(selk, slotid, cdata, cdlen, flags);

	if (err == ERRF_OK && slotid >= 0x82 && slotid <= 0x95 &&
	    piv_token_keyhistory_oncard(selk) <= slotid - 0x82) {
		uint oncard, offcard;
		const char *url;

		oncard = piv_token_keyhistory_oncard(selk);
		offcard = piv_token_keyhistory_offcard(selk);
		url = piv_token_offcard_url(selk);

		++oncard;

		err = piv_write_keyhistory(selk, oncard, offcard, url);

		if (err) {
			warnfx(err, "failed to update key "
			    "history object with new cert, trying to "
			    "continue anyway...");
			err = ERRF_OK;
		}
	}

	if (err) {
		err = errf("generate", err, "failed to write new cert");
		return (err);
	}

	return (NULL);
}

static errf_t *
cmd_import(uint slotid)
{
	errf_t *err;
	struct sshkey *pub = NULL, *priv = NULL;
	char *comment;
	char *pass;
	uint8_t *rbuf;
	struct sshbuf *buf;
	size_t boff;
	int rv;
	enum piv_alg alg = PIV_ALG_RSA1024;

	rbuf = read_stdin(16384, &boff);
	VERIFY(rbuf != NULL);

	buf = sshbuf_from(rbuf, boff);
	VERIFY(buf != NULL);

	rv = sshkey_parse_private_fileblob(buf, "", &priv, &comment);
	if (rv == SSH_ERR_KEY_WRONG_PASSPHRASE) {
		do {
			pass = getpass("Enter passphrase for key: ");
		} while (pass == NULL && errno == EINTR);
		if ((pass == NULL && errno == ENXIO) || strlen(pass) < 1) {
			errx(EXIT_PIN, "a passphrase is required to unlock "
			    "the given public key");
		}
		rv = sshkey_parse_private_fileblob(buf, pass, &priv, &comment);
	}
	if (rv != 0) {
		err = funcerrf(ssherrf("sshkey_parse_private_fileblob", rv),
		    "failed to parse key input");
		return (err);
	}
	sshbuf_free(buf);
	buf = NULL;
	free(rbuf);
	rbuf = NULL;

	if ((rv = sshkey_demote(priv, &pub))) {
		err = funcerrf(ssherrf("sshkey_demote", rv),
		    "failed to get public key from private");
		return (err);
	}

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_auth_admin(selk, admin_key, 24);
	if (err == ERRF_OK) {
		err = ykpiv_import(selk, slotid, priv, pinpolicy, touchpolicy);
	}

	if (err) {
		piv_txn_end(selk);
		err = funcerrf(err, "failed to import key");
		return (err);
	}

	switch (pub->type) {
	case KEY_RSA:
		switch (sshkey_size(pub)) {
		case 1024:
			alg = PIV_ALG_RSA1024;
			break;
		case 2048:
			alg = PIV_ALG_RSA2048;
			break;
		}
		break;
	case KEY_ECDSA:
		switch (sshkey_size(pub)) {
		case 256:
			alg = PIV_ALG_ECCP256;
			break;
		case 384:
			alg = PIV_ALG_ECCP384;
			break;
		}
		break;
	}

	override = piv_force_slot(selk, slotid, alg);
	err = selfsign_slot(slotid, alg, pub);
	piv_txn_end(selk);

	if (err) {
		err = funcerrf(err, "cert generation failed");
		return (err);
	}

	return (ERRF_OK);
}

static errf_t *
cmd_generate(uint slotid, enum piv_alg alg)
{
	errf_t *err;
	struct sshkey *pub = NULL;
	int rv;

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_auth_admin(selk, admin_key, 24);
	if (err == ERRF_OK) {
		if (pinpolicy == YKPIV_PIN_DEFAULT &&
		    touchpolicy == YKPIV_TOUCH_DEFAULT) {
			err = piv_generate(selk, slotid, alg, &pub);
		} else {
			err = ykpiv_generate(selk, slotid, alg, pinpolicy,
			    touchpolicy, &pub);
		}
	}

	if (err) {
		piv_txn_end(selk);
		err = funcerrf(err, "key generation failed");
		return (err);
	}

	err = selfsign_slot(slotid, alg, pub);
	piv_txn_end(selk);

	if (err) {
		err = funcerrf(err, "key generation failed");
		return (err);
	}

	rv = sshkey_write(pub, stdout);
	if (rv != 0) {
		err = errf("generate", ssherrf("sshkey_write", rv),
		    "failed to write public key to stdout");
		return (err);
	}
	fprintf(stdout, " PIV_slot_%02X@%s\n", slotid,
	    piv_token_guid_hex(selk));
	return (ERRF_OK);
}

static errf_t *
cmd_attest(uint slotid)
{
	struct piv_slot *slot = NULL;
	uint8_t *cert = NULL, *chain = NULL, *ptr;
	size_t certlen, chainlen, len;
	struct tlv_state *tlv;
	X509 *x509;
	errf_t *err;
	uint tag;

	assert_slotid(slotid);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_read_cert(selk, slotid);
	if (err == ERRF_OK) {
		slot = piv_get_slot(selk, slotid);
		VERIFY(slot != NULL);
		err = ykpiv_attest(selk, slot, &cert, &certlen);
		if (err == ERRF_OK) {
			err = piv_read_file(selk, PIV_TAG_CERT_YK_ATTESTATION,
			    &chain, &chainlen);
		}
	}
	piv_txn_end(selk);

	if (err != ERRF_OK)
		goto error;

	ptr = cert;
	x509 = d2i_X509(NULL, (const uint8_t **)&ptr, certlen);
	if (x509 == NULL) {
		make_sslerrf(err, "d2i_X509", "parsing attestation cert "
		    "for slot %02x", piv_slot_id(slot));
		goto error;
	}
	PEM_write_X509(stdout, x509);
	X509_free(x509);

	ptr = NULL;
	len = 0;
	tlv = tlv_init(chain, 0, chainlen);
	if ((err = tlv_read_tag(tlv, &tag)))
		goto error;
	if (tag != 0x70) {
		err = errf("PIVTagError", NULL,
		    "Got TLV tag 0x%x instead of 0x70", tag);
		goto error;
	}
	ptr = tlv_ptr(tlv);
	len = tlv_rem(tlv);

	x509 = d2i_X509(NULL, (const uint8_t **)&ptr, len);
	if (x509 == NULL) {
		make_sslerrf(err, "d2i_X509", "parsing attestation device cert");
		goto error;
	}
	PEM_write_X509(stdout, x509);
	X509_free(x509);

	tlv_skip(tlv);
	tlv_free(tlv);

	free(cert);
	piv_file_data_free(chain, chainlen);
	return (ERRF_OK);
error:
	err = funcerrf(err, "attestation failed");
	return (err);
}

static errf_t *
cmd_pubkey(uint slotid)
{
	struct piv_slot *cert;
	errf_t *err;
	int rv;

	assert_slotid(slotid);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_read_cert(selk, slotid);
	piv_txn_end(selk);

	cert = piv_get_slot(selk, slotid);

	if (cert == NULL && errf_caused_by(err, "NotFoundError")) {
		err = funcerrf(err, "PIV slot %02X has no key present",
		    slotid);
		return (err);
	} else if (cert == NULL) {
		err = funcerrf(err, "failed to read cert in slot %02X",
		    slotid);
		return (err);
	}

	rv = sshkey_write(piv_slot_pubkey(cert), stdout);
	if (rv != 0) {
		err = funcerrf(ssherrf("sshkey_write", rv),
		    "failed to write public key to stdout");
		return (err);
	}
	fprintf(stdout, " PIV_slot_%02X@%s \"%s\"\n", slotid,
	    piv_token_guid_hex(selk), piv_slot_subject(cert));
	return (ERRF_OK);
}

static errf_t *
cmd_cert(uint slotid)
{
	struct piv_slot *cert;
	errf_t *err;

	assert_slotid(slotid);

	if ((err = piv_txn_begin(selk)))
		errfx(1, err, "failed to open transaction");
	assert_select(selk);
	err = piv_read_cert(selk, slotid);
	piv_txn_end(selk);

	cert = piv_get_slot(selk, slotid);

	if (cert == NULL || err) {
		err = funcerrf(err, "failed to read cert in slot %02X", slotid);
		return (err);
	}

	VERIFY(i2d_X509_fp(stdout, piv_slot_cert(cert)) == 1);

	return (ERRF_OK);
}

static errf_t *
cmd_sign(uint slotid)
{
	struct piv_slot *cert;
	uint8_t *buf, *sig;
	enum sshdigest_types hashalg;
	size_t inplen, siglen;
	errf_t *err = ERRF_OK;

	assert_slotid(slotid);

	if (override == NULL) {
		if ((err = piv_txn_begin(selk)))
			return (err);
		assert_select(selk);
		err = piv_read_cert(selk, slotid);
		piv_txn_end(selk);

		cert = piv_get_slot(selk, slotid);
	} else {
		cert = override;
	}

	if (cert == NULL || err) {
		err = funcerrf(err, "failed to read cert for signing key in "
		    "slot %02X", slotid);
		return (err);
	}

	buf = read_stdin(16384, &inplen);
	assert(buf != NULL);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	assert_pin(selk, B_FALSE);
again:
	hashalg = 0;
	err = piv_sign(selk, cert, buf, inplen, &hashalg, &sig, &siglen);
	if (errf_caused_by(err, "PermissionError")) {
		assert_pin(selk, B_TRUE);
		goto again;
	}
	piv_txn_end(selk);
	if (err) {
		err = funcerrf(err, "failed to sign data");
		return (err);
	}

	fwrite(sig, 1, siglen, stdout);
	free(sig);
	free(buf);

	return (ERRF_OK);
}

static errf_t *
cmd_box(uint slotid)
{
	struct piv_slot *slot = NULL;
	struct piv_ecdh_box *box;
	errf_t *err;
	size_t len;
	uint8_t *buf;

	if (slotid != 0 || opubkey == NULL) {
		if ((err = piv_txn_begin(selk)))
			return (err);
		assert_select(selk);
		err = piv_read_cert(selk, slotid);
		piv_txn_end(selk);
		if (err) {
			err = funcerrf(err, "while reading cert for slot "
			    "%02X", slotid);
			return (err);
		}

		slot = piv_get_slot(selk, slotid);
		VERIFY3P(slot, !=, NULL);
	}

	box = piv_box_new();
	VERIFY3P(box, !=, NULL);

	buf = read_stdin(8192, &len);
	assert(buf != NULL);
	VERIFY3U(len, >, 0);
	VERIFY0(piv_box_set_data(box, buf, len));
	explicit_bzero(buf, len);
	free(buf);

	if (opubkey == NULL) {
		err = piv_box_seal(selk, slot, box);
	} else {
		err = piv_box_seal_offline(opubkey, box);
	}
	if (err) {
		if (slotid != 0) {
			err = errf("box", err, "failed sealing new box to key "
			    "in slot %02x", slotid);
		} else {
			err = errf("box", err, "failed sealing to given pubkey");
		}
		return (err);
	}

	VERIFY0(piv_box_to_binary(box, &buf, &len));
	piv_box_free(box);

	fwrite(buf, 1, len, stdout);
	explicit_bzero(buf, len);
	free(buf);

	return (ERRF_OK);
}

static errf_t *
cmd_unbox(void)
{
	struct piv_token *tk;
	struct piv_slot *sl;
	struct piv_ecdh_box *box;
	errf_t *err;
	size_t len;
	uint8_t *buf;

	buf = read_stdin(8192, &len);
	assert(buf != NULL);
	VERIFY3U(len, >, 0);

	if ((err = piv_box_from_binary(buf, len, &box)))
		return (err);
	free(buf);

	if (!piv_box_has_guidslot(box)) {
		err = funcerrf(NULL, "box has no hardware GUID + slot "
		    "information; can't be opened by pivy-tool");
		return (err);
	}

	err = piv_find(ctx, piv_box_guid(box), GUID_LEN, &tk);
	if (err)
		return (err);
	ks = (selk = tk);
	err = piv_box_find_token(ks, box, &tk, &sl);
	if (errf_caused_by(err, "NotFoundError")) {
		err = funcerrf(err, "no token found on system that can "
		    "unlock this box");
		return (err);
	} else if (err) {
		return (err);
	}

	if ((err = piv_txn_begin(tk)))
		return (err);
	assert_select(tk);
	assert_pin(tk, B_FALSE);
again:
	err = piv_box_open(tk, sl, box);
	if (errf_caused_by(err, "PermissionError")) {
		assert_pin(tk, B_TRUE);
		goto again;
	}
	piv_txn_end(tk);

	if (err) {
		return (funcerrf(err, "failed to open box"));
	}

	if ((err = piv_box_take_data(box, &buf, &len))) {
		explicit_bzero(buf, len);
		free(buf);
		return (err);
	}

	fwrite(buf, 1, len, stdout);
	explicit_bzero(buf, len);
	free(buf);

	return (ERRF_OK);
}


struct sgdebugbuf {
	uint8_t sb_id;
	uint8_t sb_flags;
	uint16_t sb_size;
	uint16_t sb_offset;
	uint16_t sb_len;
} __attribute__((packed));
struct sgdebugdata {
	uint16_t sg_buf;
	uint16_t sg_off;
	struct sgdebugbuf sg_bufs[1];
} __attribute__((packed));

static errf_t *
cmd_sgdebug(void)
{
	struct apdu *apdu;
	errf_t *err;

	apdu = piv_apdu_make(CLA_ISO, 0xE0, 0x00, 0x00);
	VERIFY(apdu != NULL);

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_apdu_transceive_chain(selk, apdu);
	piv_txn_end(selk);

	if (err) {
		err = errf("sgdebug", err, "failed to fetch debug info");
		return (err);
	}

	const uint8_t *reply;
	size_t len;
	reply = piv_apdu_get_reply(apdu, &len);

	struct sgdebugdata *data = (struct sgdebugdata *)reply;
	struct sgdebugbuf *buf;
	data->sg_buf = be16toh(data->sg_buf);
	data->sg_off = be16toh(data->sg_off);
	printf("== SGList debug data ==\n");
	printf("current position = %d + 0x%04x\n", data->sg_buf, data->sg_off);
	buf = data->sg_bufs;
	while ((char *)buf - (char *)data < len) {
		buf->sb_size = be16toh(buf->sb_size);
		buf->sb_offset = be16toh(buf->sb_offset);
		buf->sb_len = be16toh(buf->sb_len);
		printf("buf %-3d: ", buf->sb_id);
		if (buf->sb_flags & 0x02)
			printf("transient ");
		if (buf->sb_flags & 0x01)
			printf("dynamic ");
		printf("size=%04x offset=%04x len=%04x\n",
		    buf->sb_size, buf->sb_offset, buf->sb_len);
		++buf;
	}

	piv_apdu_free(apdu);

	return (ERRF_OK);
}

static errf_t *
cmd_box_info(void)
{
	struct piv_ecdh_box *box;
	size_t len;
	uint8_t *buf;
	char *hex;
	errf_t *err;

	buf = read_stdin(8192, &len);
	assert(buf != NULL);
	VERIFY3U(len, >, 0);

	if ((err = piv_box_from_binary(buf, len, &box)))
		return (err);
	free(buf);

	printf("version:      %u\n", piv_box_version(box));

	if (piv_box_has_guidslot(box)) {
		printf("type:         hardware (has guid + slot)\n");
		hex = buf_to_hex(piv_box_guid(box), 16, B_FALSE);
		printf("guid:         %s\n", hex);
		free(hex);
		printf("slot:         %02X\n", piv_box_slot(box));
	} else {
		printf("type:         virtual (no guid or slot)\n");
	}

	printf("pubkey:       ");
	VERIFY0(sshkey_write(piv_box_pubkey(box), stdout));
	printf("\n");

	printf("ephem_pubkey: ");
	VERIFY0(sshkey_write(piv_box_ephem_pubkey(box), stdout));
	printf("\n");

	printf("cipher:       %s\n", piv_box_cipher(box));
	printf("kdf:          %s\n", piv_box_kdf(box));
	printf("encsize:      %zu bytes\n", piv_box_encsize(box));
	printf("nonce:        %zu bytes\n", piv_box_nonce_size(box));

	return (ERRF_OK);
}

static errf_t *
cmd_auth(uint slotid)
{
	struct piv_slot *cert;
	struct sshkey *pubkey;
	uint8_t *buf;
	char *ptr;
	size_t boff;
	errf_t *err = NULL;
	int rv;

	switch (slotid) {
	case 0x9A:
	case 0x9C:
	case 0x9D:
	case 0x9E:
		break;
	default:
		if (slotid >= 0x82 && slotid <= 0x95)
			break;
		err = funcerrf(NULL, "PIV slot %02X cannot be "
		    "used for signing", slotid);
		return (err);
	}

	if (override == NULL) {
		if ((err = piv_txn_begin(selk)))
			return (err);
		assert_select(selk);
		err = piv_read_cert(selk, slotid);
		piv_txn_end(selk);

		cert = piv_get_slot(selk, slotid);
	} else {
		cert = override;
	}

	if (cert == NULL || err) {
		err = funcerrf(err, "failed to read cert for signing key");
		return (err);
	}

	buf = read_stdin(16384, &boff);
	assert(buf != NULL);
	buf[boff] = 0;

	pubkey = sshkey_new(piv_slot_pubkey(cert)->type);
	VERIFY(pubkey != NULL);
	ptr = (char *)buf;
	rv = sshkey_read(pubkey, &ptr);
	if (rv != 0) {
		err = funcerrf(ssherrf("sshkey_read", rv),
		    "failed to parse public key input");
		return (err);
	}

	if ((err = piv_txn_begin(selk)))
		errfx(1, err, "failed to open transaction");
	assert_select(selk);
	assert_pin(selk, B_FALSE);
again:
	err = piv_auth_key(selk, cert, pubkey);
	if (errf_caused_by(err, "PermissionError")) {
		assert_pin(selk, B_TRUE);
		goto again;
	}
	piv_txn_end(selk);
	if (err) {
		err = funcerrf(err, "key authentication failed");
		return (err);
	}

	return (ERRF_OK);
}

static errf_t *
cmd_ecdh(uint slotid)
{
	struct piv_slot *cert;
	struct sshkey *pubkey;
	uint8_t *buf, *secret;
	char *ptr;
	size_t boff, seclen;
	errf_t *err = ERRF_OK;
	int rv;

	switch (slotid) {
	case 0x9A:
	case 0x9C:
	case 0x9D:
	case 0x9E:
		break;
	default:
		err = funcerrf(NULL, "PIV slot %02X cannot be used for ECDH",
		    slotid);
		return (err);
	}

	if (override == NULL) {
		if ((err = piv_txn_begin(selk)))
			return (err);
		assert_select(selk);
		err = piv_read_cert(selk, slotid);
		piv_txn_end(selk);

		cert = piv_get_slot(selk, slotid);
	} else {
		cert = override;
	}

	if (cert == NULL || err) {
		err = funcerrf(err, "failed to read cert in PIV slot %02X",
		    slotid);
		return (err);
	}

	switch (piv_slot_alg(cert)) {
	case PIV_ALG_ECCP256:
	case PIV_ALG_ECCP384:
		break;
	default:
		err = funcerrf(NULL, "PIV slot %02X does not contain an EC key",
		    slotid);
		return (err);
	}

	buf = read_stdin(8192, &boff);
	assert(buf != NULL);
	buf[boff] = 0;

	pubkey = sshkey_new(piv_slot_pubkey(cert)->type);
	assert(pubkey != NULL);
	ptr = (char *)buf;
	rv = sshkey_read(pubkey, &ptr);
	if (rv != 0) {
		err = errf("ecdh", ssherrf("sshkey_read", rv),
		    "failed to parse public key input");
		return (err);
	}

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	assert_pin(selk, B_FALSE);
again:
	err = piv_ecdh(selk, cert, pubkey, &secret, &seclen);
	if (errf_caused_by(err, "PermissionError")) {
		assert_pin(selk, B_TRUE);
		goto again;
	}
	piv_txn_end(selk);
	if (err) {
		err = funcerrf(err, "failed to compute ECDH");
		return (err);
	}

	fwrite(secret, 1, seclen, stdout);

	return (ERRF_OK);
}

static void
check_select_key(void)
{
	struct piv_token *t;
	errf_t *err;
	size_t len;

	if (guid_len == 0) {
		err = piv_enumerate(ctx, &t);
		if (err) {
			errfx(EXIT_IO_ERROR, err,
			    "failed to enumerate PIV tokens");
		}
		if (t == NULL) {
			errx(EXIT_NO_CARD, "no PIV cards/tokens found");
		}
		if (piv_token_next(t) != NULL) {
			errx(EXIT_NO_CARD, "multiple PIV cards "
			    "present and no system token set; you "
			    "must provide -g|--guid to select one");
		}
		selk = (ks = t);
		return;
	}

	len = guid_len;
	if (buf_is_zero(guid, guid_len))
		len = 0;

	err = piv_find(ctx, guid, len, &t);
	if (errf_caused_by(err, "DuplicateError"))
		errx(EXIT_NO_CARD, "GUID prefix specified is not unique");
	if (errf_caused_by(err, "NotFoundError")) {
		errx(EXIT_NO_CARD, "no PIV card present matching given "
		    "GUID");
	}
	if (err)
		errfx(EXIT_IO_ERROR, err, "while finding PIV token with GUID");
	selk = (ks = t);
}

static errf_t *
cmd_factory_reset(void)
{
	char *resp;
	errf_t *err;

	if (!piv_token_is_ykpiv(selk)) {
		err = funcerrf(NULL, "factory-reset command is only for "
		    "YubiKeys");
		return (err);
	}

	fprintf(stderr, "Resetting YubiKey %s (%s)\n",
	    piv_token_shortid(selk), piv_token_rdrname(selk));
	if (ykpiv_token_has_serial(selk)) {
		fprintf(stderr, "Serial #%u\n", ykpiv_token_serial(selk));
	}

	fprintf(stderr, "WARNING: this will completely reset the PIV applet "
	    "on this YubiKey, erasing all keys and certificates!\n");
	do {
		resp = getpass("Type 'YES' to continue: ");
	} while (resp == NULL && errno == EINTR);
	if (resp == NULL || strcmp(resp, "YES") != 0) {
		return (ERRF_OK);
	}

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = ykpiv_reset(selk);
	piv_txn_end(selk);

	if (err)
		return (err);
	return (ERRF_OK);
}

static errf_t *
cmd_setup(SCARDCONTEXT ctx)
{
	boolean_t usetouch = B_FALSE;
	errf_t *err;

	if (!piv_token_is_ykpiv(selk)) {
		err = funcerrf(NULL, "setup command is only for YubiKeys");
		return (err);
	}

	if (ykpiv_version_compare(selk, 4, 3, 0) == 1) {
		usetouch = B_TRUE;
	}

	if (!piv_token_has_chuid(selk)) {
		fprintf(stderr, "Initializing CCC and CHUID files...\n");
		if ((err = cmd_init())) {
			return (funcerrf(err,
			    "initializing CCC and CHUID files"));
		}
		piv_release(ks);
		selk = NULL;
		check_select_key();
	}

	touchpolicy = YKPIV_TOUCH_DEFAULT;
	pinpolicy = YKPIV_PIN_DEFAULT;
	pin = "123456";

	fprintf(stderr, "Generating standard keys...\n");

	if ((err = piv_txn_begin(selk)))
		return (err);
	assert_select(selk);
	err = piv_read_cert(selk, 0x9E);
	piv_txn_end(selk);

	if (err) {
		errf_free(err);
		override = piv_force_slot(selk, 0x9E, PIV_ALG_ECCP256);
		err = cmd_generate(piv_slot_id(override),
		    piv_slot_alg(override));
		if (err)
			return (err);
	}
	override = piv_force_slot(selk, 0x9A, PIV_ALG_ECCP256);
	if ((err = cmd_generate(piv_slot_id(override), piv_slot_alg(override))))
		return (err);

	override = piv_force_slot(selk, 0x9C, PIV_ALG_RSA2048);
	if ((err = cmd_generate(piv_slot_id(override), piv_slot_alg(override))))
		return (err);

	if (usetouch) {
		touchpolicy = YKPIV_TOUCH_CACHED;
		fprintf(stderr, "Using touch button confirmation for 9D key\n");
		fprintf(stderr, "Please touch YubiKey when it is flashing\n");
	}
again9d:
	override = piv_force_slot(selk, 0x9D, PIV_ALG_ECCP256);
	err = cmd_generate(piv_slot_id(override), piv_slot_alg(override));
	if (errf_caused_by(err, "ArgumentError") ||
	    errf_caused_by(err, "NotSupportedError") ||
	    errf_caused_by(err, "APDUError")) {
		touchpolicy = YKPIV_TOUCH_DEFAULT;
		usetouch = B_FALSE;
		goto again9d;
	}
	if (err)
		return (err);

	touchpolicy = YKPIV_TOUCH_DEFAULT;

	fprintf(stderr, "Changing PIN and PUK...\n");
	if ((err = cmd_change_pin(PIV_PIN)))
		return (err);
	pin = "12345678";
	if ((err = cmd_change_pin(PIV_PUK)))
		return (err);

	fprintf(stderr, "Generating final admin 3DES key...\n");
	uint8_t *admin_key = malloc(24);
	char *hex;
	VERIFY(admin_key != NULL);
	arc4random_buf(admin_key, 24);
	if (usetouch)
		touchpolicy = YKPIV_TOUCH_ALWAYS;
	hex = buf_to_hex(admin_key, 24, B_FALSE);
	printf("Admin 3DES key: %s\n", hex);
	fprintf(stderr, "This key is only needed to generate new slot keys or "
	    "change certificates in future. If you don't intend to do either "
	    "you can simply forget about this key and the YubiKey will be "
	    "sealed.\n");
	if ((err = cmd_set_admin(admin_key)))
		return (err);

	fprintf(stderr, "Done!\n");

	return (ERRF_OK);
}

#if defined(__sun)
const char *
_umem_debug_init()
{
	return ("guards");
}
#endif

void
usage(void)
{
	fprintf(stderr,
	    "usage: pivy-tool [options] <operation>\n"
	    "Available operations:\n"
	    "  list                   Lists PIV tokens present\n"
	    "  pubkey <slot>          Outputs a public key in SSH format\n"
	    "  cert <slot>            Outputs DER certificate from slot\n"
	    "\n"
	    "  init                   Writes GUID and card capabilities\n"
	    "                         (used to init a new Yubico PIV)\n"
	    "  setup                  Quick setup procedure for new YubiKey\n"
	    "                         (does init + generate + change-pin +\n"
	    "                         change-puk + set-admin)\n"
	    "  generate <slot>        Generate a new private key and a\n"
	    "                         self-signed cert\n"
	    "  import <slot>          Accept a SSH private key on stdin\n"
	    "                         and import it to a YubiKey (generates\n"
	    "                         a self-signed cert to go with it)\n"
	    "  change-pin             Changes the PIV PIN\n"
	    "  change-puk             Changes the PIV PUK\n"
	    "  reset-pin              Resets the PIN using the PUK\n"
	    "  factory-reset          Factory reset the PIV applet on a\n"
	    "                         YubiKey, once the PIN and PUK are both\n"
	    "                         locked (max retries used)\n"
	    "  set-admin <hex|@file>  Sets the admin 3DES key\n"
	    "\n"
	    "  sign <slot>            Signs data on stdin\n"
	    "  ecdh <slot>            Do ECDH with pubkey on stdin\n"
	    "  auth <slot>            Does a round-trip signature test to\n"
	    "                         verify that the pubkey on stdin\n"
	    "                         matches the one in the slot\n"
	    "  attest <slot>          (YubiKey only) Output attestation cert\n"
	    "                         and chain for a given slot.\n"
	    "\n"
	    "  box [slot]             Encrypts stdin data with an ECDH box\n"
	    "  unbox                  Decrypts stdin data with an ECDH box\n"
	    "                         Chooses token and slot automatically\n"
	    "  box-info               Prints metadata about a box from stdin\n"
	    "\n"
	    "General options:\n"
	    "  -g <hex>               GUID of the PIV token to use\n"
	    "                         (Required if >1 token on system)\n"
	    "  -P <code>              PIN code to authenticate with\n"
	    "                         (defaults to reading from terminal)\n"
	    "  -f                     Attempt to unlock with PIN code even\n"
	    "                         if there is only 1 attempt left before\n"
	    "                         card lock\n"
	    "  -K <hex|@file>         Provides the admin 3DES key to use for\n"
	    "                         auth to the card with admin ops (e.g.\n"
	    "                         generate or init)\n"
	    "  -d                     Output debug info to stderr\n"
	    "                         (use twice to include APDU trace)\n"
	    "\n"
	    "Options for 'list':\n"
	    "  -p                     Generate parseable output\n"
	    "\n"
	    "Options for 'generate':\n"
	    "  -a <algo>              Choose algorithm of new key\n"
	    "                         EC algos: eccp256, eccp384\n"
	    "                         RSA algos: rsa1024, rsa2048, rsa4096\n"
	    "  -n <cn>                Set a CN= attribute to be used on\n"
	    "                         the new slot's certificate\n"
	    "  -t <never|always|cached>\n"
	    "                         Set the touch policy. Only supported\n"
	    "                         with YubiKeys\n"
	    "  -i <never|always|once> Set the PIN policy. Only supported\n"
	    "                         with YubiKeys\n"
	    "\n"
	    "Options for 'box'/'unbox':\n"
	    "  -k <pubkey>            Use a public key for box operation\n"
	    "                         instead of a slot\n");
	exit(EXIT_BAD_ARGS);
}

/*const char *optstring =
    "d(debug)"
    "p(parseable)"
    "g:(guid)"
    "P:(pin)"
    "a:(algorithm)"
    "f(force)"
    "K:(admin-key)"
    "k:(key)";*/
const char *optstring = "dpg:P:a:fK:k:n:t:i:";

int
main(int argc, char *argv[])
{
	LONG rv;
	errf_t *err = ERRF_OK;
	extern char *optarg;
	extern int optind;
	int c;
	uint len;
	char *ptr;
	uint8_t *buf;
	uint d_level = 0;
	enum piv_alg overalg = 0;
	boolean_t hasover = B_FALSE;

	bunyan_init();
	bunyan_set_name("pivy-tool");

	while ((c = getopt(argc, argv, optstring)) != -1) {
		switch (c) {
		case 'd':
			bunyan_set_level(BNY_TRACE);
			if (++d_level > 1)
				piv_full_apdu_debug = B_TRUE;
			break;
		case 'K':
			if (strcmp(optarg, "default") == 0) {
				admin_key = DEFAULT_ADMIN_KEY;
			} else if (optarg[0] == '@') {
				buf = read_key_file(&optarg[1], &len);
				if (len > 24 && sniff_hex(buf, len)) {
					admin_key = parse_hex(
					    (const char *)buf, &len);
				} else {
					admin_key = buf;
				}
			} else {
				admin_key = parse_hex(optarg, &len);
			}
			if (len != 24) {
				errx(EXIT_BAD_ARGS, "admin key must be "
				    "24 bytes in length (%d given)", len);
			}
			break;
		case 'n':
			cn = optarg;
			break;
		case 'f':
			min_retries = 0;
			break;
		case 't':
			if (strcasecmp(optarg, "never") == 0) {
				touchpolicy = YKPIV_TOUCH_NEVER;
			} else if (strcasecmp(optarg, "always") == 0) {
				touchpolicy = YKPIV_TOUCH_ALWAYS;
			} else if (strcasecmp(optarg, "cached") == 0) {
				touchpolicy = YKPIV_TOUCH_CACHED;
			}
			break;
		case 'i':
			if (strcasecmp(optarg, "never") == 0) {
				pinpolicy = YKPIV_PIN_NEVER;
			} else if (strcasecmp(optarg, "always") == 0) {
				pinpolicy = YKPIV_PIN_ALWAYS;
			} else if (strcasecmp(optarg, "once") == 0) {
				pinpolicy = YKPIV_PIN_ONCE;
			}
			break;
		case 'a':
			hasover = B_TRUE;
			if (strcasecmp(optarg, "rsa1024") == 0) {
				overalg = PIV_ALG_RSA1024;
			} else if (strcasecmp(optarg, "rsa2048") == 0) {
				overalg = PIV_ALG_RSA2048;
			} else if (strcasecmp(optarg, "eccp256") == 0) {
				overalg = PIV_ALG_ECCP256;
			} else if (strcasecmp(optarg, "eccp384") == 0) {
				overalg = PIV_ALG_ECCP384;
			} else if (strcasecmp(optarg, "3des") == 0) {
				overalg = PIV_ALG_3DES;
			} else {
				errx(EXIT_BAD_ARGS, "invalid algorithm: '%s'",
				    optarg);
			}
			/* ps_slot will be set after we've parsed the slot */
			break;
		case 'g':
			guid = parse_hex(optarg, &len);
			guid_len = len;
			if (len > 16) {
				errx(EXIT_BAD_ARGS, "GUID must be <=16 bytes "
				    "(%d given)", len);
			}
			break;
		case 'P':
			pin = optarg;
			break;
		case 'p':
			parseable = B_TRUE;
			break;
		case 'k':
			opubkey = sshkey_new(KEY_UNSPEC);
			assert(opubkey != NULL);
			ptr = optarg;
			rv = sshkey_read(opubkey, &ptr);
			if (rv != 0) {
				errfx(EXIT_BAD_ARGS, ssherrf("sshkey_read",
				    rv), "failed to parse public key in -k");
			}
			break;
		}
	}

	if (optind >= argc) {
		warnx("operation required");
		usage();
	}

	const char *op = argv[optind++];

	rv = SCardEstablishContext(SCARD_SCOPE_SYSTEM, NULL, NULL, &ctx);
	if (rv != SCARD_S_SUCCESS) {
		errfx(EXIT_IO_ERROR, pcscerrf("SCardEstablishContext", rv),
		    "failed to initialise libpcsc");
	}

#if 0
	if (piv_system_token_find(ks, &sysk) != 0)
		sysk = NULL;
#endif

	if (strcmp(op, "list") == 0) {
		err = piv_enumerate(ctx, &ks);
		if (err)
			errfx(1, err, "failed to enumerate PIV tokens");
		if (optind < argc)
			usage();
		err = cmd_list();

	} else if (strcmp(op, "init") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_init();

#if 0
	} else if (strcmp(op, "set-system") == 0) {
		if (optind < argc) {
			fprintf(stderr, "error: too many arguments\n");
			usage();
		}
		check_select_key();
		cmd_set_system();
#endif

	} else if (strcmp(op, "change-pin") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_change_pin(piv_token_default_auth(selk));

	} else if (strcmp(op, "set-admin") == 0) {
		uint8_t *new_admin;

		if (optind >= argc)
			usage();

		if (strcmp(argv[optind], "default") == 0) {
			new_admin = (uint8_t *)DEFAULT_ADMIN_KEY;
		} else if (argv[optind][0] == '@') {
			buf = read_key_file(&argv[optind][1], &len);
			if (len > 24 && sniff_hex(buf, len)) {
				new_admin = parse_hex(
				    (const char *)buf, &len);
			} else {
				new_admin = buf;
			}
		} else {
			new_admin = parse_hex(argv[optind], &len);
		}

		if (++optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		if (len != 24) {
			errx(EXIT_BAD_ARGS, "admin key must be 24 bytes in "
			    "length (%d given)", len);
		}
		check_select_key();
		err = cmd_set_admin(new_admin);

	} else if (strcmp(op, "change-puk") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_change_pin(PIV_PUK);

	} else if (strcmp(op, "reset-pin") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_reset_pin();

	} else if (strcmp(op, "sign") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s", op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		if (hasover)
			override = piv_force_slot(selk, slotid, overalg);
		err = cmd_sign(slotid);

	} else if (strcmp(op, "pubkey") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		err = cmd_pubkey(slotid);

	} else if (strcmp(op, "attest") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		err = cmd_attest(slotid);

	} else if (strcmp(op, "setup") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_setup(ctx);

	} else if (strcmp(op, "factory-reset") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_factory_reset();

	} else if (strcmp(op, "cert") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		err = cmd_cert(slotid);

	} else if (strcmp(op, "ecdh") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		if (hasover)
			override = piv_force_slot(selk, slotid, overalg);
		err = cmd_ecdh(slotid);

	} else if (strcmp(op, "auth") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		if (hasover)
			override = piv_force_slot(selk, slotid, overalg);
		err = cmd_auth(slotid);

	} else if (strcmp(op, "box") == 0) {
		uint slotid;

		if (opubkey == NULL) {
			if (optind >= argc) {
				slotid = PIV_SLOT_KEY_MGMT;
			} else {
				slotid = strtol(argv[optind++], NULL, 16);
			}
			check_select_key();
		} else {
			slotid = 0;
		}

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		err = cmd_box(slotid);

	} else if (strcmp(op, "unbox") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		err = cmd_unbox();

	} else if (strcmp(op, "box-info") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		err = cmd_box_info();

	} else if (strcmp(op, "sgdebug") == 0) {
		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}
		check_select_key();
		err = cmd_sgdebug();

	} else if (strcmp(op, "generate") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		if (!hasover) {
			warnx("%s requires the -a (algorithm) option", op);
			usage();
		}

		check_select_key();
		if (hasover)
			override = piv_force_slot(selk, slotid, overalg);
		err = cmd_generate(slotid, overalg);

	} else if (strcmp(op, "import") == 0) {
		uint slotid;

		if (optind >= argc) {
			warnx("not enough arguments for %s (slot required)",
			    op);
			usage();
		}
		slotid = strtol(argv[optind++], NULL, 16);

		if (optind < argc) {
			warnx("too many arguments for %s", op);
			usage();
		}

		check_select_key();
		err = cmd_import(slotid);

	} else {
		warnx("invalid operation '%s'", op);
		usage();
	}

	if (err)
		errfx(1, err, "error occurred while executing '%s'", op);

	return (0);
}
