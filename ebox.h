/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * Copyright (c) 2018, Joyent Inc
 * Author: Alex Wilson <alex.wilson@joyent.com>
 */

#if !defined(_EBOX_H)
#define _EBOX_H

#include <stdint.h>
#include <assert.h>

#if defined(__APPLE__)
#include <PCSC/wintypes.h>
#include <PCSC/winscard.h>
#else
#include <wintypes.h>
#include <winscard.h>
#endif

#include <sys/types.h>
#include <sys/uio.h>

#include <openssl/x509.h>
#include <openssl/x509v3.h>

#include "errf.h"
#include "piv.h"
#include "libssh/digest.h"

enum ebox_type {
	EBOX_TEMPLATE = 0x01,
	EBOX_KEY = 0x02,
	EBOX_STREAM = 0x03
};

enum ebox_recov_tag {
	EBOX_RECOV_TOKEN = 0x01,
	EBOX_RECOV_KEY = 0x02
};

enum ebox_config_type {
	EBOX_PRIMARY = 0x01,
	EBOX_RECOVERY = 0x02
};

enum ebox_chaltype {
	CHAL_RECOVERY = 1,
	CHAL_VERIFY_AUDIT = 2,
};

struct ebox_tpl;
struct ebox_tpl_config;
struct ebox_tpl_part;
struct ebox;
struct ebox_config;
struct ebox_part;
struct ebox_challenge;
struct ebox_stream;
struct ebox_stream_chunk;

struct ebox_tpl *ebox_tpl_alloc(void);
void ebox_tpl_free(struct ebox_tpl *tpl);
uint ebox_tpl_version(const struct ebox_tpl *tpl);
void *ebox_tpl_private(const struct ebox_tpl *tpl);
void *ebox_tpl_alloc_private(struct ebox_tpl *tpl, size_t sz);
struct ebox_tpl *ebox_tpl_clone(struct ebox_tpl *tpl);
void ebox_tpl_add_config(struct ebox_tpl *tpl, struct ebox_tpl_config *config);
void ebox_tpl_remove_config(struct ebox_tpl *tpl, struct ebox_tpl_config *config);
struct ebox_tpl_config *ebox_tpl_next_config(const struct ebox_tpl *tpl,
    const struct ebox_tpl_config *prev);

struct ebox_tpl_config *ebox_tpl_config_alloc(enum ebox_config_type type);
void ebox_tpl_config_free(struct ebox_tpl_config *config);
void ebox_tpl_config_free_private(struct ebox_tpl_config *config);
void *ebox_tpl_config_private(const struct ebox_tpl_config *config);
void *ebox_tpl_config_alloc_private(struct ebox_tpl_config *config, size_t sz);
errf_t *ebox_tpl_config_set_n(struct ebox_tpl_config *config, uint n);
uint ebox_tpl_config_n(const struct ebox_tpl_config *config);
enum ebox_config_type ebox_tpl_config_type(
    const struct ebox_tpl_config *config);
void ebox_tpl_config_add_part(struct ebox_tpl_config *config,
    struct ebox_tpl_part *part);
void ebox_tpl_config_remove_part(struct ebox_tpl_config *config,
    struct ebox_tpl_part *part);
struct ebox_tpl_part *ebox_tpl_config_next_part(
    const struct ebox_tpl_config *config, const struct ebox_tpl_part *prev);

struct ebox_tpl_part *ebox_tpl_part_alloc(const uint8_t *guid, size_t guidlen,
    enum piv_slotid slot, struct sshkey *pubkey);
void ebox_tpl_part_free(struct ebox_tpl_part *part);
void ebox_tpl_part_set_name(struct ebox_tpl_part *part, const char *name);
void ebox_tpl_part_set_cak(struct ebox_tpl_part *part, struct sshkey *cak);
void *ebox_tpl_part_private(const struct ebox_tpl_part *part);
void *ebox_tpl_part_alloc_private(struct ebox_tpl_part *part, size_t sz);
void ebox_tpl_part_free_private(struct ebox_tpl_part *part);
const char *ebox_tpl_part_name(const struct ebox_tpl_part *part);
struct sshkey *ebox_tpl_part_pubkey(const struct ebox_tpl_part *part);
struct sshkey *ebox_tpl_part_cak(const struct ebox_tpl_part *part);
const uint8_t *ebox_tpl_part_guid(const struct ebox_tpl_part *part);
enum piv_slotid ebox_tpl_part_slot(const struct ebox_tpl_part *part);

errf_t *sshbuf_get_ebox_tpl(struct sshbuf *buf, struct ebox_tpl **tpl);
errf_t *sshbuf_put_ebox_tpl(struct sshbuf *buf, struct ebox_tpl *tpl);

uint ebox_version(const struct ebox *ebox);
enum ebox_type ebox_type(const struct ebox *ebox);
uint ebox_ephem_count(const struct ebox *ebox);
void ebox_free(struct ebox *box);

void *ebox_private(const struct ebox *ebox);
void *ebox_alloc_private(struct ebox *ebox, size_t sz);

struct ebox_tpl *ebox_tpl(const struct ebox *ebox);

struct ebox_config *ebox_next_config(const struct ebox *box,
    const struct ebox_config *prev);
struct ebox_part *ebox_config_next_part(const struct ebox_config *config,
    const struct ebox_part *prev);

struct ebox_tpl_config *ebox_config_tpl(const struct ebox_config *config);
struct ebox_tpl_part *ebox_part_tpl(const struct ebox_part *part);

void *ebox_config_private(const struct ebox_config *config);
void *ebox_config_alloc_private(struct ebox_config *config, size_t sz);

void *ebox_part_private(const struct ebox_part *part);
void *ebox_part_alloc_private(struct ebox_part *part, size_t sz);

struct piv_ecdh_box *ebox_part_box(const struct ebox_part *part);

errf_t *sshbuf_get_ebox(struct sshbuf *buf, struct ebox **box);
errf_t *sshbuf_put_ebox(struct sshbuf *buf, struct ebox *box);

void ebox_stream_free(struct ebox_stream *str);
void ebox_stream_chunk_free(struct ebox_stream_chunk *chunk);

/*
 * Creates a new ebox based on a given template, sealing up the provided key
 * and (optional) recovery token.
 */
errf_t *ebox_create(const struct ebox_tpl *tpl, const uint8_t *key,
    size_t keylen, const uint8_t *rtoken, size_t rtokenlen,
    struct ebox **pebox);

const char *ebox_cipher(const struct ebox *box);
const uint8_t *ebox_key(const struct ebox *box, size_t *len);
const uint8_t *ebox_recovery_token(const struct ebox *box, size_t *len);

/*
 * Generate a challenge for a given recovery config + part.
 *
 * The challenge can then be serialised using sshbuf_put_ebox_challenge() and
 * sent to the remote side. The "descfmt", ... arguments are given to vsnprintf
 * to create the "description" field for the challenge (displayed on the
 * remote end).
 *
 * Errors:
 *  - ENOMEM: description was too long for available space
 */
errf_t *ebox_gen_challenge(struct ebox_config *config, struct ebox_part *part,
    const char *descfmt, ...);
const struct ebox_challenge *ebox_part_challenge(const struct ebox_part *part);

void ebox_challenge_free(struct ebox_challenge *chal);

/*
 * Serializes an ebox challenge inside a piv_ecdh_box as a one-step process.
 *
 * The data written in the buf is ready to be transported to a remote machine.
 */
errf_t *sshbuf_put_ebox_challenge(struct sshbuf *buf,
    const struct ebox_challenge *chal);

/*
 * De-serializes an ebox challenge from inside a piv_ecdh_box. The piv_ecdh_box
 * must be already unsealed.
 */
errf_t *sshbuf_get_ebox_challenge(struct piv_ecdh_box *box,
    struct ebox_challenge **chal);

enum ebox_chaltype ebox_challenge_type(const struct ebox_challenge *chal);
uint ebox_challenge_id(const struct ebox_challenge *chal);
const char *ebox_challenge_desc(const struct ebox_challenge *chal);
const char *ebox_challenge_hostname(const struct ebox_challenge *chal);
uint64_t ebox_challenge_ctime(const struct ebox_challenge *chal);
const uint8_t *ebox_challenge_words(const struct ebox_challenge *chal,
    size_t *len);
struct sshkey *ebox_challenge_destkey(const struct ebox_challenge *chal);
struct piv_ecdh_box *ebox_challenge_box(const struct ebox_challenge *chal);


/*
 * Serializes a response to an ebox challenge inside a piv_ecdh_box as a
 * one-step process. The c_keybox on chal must be already unsealed.
 *
 * The data written in the buf is ready to be transported to the original
 * requesting machine.
 */
errf_t *sshbuf_put_ebox_challenge_response(struct sshbuf *buf,
    const struct ebox_challenge *chal);

/*
 * Process an incoming response to a recovery challenge for the given config.
 *
 * *ppart is set to point at the part that this response was from. Takes
 * ownership of respbox, and will free it.
 *
 * Errors:
 *  - EAGAIN: this challenge matched a part that is already unlocked
 */
errf_t *ebox_challenge_response(struct ebox_config *config,
    struct piv_ecdh_box *respbox, struct ebox_part **ppart);

/*
 * Unlock an ebox using a primary config.
 *
 * One of the primary config's part boxes must have been already unsealed
 * before calling this.
 *
 * Errors:
 *  - EINVAL: none of the part boxes were unsealed
 */
errf_t *ebox_unlock(struct ebox *ebox, struct ebox_config *config);

/*
 * Perform recovery on an ebox using a recovery config.
 *
 * N out of M of the parts on this config must have been processed with
 * ebox_challenge_response() before calling this.
 *
 * Errors:
 *  - EINVAL: insufficient number of parts available on this config that are
 *            ready for recovery
 *  - EAGAIN: the ebox is already unlocked or recovered
 *  - EBADF: the recovery box data was invalid or corrupt
 */
errf_t *ebox_recover(struct ebox *ebox, struct ebox_config *config);

errf_t *sshbuf_get_ebox_stream(struct sshbuf *buf, struct ebox_stream **str);
errf_t *sshbuf_put_ebox_stream(struct sshbuf *buf, struct ebox_stream *str);
errf_t *sshbuf_get_ebox_stream_chunk(struct sshbuf *buf,
    const struct ebox_stream *stream, struct ebox_stream_chunk **chunk);
errf_t *sshbuf_put_ebox_stream_chunk(struct sshbuf *buf,
    struct ebox_stream_chunk *chunk);

struct ebox *ebox_stream_ebox(const struct ebox_stream *str);
const char *ebox_stream_cipher(const struct ebox_stream *str);
const char *ebox_stream_mac(const struct ebox_stream *str);
size_t ebox_stream_chunk_size(const struct ebox_stream *str);
size_t ebox_stream_seek_offset(const struct ebox_stream *str, size_t offset);

errf_t *ebox_stream_new(const struct ebox_tpl *tpl, struct ebox_stream **str);
errf_t *ebox_stream_chunk_new(const struct ebox_stream *str, const void *data,
    size_t size, size_t seqnr, struct ebox_stream_chunk **chunk);

errf_t *ebox_stream_decrypt_chunk(struct ebox_stream_chunk *chunk);
errf_t *ebox_stream_encrypt_chunk(struct ebox_stream_chunk *chunk);
const uint8_t *ebox_stream_chunk_data(const struct ebox_stream_chunk *chunk,
    size_t *size);

#endif
