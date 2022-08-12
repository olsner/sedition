#define _GNU_SOURCE
#undef NDEBUG

#include <assert.h>
#include <ctype.h>
#include <malloc.h>
#include <regex.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/random.h>

struct string { char* buf; size_t len; size_t alloc; };
typedef struct string string;

struct re_t {
    bool init;
    regex_t regex;
    const char *str;
};
typedef struct re_t re_t;

#define MAXGROUP 9
struct match_t {
    // Possible required for next_match
    const re_t *regex;

    bool result;
    regmatch_t matches[MAXGROUP + 1];
};
typedef struct match_t match_t;

static int lineNumber;
static int inputFileIndex;

//
// String functions
//

static size_t grow(size_t prev, size_t min)
{
    const size_t plus10 = prev + prev / 10;
    // Grow 10% or directly to the given size
    return min > plus10 ? min : plus10;
}

static void ensure_len_discard(string* s, size_t n)
{
    if (n > s->alloc) {
        n = grow(s->alloc, n);
        if (s->alloc) {
            free(s->buf);
        }
        s->buf = malloc(n);
        if (!s->buf) abort();
        s->alloc = malloc_usable_size(s->buf);
        s->len = 0;
    }
}

static void ensure_len(string* s, size_t n)
{
    if (n > s->alloc) {
        n = grow(s->alloc, n);
        if (s->alloc == 0) {
            // Copy static string to new heap buffer.
            char *new_buf = malloc(n);
            memcpy(new_buf, s->buf, s->len);
            s->buf = new_buf;
        } else {
            s->buf = realloc(s->buf, n);
        }
        if (!s->buf) abort();
        s->alloc = malloc_usable_size(s->buf);
    }
}

static void free_string(string* s)
{
    if (s->alloc > 0) {
        free(s->buf);
    }
    s->alloc = s->len = 0;
    s->buf = 0;
}

static void set_str_const(string* dst, const char* src, size_t n)
{
    dst->alloc = 0;
    dst->buf = (char*)src;
    dst->len = n;
}

static void copy_cstr(string* dst, const char* src, size_t n)
{
    ensure_len_discard(dst, n);
    memcpy(dst->buf, src, n);
    dst->len = n;
}

static void append_str(string* dst, const char *str, size_t n)
{
    ensure_len(dst, dst->len + n);
    memcpy(dst->buf + dst->len, str, n);
    dst->len += n;
}

static void copy(string* dst, string* src)
{
    ensure_len_discard(dst, src->len);
    memcpy(dst->buf, src->buf, src->len);
    dst->len = src->len;
}

static void concat_newline(string* dst, string* a, string* b)
{
    const size_t n = a->len + 1 + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    *p++ = '\n';
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void concat(string* dst, string* a, string* b)
{
    const size_t n = a->len + b->len;
    ensure_len_discard(dst, n);

    char *p = mempcpy(dst->buf, a->buf, a->len);
    memcpy(p, b->buf, b->len);
    dst->len = n;
}

static void concat_inplace(string* dst, string* b)
{
    append_str(dst, b->buf, b->len);
}

static void substring(string* dst, string* src, size_t i1, size_t i2)
{
    assert(i1 <= src->len && i2 <= src->len);
    assert(i1 <= i2);
    const size_t n = i2 - i1;
    ensure_len_discard(dst, n);
    memcpy(dst->buf, src->buf + i1, n);
    dst->len = n;
}

static void trans(string* dst, const char* from, const char* to, string* src)
{
    ensure_len_discard(dst, src->len);
    assert(strlen(to) >= strlen(from));
    for (size_t i = 0; i < src->len; i++) {
        char c = src->buf[i];
        const char *p = strchr(from, c);
        if (p) {
            c = to[p - from];
        }
        dst->buf[i] = c;
    }
    dst->len = src->len;
}

static void random_string(string* dst)
{
    uint8_t temp[16];
    getrandom(temp, sizeof(temp), 0);

    ensure_len_discard(dst, 2 * sizeof(temp) + 1);
    for (size_t i = 0; i < sizeof(temp); i++) {
        snprintf(dst->buf + 2 * i, 3, "%02x", temp[i]);
    }
    dst->len = 2 * sizeof(temp);
}

static void format_literal(string* dst, int width, string* s)
{
    int col = 0;
    dst->len = 0;
    for (size_t i = 0; i < s->len; i++) {
        uint8_t c = s->buf[i];
        size_t prev = dst->len;
        if (c == '\n') {
            append_str(dst, "$\n", 2);
            col = 0;
        } else if (c == '\\') {
            append_str(dst, "\\\\", 2);
            col += 2;
        } else if (!isprint(c) || c >= 128) {
            // one more here to have room for a NUL from snprintf
            append_str(dst, "\\ooo", 5);
            dst->len--;
            snprintf(dst->buf + dst->len - 3, 4, "%03o", c);
            col += 4;
        } else {
            append_str(dst, &c, 1);
            col++;
        }
        // TODO Should be breaking before output? I think the haskell also gets
        // this wrong if e.g. an octal escape would straddle a line break.
        if (col >= width - 1) {
            append_str(dst, "\\\n", 2);
            col = 0;
        }
    }
    append_str(dst, "$", 1);
}

static void format_int(string* dst, int i)
{
    char temp[32];
    snprintf(temp, sizeof(temp), "%d", i);
    copy_cstr(dst, temp, strlen(temp));
}

//
// Regex functions
//

static void compile_regexp(re_t* re, const char* regexp, bool ere)
{
    if (re->init) {
        return;
    }

    int res = regcomp(&re->regex, regexp, ere ? REG_EXTENDED : 0);
    if (res) {
        fprintf(stderr, "regcomp: error %d in %s\n", res, regexp);
        abort();
    }
    re->init = true;
    re->str = regexp;
}

static void free_regexp(re_t* re)
{
    regfree(&re->regex);
}

static void match_regexp(match_t* m, string* s, const re_t* regex, size_t offset)
{
    memset(m, 0, sizeof(*m));

    // Stop matching when we've consumed the whole string, but allow a zero
    // length match if it comes first?
    if (offset && offset >= s->len) {
        return;
    }

    m->regex = regex;
    m->matches[0].rm_so = offset;
    m->matches[0].rm_eo = s->len;
    // REG_STARTEND with non-zero offset seems to imply REG_NOTBOL in glibc.
    const int flags = REG_STARTEND | (offset ? REG_NOTBOL : 0);
    int res = regexec(&regex->regex, s->buf, MAXGROUP + 1, m->matches, flags);
    if (res != 0 && res != REG_NOMATCH) {
        fprintf(stderr, "regexec: error %d in %s\n", res, regex->str);
        abort();
    }
    m->result = (res == 0);
}

static void copy_match(match_t* dst, match_t* src)
{
    memcpy(dst, src, sizeof(match_t));
}

static void next_match(match_t* dst, match_t* src, string* s)
{
    match_regexp(dst, s, src->regex, src->matches[0].rm_eo);
}

//
// File and I/O functions
//

static void print(FILE* fp, string* s)
{
    assert(fp);
    fwrite(s->buf, 1, s->len, fp);
    fprintf(fp, "\n");
}

static bool is_eof(FILE* fp)
{
    if (fp == NULL) return true;

    int c = getc(fp);
    if (c == EOF) {
        return true;
    }
    ungetc(c, fp);
    return false;
}

static void strip_trailing_newline(string* s)
{
    if (s->buf[s->len - 1] == '\n') {
        s->len--;
    }
}

static bool read_line(string* s, FILE* fp)
{
    if (fp == NULL) return false;

    ssize_t res = getline(&s->buf, &s->alloc, fp);
    if (res < 0) return false;
    s->len = res;

    // TODO Only increment on fd 0?
    lineNumber++;
    strip_trailing_newline(s);
    return true;
}

static void read_file(string* s, FILE* fp)
{
    assert(fp);

    s->len = 0;
    ensure_len(s, 1024);
    while (true) {
        if (s->len == s->alloc) {
            ensure_len(s, s->alloc + 1);
        }
        ssize_t res = fread(s->buf + s->len, 1, s->alloc - s->len, fp);
        if (res <= 0) break;

        s->len += res;
    }

    strip_trailing_newline(s);
}

static FILE* next_input(int argc, const char *argv[])
{
    // Starts at 0, first input file is at argv[1]
    inputFileIndex++;
    if (inputFileIndex == 1 && argc == 1) {
        // No input files - use stdin
        return stdin;
    }
    if (argc > inputFileIndex) {
        return fopen(argv[inputFileIndex], "r");
    }
    // EOF
    return NULL;
}

static FILE* open_file(const char *path, bool write)
{
    return fopen(path, write ? "w" : "r");
}

static void close_file(FILE* fp)
{
    if (fp && fp != stdin) {
        fclose(fp);
    }
}

static bool is_all_eof(FILE** pfp, int argc, const char *argv[])
{
    FILE* fp = *pfp;
    while (fp && is_eof(fp)) {
        close_file(fp);
        fp = next_input(argc, argv);
    }
    *pfp = fp;
    return fp == NULL;
}

//
// IPC Functions: unimplemented mostly
//

static void wait_or_event(FILE* fp)
{
    // With IPC: check for either pending messages or a input on fp.
    // (I guess we should be looking for complete lines on fp, but as a cheat
    // we could also assume that seeing the start of a line means we will
    // eventually get the whole thing).
    // Without IPC: no-op, reading from a file will simply block instead.
}

static void get_message(string* s)
{
    fprintf(stderr, "UNIMPL: IPC get_message\n");
    abort();
}
