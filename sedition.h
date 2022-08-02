// TODO Bundle this in Compile.hs or something so we don't need loose data
// files in a sedition distribution.

#include <regex.h>
#include <string.h>

struct string { char* buf; size_t len; size_t alloc; };
typedef struct string string;

//
// String functions
//

static void ensure_len_discard(string* s, size_t n)
{
    if (n > s->alloc) {
        free(s->buf);
        s->buf = malloc(n);
        if (!s->buf) abort();
        s->alloc = n;
        s->len = 0;
    }
}

static void free_string(string* s)
{
    free(s->buf);
    s->alloc = s->len = 0;
    s->buf = 0;
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

//
// Regex functions
//

static bool checkRE(string* s, const char* regexp, int cflags)
{
    regex_t re;
    regmatch_t match;
    int res = regcomp(&re, regexp, cflags);
    if (res) {
        fprintf(stderr, "regcomp: error %d in %s\n", res, regexp);
        abort();
    }
    match.rm_so = 0;
    match.rm_eo = s->len;
    res = regexec(&re, s->buf, 0, &match, REG_STARTEND);
    if (res != 0 && res != REG_NOMATCH) {
        fprintf(stderr, "regexec: error %d in %s\n", res, regexp);
        abort();
    }
    regfree(&re);
    return res == 0;
}

//
// File and I/O functions
//

static void write_file(const char* path, string* src)
{
    // TODO Appends newline?
    fprintf(stderr, "UNIMPL: write to %s: %s\n", path, src->buf);
}

static void print(FILE* fp, string* s)
{
    // TODO Track input and output separately so that fd 0 can be stdin/out?
    // Or change the semantics of file descriptors a bit...
    if (fp == NULL) fp = stdout;
    fwrite(s->buf, 1, s->len, fp);
    fprintf(fp, "\n");
}

static bool is_eof(FILE* fp)
{
    if (fp == NULL) fp = stdin;
    return feof(fp);
}

static void read_line(string* s, FILE* fp)
{
    if (fp == NULL) fp = stdin;
    ssize_t res = getline(&s->buf, &s->alloc, fp);
    if (res < 0) exit(0);
    s->len = res;
}

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
