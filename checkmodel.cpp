// clang-format off

static const char * usage =

"usage: checksat [ -h | --help ] [ -v | --verbose ] <formula> <model>\n"
"\n"
"where\n"
"\n"
"  -h | --help      print this command line option summary\n"
"  -v | --verbose   increase verbosity and print more information\n"
"  -q | --quiet     be quiet (only prints errors)\n"
"\n"
"and\n"
"\n"
"  <formula>        input CNF formula in DIMACS format\n"
"  <model>          assumed model (in SAT competition format with 'v' lines)\n"
"\n"
"The formula is read and checked against the provided model, where\n"
"integer DIMACS literals in 'v' lines are assumed to be true.  If the\n"
"model satisfies the formula the checker exits with exit code '0' after\n"
"printing the status line 's MODEL VERIFIED'.  Otherwise an error message\n"
"is printed on '<stderr>' and the checker exists with exit code '1'.\n"
"\n"
"Files with suffix '.bz2', '.gz', and '.xz' are decompressed using the\n"
"corresponding tools 'bzip2', 'gzip' and 'xz'.  If a file name is '-'\n"
"the tool reads from '<stdin>' (only one '-' is allowed).\n"
;

// clang-format on

#include <cassert>
#include <cctype>
#include <climits>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <vector>

extern "C" {
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>
};

static int verbosity;

static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void die(const char *fmt, ...) {
  fputs("checkmodel: error: ", stderr);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void message(const char *, ...) __attribute__((format(printf, 1, 2)));

static void message(const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void verbose(const char *, ...) __attribute__((format(printf, 1, 2)));

static void verbose(const char *fmt, ...) {
  if (verbosity < 1)
    return;
  fputs("c ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static double time(void) {
  struct rusage u;
  double res;
  if (getrusage(RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

struct file {
  const char *type;
  const char *path;
  FILE *file;
  int close;
  size_t line;
  bool done;
};

static struct file formula = {.type = "formula"}, model = {.type = "model"};

static bool has_suffix(const char *str, const char *suffix) {
  const size_t k = strlen(str), l = strlen(suffix);
  return k >= l && !strcmp(str + k - l, suffix);
}

static FILE *read_pipe(const char *zipper, const char *path) {
  size_t len = strlen(zipper) + strlen(path) + 8;
  char *tmp = (char *)malloc(len);
  snprintf(tmp, len, "%s -d -c %s", zipper, path);
  FILE *file = popen(tmp, "r");
  free(tmp);
  return file;
}

static bool exists(const char *path) {
  struct stat stat;
  return !::stat(path, &stat);
}

static void read_file(file &file) {
  if (!file.path || !strcmp(file.path, "-")) {
    file.file = stdin, file.path = "<stdin>", assert(!file.close);
    verbose("reading %s from '%s'", file.type, file.path);
  } else {
    file.close = 2;
    if (!exists(file.path))
      die("%s file '%s' does not exist", file.type, file.path);
    verbose("opening %s '%s'", file.type, file.path);
    if (has_suffix(file.path, ".bz2"))
      file.file = read_pipe("bzip2", file.path);
    else if (has_suffix(file.path, ".gz"))
      file.file = read_pipe("gzip", file.path);
    else if (has_suffix(file.path, ".xz"))
      file.file = read_pipe("xz", file.path);
    else if (!(file.file = fopen(file.path, "r")))
      die("can not read %s '%s'", file.type, file.path);
    else
      file.close = 1;
  }
  file.line = 1;
}

static void close_file(file &file) {
  verbose("closing %s '%s' after reading %zu lines", file.type, file.path,
          file.line);
  if (file.close == 1)
    fclose(file.file);
  if (file.close == 2)
    pclose(file.file);
}

static void parse_error(file &, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static void parse_error(file &file, const char *fmt, ...) {
  fputs("checkmodel: parse error: ", stderr);
  if (!file.done)
    fprintf(stderr, "at line %zu ", file.line);
  fprintf(stderr, "in %s file '%s': ", file.type, file.path);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static int next_char(file &file) {
  int res = getc(file.file);
  if (res == '\r') {
    res = getc(file.file);
    if (res != '\n')
      parse_error(file, "expected new-line after carriage-return");
  }
  if (res == '\n')
    file.line++;
  return res;
}

static size_t variables;
static size_t allocated;
static signed char *values;

static void parse_model(file &file) {
  double start = time();
  bool found_satisfiable_status = false;
  bool found_terminating_zero = false;
  bool found_v_lines = false;
  size_t parsed = 0;
  int ch;
  while ((ch = next_char(file)) != EOF) {
    if (ch == 'c') {
      while ((ch = next_char(file)) != '\n')
        if (ch == EOF)
          parse_error(file, "unexpected end-of-file in comment");
    } else if (ch == 's') {
      if (next_char(file) != ' ')
        parse_error(file, "expected space after 's'");
      for (const char *p = "SATISFIABLE"; *p; p++)
        if (*p != next_char(file))
          parse_error(file, "expected 'SATISFIABLE' after 's'");
      if (next_char(file) != '\n')
        parse_error(file, "expected new-line at end of status line");
      verbose("parsed 's SATISFIABLE' status line");
      found_satisfiable_status = true;
    } else if (ch == 'v') {
      if (!found_satisfiable_status)
        parse_error(file, "'v' line before 's' line");
      if (found_v_lines && found_terminating_zero)
        parse_error(file, "unexpected 'v' line");
      if (!found_v_lines)
        verbose("found first 'v' line at line %zu", file.line);
      size_t line = file.line;
      ch = next_char(file);
      while (ch != '\n') {
        if (ch == EOF)
          parse_error(file, "unexpected end-of-file in 'v' line");
        if (ch == ' ' || ch == '\t') {
          ch = next_char(file);
          continue;
        }
        signed char value;
        if (ch == '-') {
          value = -1;
          ch = next_char(file);
          if (!isdigit(ch) || ch == '0')
            parse_error(file, "expected positive digit after '-'");
        } else {
          value = 1;
          if (!isdigit(ch))
            parse_error(file, "expected digit or '-'");
        }
        assert(isdigit(ch));
        unsigned idx = ch - '0';
        while (isdigit(ch = next_char(file))) {
          if ((unsigned)INT_MAX / 10 < idx)
            parse_error(file, "literal in 'v' line too large");
          idx *= 10;
          unsigned digit = ch - '0';
          if ((unsigned)INT_MAX - digit < idx)
            parse_error(file, "literal in 'v' line too large");
          idx += digit;
        }
        if (idx) {
          size_t needed = idx + 1;
          if (needed > allocated) {
            allocated = allocated ? 2 * allocated : 1;
            while (allocated < needed)
              allocated *= 2;
            values = (signed char *)realloc(values, allocated);
            if (!values)
              die("out-of-memory reallocating values");
          }
          if (variables < idx) {
            memset(values + variables + 1, 0, idx - variables);
            variables = idx;
          }
          if (values[idx])
            parse_error(file, "variable '%d' already set", idx);
          values[idx] = value;
          parsed++;
        } else {
          found_terminating_zero = true;
          verbose("found last 'v' line at line %zu", line);
        }
      }
      found_v_lines = true;
    }
  }
  file.done = true;
  if (!found_satisfiable_status)
    parse_error(file, "status line 's SATISFIABLE' missing");
  if (!found_v_lines)
    parse_error(file, "'v' lines missing");
  if (!found_terminating_zero)
    parse_error(file, "terminating '0' in 'v' lines missing");
  message("parsed %zu values in %.2f seconds", parsed, time() - start);
}

static void parse_and_check_formula(file &file) {
  double start = time();
  int ch;
  while ((ch = next_char(file)) == 'c')
    while ((ch = next_char(file)) != '\n')
      if (ch == EOF)
        parse_error(file, "unexpected end-of-file in comment");
  if (ch != 'p')
    parse_error(file, "expected 'c' or 'p'");
  for (const char *p = " cnf "; *p; p++)
    if (next_char(file) != *p)
      parse_error(file, "invalid 'p' header line");
  ch = next_char(file);
  if (!isdigit(ch))
    parse_error(file, "expected digit after 'p cnf '");
  int specified_variables = ch - '0';
  while (isdigit(ch = next_char(file))) {
    if (INT_MAX / 10 < specified_variables)
      parse_error(file, "specified variables too large");
    specified_variables *= 10;
    int digit = ch - '0';
    if (INT_MAX - digit < specified_variables)
      parse_error(file, "specified variables too large");
    specified_variables += digit;
  }
  if (ch != ' ')
    parse_error(file, "expected space after 'p cnf %d'", specified_variables);
  ch = next_char(file);
  if (!isdigit(ch))
    parse_error(file, "expected digit after 'p cnf %d '", specified_variables);
  size_t specified_clauses = ch - '0';
  const size_t max_specified_clauses = ~(size_t)0;
  while (isdigit(ch = next_char(file))) {
    if (max_specified_clauses / 10 < specified_clauses)
      parse_error(file, "specified clauses too large");
    specified_clauses *= 10;
    int digit = ch - '0';
    if (max_specified_clauses - digit < specified_clauses)
      parse_error(file, "specified clauses too large");
    specified_clauses += digit;
  }
  if (ch == ' ')
    while ((ch = next_char(file)) == ' ')
      ;
  if (ch != '\n')
    parse_error(file, "expected new-line after 'p cnf' header");
  verbose("parsed 'p cnf %d %zu' header", specified_variables,
          specified_clauses);
  size_t parsed_clauses = 0;
  bool satisfied = false;
  size_t line = 0;
  int lit = 0;
  std::vector<int> clause;
  for (;;) {
    ch = next_char(file);
    if (ch == ' ' || ch == '\t' || ch == '\n')
      continue;
    if (ch == 'c') {
      while ((ch = next_char(file)) != '\n')
        if (ch == EOF)
          parse_error(file, "unexpected end-of-file in comment");
      continue;
    }
    if (ch == EOF)
      break;
    if (!lit)
      line = file.line;
    if (parsed_clauses == specified_clauses)
      parse_error(file, "too many clauses");
    signed char sign;
    if (ch == '-') {
      ch = next_char(file);
      if (!isdigit(ch) || ch == '0')
        parse_error(file, "expected positive digit after '-'");
      sign = -1;
    } else {
      if (!isdigit(ch))
        parse_error(file, "expected digit or '-'");
      sign = 1;
    }
    int idx = ch - '0';
    while (isdigit(ch = next_char(file))) {
      if (INT_MAX / 10 < idx)
        parse_error(file, "literal in 'v' line too large");
      idx *= 10;
      int digit = ch - '0';
      if (INT_MAX - digit < idx)
        parse_error(file, "literal in 'v' line too large");
      idx += digit;
    }
    lit = sign * idx;
    if (ch == 'c') {
      while ((ch = next_char(file)) != '\n')
        if (ch == EOF)
          parse_error(file, "unexpected end-of-file in comment");
    }
    if (ch != EOF && ch != ' ' && ch != '\t' && ch != '\n')
      parse_error(file, "expected white-space after '%d'", lit);
    if (lit) {
      if ((unsigned)idx <= variables) {
        signed char value = values[idx];
        if (sign == value)
          satisfied = true;
      }
      clause.push_back(lit);
    } else {
      parsed_clauses++;
      if (!satisfied) {
        fflush(stdout);
        fprintf(stderr,
                "checkmodel: failed: "
                "clause %zu at line %zu in '%s' falsified",
                parsed_clauses, line, file.path);
        if (verbosity < 0)
          fputc('\n', stderr);
        else {
          fputs(":\n", stderr);
          for (auto other : clause)
            fprintf(stderr, "%d ", other);
          fputs("0\n", stderr);
        }
        exit(1);
      }
      clause.clear();
      satisfied = false;
    }
  }
  if (lit)
    parse_error(file, "zero after clause %zu missing", parsed_clauses);
  file.done = true;
  if (parsed_clauses < specified_clauses)
    parse_error(file, "clauses missing");
  assert(parsed_clauses == specified_clauses);
  message("parsed and checked %zu clauses in %.2f seconds", parsed_clauses,
          time() - start);
}

int main(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose"))
      verbosity = 1;
    else if (!strcmp(arg, "-q") || !strcmp(arg, "--quiet"))
      verbosity = -1;
    else if (arg[0] == '-' && arg[1])
      die("invalid option '%s' (try '-h')", arg);
    else if (!formula.path)
      formula.path = arg;
    else if (!model.path)
      model.path = arg;
    else
      die("too many files '%s', '%s' and '%s'", formula.path, model.path, arg);
  }
  if (!formula.path)
    die("formula missing (try '-h')");
  if (!model.path)
    die("model missing (try '-h')");
  if (!strcmp(formula.path, "-") && !strcmp(model.path, "-"))
    die("can only read one file from '<stdin>'");
  message("CheckModel DIMACS Model Checker");
  read_file(model);
  parse_model(model);
  close_file(model);
  read_file(formula);
  parse_and_check_formula(formula);
  close_file(formula);
  if (values)
    free(values);
  if (verbosity < 0)
    return 0;
  fputs("s MODEL VERIFIED\n", stdout);
  fflush(stdout);
  return 0;
}
