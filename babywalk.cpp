// clang-format off

static const char *

usage =

"usage: babywalk [ -h ] [ <input> ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -h           print this command line option summary\n"
"  -n           do not print satisfying assignment (model)\n"
"  -v           increase verbosity level\n"
"  -q           disable all messages\n"
#ifdef LOGGING
"  -l           enable logging for debugging\n"
#endif          
"\n"
"  -t <string>  hash '<string>' to random number generator seed\n"
"\n"
"and '<input>' is the path to a file with a formula in DIMACS format. If\n"
"'<input>' is '-' we read from '<stdin>', which is also the default. We\n"
"use 'bzip2', 'gzip' and 'xz' to decompress and compress '.bz2', '.gz' or\n"
"'.xz' files.\n"

;

// clang-format on

#include <cassert>
#include <cctype>
#include <cinttypes>
#include <climits>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

extern "C" {
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>
};

#include <algorithm>
#include <vector>

// The main 'clause' data structure.

struct clause {
  size_t id;   // Clause identifier for debugging.
  size_t pos;  // Position in 'unsatisfied' stack.
  size_t size; // The actual size of 'literals'.
  int literals[];
  int *begin() { return literals; }
  int *end() { return literals + size; }
  const int *begin() const { return literals; }
  const int *end() const { return literals + size; }
  void print(FILE *file = stdout) {
    for (auto lit : *this)
      fprintf(file, "%d ", lit);
    fputs("0\n", file);
  }
};

// Actual global state of preprocessor.

static int variables;                      // Total number of variables.
static bool found_empty_clause;            // Found empty clause.
static std::vector<clause *> clauses;      // Contains all clauses.
static std::vector<clause *> *occurrences; // Connections to all clauses.

// Part of the state needed for parsing and unit propagation.

static std::vector<int> simplified;
static std::vector<int> unsimplified;

static std::vector<int> trail; // Assigned literals.
static size_t propagated;      // Propagation level of trail.

static signed char *values; // Values of all literals.
static bool *marks;         // Marks for simplification.

// The state of the local source solver.

static std::vector<clause *> unsatisfied; // Stack of unsatisfied clauses.
static uint64_t generator;                // Random number generator state.

// Parsing state.

static int close_input; // 0=stdin, 1=file, 2=pipe
static const char *input_path;
static FILE *input_file;
static size_t lineno = 1;

// Global flags.

static int verbosity;
static bool do_not_print_model;
static const char *thank;

// Some statistics.

static struct {
  size_t added;    // Number of added clauses (used for ID).
  size_t parsed;   // Number of parsed clauses.
  size_t flipped;  // Number of flipped variables.
  size_t restarts; // Number of restarts.
} stats;

// Returns the time in seconds spent in this process.

static double time(void) {
  struct rusage u;
  double res;
  if (getrusage(RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

// Functions to print messages follow.

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

static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void die(const char *fmt, ...) {
  fputs("babywalk: error: ", stderr);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

static void error(const char *, ...) __attribute__((format(printf, 1, 2)));

static void error(const char *fmt, ...) {
  fprintf(stderr, "babywalk: parse error: at line %zu in '%s': ", lineno,
          input_path);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

#ifdef LOGGING

static const char *LOG(int lit) {
  if (verbosity < INT_MAX)
    return 0;
  static char buffer[4][32];
  static size_t next_buffer = 0;
  const size_t size_buffer = sizeof buffer / sizeof *buffer;
  int value = values[lit];
  if (value)
    sprintf(buffer[next_buffer], "%d=%d", lit, value);
  else
    sprintf(buffer[next_buffer], "%d", lit);
  const char *res = buffer[next_buffer++];
  if (next_buffer == size_buffer)
    next_buffer = 0;
  return res;
}

static void LOG(const char *, ...) __attribute__((format(printf, 1, 2)));

static void LOG(const char *fmt, ...) {
  if (verbosity < INT_MAX)
    return;
  fputs("c LOG ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void LOG(clause *c, const char *fmt, ...) {
  if (verbosity < INT_MAX)
    return;
  fputs("c LOG ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf(" size %zu clause[%zu]", c->size, c->id);
  for (auto lit : *c)
    printf(" %s", LOG(lit));
  fputc('\n', stdout);
  fflush(stdout);
}

static void LOG(const std::vector<int> &c, const char *fmt, ...) {
  if (verbosity < INT_MAX)
    return;
  fputs("c LOG ", stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  printf(" size %zu temporary clause", c.size());
  for (auto lit : c)
    printf(" %s", LOG(lit));
  fputc('\n', stdout);
  fflush(stdout);
}

#else

#define LOG(...)                                                               \
  do {                                                                         \
  } while (false)

#endif

// Clause simplification during parsing.

static bool tautological_clause(const std::vector<int> &clause) {
  bool res = false;
  for (auto lit : clause) {
    if (marks[lit])
      continue;
    if (values[lit] > 0) {
      LOG(clause, "literal %s satisfied", LOG(lit));
      res = true;
      break;
    }
    if (marks[-lit]) {
      LOG(clause, "tautological containing %s and %s", LOG(-lit), LOG(lit));
      res = true;
      break;
    }
    marks[lit] = true;
  }
  for (auto lit : clause)
    marks[lit] = false;
  return res;
}

static bool simplify_clause(std::vector<int> &dst,
                            const std::vector<int> &src) {
  dst.clear();
  for (auto lit : src) {
    if (marks[lit]) {
      LOG(src, "duplicated %s in", LOG(lit));
      continue;
    }
    if (values[lit] < 0) {
      LOG(src, "falsified %s in", LOG(lit));
      continue;
    }
    assert(!marks[-lit]);
    marks[lit] = true;
    dst.push_back(lit);
  }
  for (auto lit : dst)
    marks[lit] = false;
  return dst.size() != src.size();
}

#ifndef NDEBUG

// Clause which are actually added (allocated and connected) have to be
// normalized, which means they do not contain any assigned nor
// duplicated literals, and are not tautological either.

static void check_simplified(const std::vector<int> &clause) {
  for (auto lit : clause) {
    assert(!values[lit]); // Not satisfied nor falsified.
    assert(!marks[lit]);  // No duplicates.
    assert(!marks[-lit]); // Not tautological.
    marks[lit] = true;
  }
  for (auto lit : clause)
    marks[lit] = false;
}

#endif

// Connect clauses and literals.

static void connect_literal(int lit, clause *c) {
  assert(c->size > 1);
  LOG(c, "connecting %s in", LOG(lit));
  occurrences[lit].push_back(c);
}

static void connect_clause(clause *c) {
  assert(c->size > 1);
  for (auto lit : *c)
    connect_literal(lit, c);
}

// Allocate, initialize, push and connect clause.

static clause *new_clause(const std::vector<int> &literals) {
#ifndef NDEBUG
  check_simplified(literals);
#endif
  const size_t size = literals.size();
  const size_t bytes = sizeof(clause) + size * sizeof(int);
  clause *res = (clause *)new char[bytes];
  res->size = size;
  res->id = stats.added++;
  memcpy(res->literals, &literals[0], size * sizeof(int));
  LOG(res, "new");
  if (size > 1) {
    clauses.push_back(res);
    connect_clause(res);
  }
  return res;
}

static void delete_clause(clause *c) {
  LOG(c, "delete");
  delete[](char *) c;
}

// Initialize after we know how many variables are needed.

static void init() {
  occurrences = new std::vector<clause *>[2 * variables + 1]();
  marks = new bool[2 * variables + 1]();
  values = new signed char[2 * variables + 1]();
  occurrences += variables;
  marks += variables;
  values += variables;
  LOG("initialized data-structures");
}

// At the end reclaim all allocated memory.

static void reset() {
  for (auto c : clauses)
    delete_clause(c);
  occurrences -= variables;
  marks -= variables;
  values -= variables;
  delete[] occurrences;
  delete[] marks;
  delete[] values;
  LOG("reset data-structures");
}

// Assign a new unit and push it on the trail stack.

static void assign(int lit, clause *reason) {
  assert(reason);
  LOG(reason, "assign %s reason", LOG(lit));
  assert(!values[lit]);
  assert(!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  trail.push_back(lit);
}

// Much simpler propagator than with watches.

static bool propagate() {
  assert(!found_empty_clause);
  while (propagated != trail.size()) {
    const int lit = trail[propagated++];
    LOG ("propagated %s", LOG (lit));
    for (auto c : occurrences[-lit]) {
      int unit = 0;
      for (auto other : *c) {
        const auto value = values[other];
        if (value < 0)
          continue;
        if (value > 0)
          goto NEXT_CLAUSE;
        if (unit)
          goto NEXT_CLAUSE;
        unit = other;
      }
      if (!unit) {
        LOG(c, "conflicting");
        found_empty_clause = true;
        return false;
      }
      assign(unit, c);
    NEXT_CLAUSE:;
    }
  }
  return true;
}

// Here start the parsing part.

static int next() {
  int ch = getc(input_file);
  if (ch == '\r') {
    ch = getc(input_file);
    if (ch != '\n')
      error("expected new-line after carriage-return");
  }
  if (ch == '\n')
    lineno++;
  return ch;
}

static bool has_suffix(const char *str, const char *suffix) {
  const size_t k = strlen(str), l = strlen(suffix);
  return k >= l && !strcmp(str + k - l, suffix);
}

static FILE *read_pipe(const char *zipper) {
  char *tmp = (char *)malloc(strlen(zipper) + strlen(input_path) + 8);
  sprintf(tmp, "%s -d -c %s", zipper, input_path);
  FILE *file = popen(tmp, "r");
  free(tmp);
  return file;
}

static void parse() {

  double start = time();

  if (!input_path || !strcmp(input_path, "-"))
    input_file = stdin, input_path = "<stdin>", assert(!close_input);
  else if (has_suffix(input_path, ".bz2"))
    input_file = read_pipe("bzip2"), close_input = 2;
  else if (has_suffix(input_path, ".gz"))
    input_file = read_pipe("gzip"), close_input = 2;
  else if (has_suffix(input_path, ".xz"))
    input_file = read_pipe("xz"), close_input = 2;
  else if (!(input_file = fopen(input_path, "r")))
    die("can not read '%s'", input_path);
  else
    close_input = 1;

  message("reading from '%s'", input_path);
  int ch;
  while ((ch = next()) == 'c')
    while ((ch = next()) != '\n')
      if (ch == EOF)
        error("unexpected end-of-file in comment");
  if (ch != 'p')
    error("expected comment or header");
  for (const char *p = " cnf "; *p; p++)
    if (*p != next())
      error("invalid header");
  if (!isdigit(ch = next()))
    error("expected digit");
  variables = ch - '0';
  while (isdigit(ch = next())) {
    if (INT_MAX / 10 < variables)
      error("too many variables specified in header");
    variables *= 10;
    int digit = (ch - '0');
    if (INT_MAX - digit < variables)
      error("too many variables specified in header");
    variables += digit;
  }
  if (ch != ' ')
    error("expected white space");
  LOG("%u variables specified", variables);
  if (!isdigit(ch = next()))
    error("expected digit");
  size_t expected = ch - '0';
  const size_t SIZE_T_MAX = ~(size_t)0;
  while (isdigit(ch = next())) {
    if (SIZE_T_MAX / 10 < expected)
      error("too many clauses specified in header");
    expected *= 10;
    int digit = (ch - '0');
    if (SIZE_T_MAX - digit < expected)
      error("too many clauses specified in header");
    expected += digit;
  }
  if (ch != '\n')
    error("expected new-line");
  message("found 'p cnf %d %zu' header", variables, expected);
  init();
  int lit = 0;
  for (;;) {
    ch = next();
    if (ch == ' ' || ch == '\n')
      continue;
    if (ch == EOF)
      break;
    int sign = 1;
    if (ch == '-') {
      ch = next();
      sign = -1;
    }
    if (!isdigit(ch))
      error("expected digit");
    if (stats.parsed == expected)
      error("specified clauses exceeded");
    lit = ch - '0';
    while (isdigit(ch = next())) {
      if (INT_MAX / 10 < lit)
        error("literal too large");
      lit *= 10;
      int digit = ch - '0';
      if (INT_MAX - digit < lit)
        error("literal too large");
      lit += digit;
    }
    if (ch != ' ' && ch != '\n')
      error("expected white-space");
    if (lit > variables)
      error("invalid variable %d", lit);
    if (lit) {
      lit *= sign;
      unsimplified.push_back(lit);
    } else {
      stats.parsed++;
      LOG(unsimplified, "parsed");
      if (!found_empty_clause && !tautological_clause(unsimplified)) {
        if (simplify_clause(simplified, unsimplified))
          LOG(simplified, "simplified");
        clause *c = new_clause(simplified);
        const size_t size = c->size;
        if (!size) {
          assert(!found_empty_clause);
          verbose("found empty clause");
          found_empty_clause = true;
        } else if (size == 1) {
          int unit = c->literals[0];
          LOG(simplified, "found unit %s", LOG(unit));
          assign(unit, c);
          if (!propagate()) {
            verbose("root-level propagation yields conflict");
            assert(found_empty_clause);
          }
        }
      }
      unsimplified.clear();
    }
  }
  if (lit)
    error("zero missing");
  if (stats.parsed != expected)
    error("clause missing");

  if (close_input == 1)
    fclose(input_file);
  if (close_input == 2)
    pclose(input_file);

  message("parsed %zu clauses in %.2f seconds", stats.parsed, time() - start);
}

// Remove satisfied clauses and falsified literals.

static void simplify() {
  for (int64_t lit = -variables; lit <= variables; lit++)
    occurrences[lit].clear();
  auto begin = clauses.begin();
  auto end = clauses.end();
  auto j = begin, i = j;
  while (i != end) {
    auto c = *j++ = *i++;
    simplified.clear();
    size_t new_size;
    for (auto lit : *c) {
      auto value = values[lit];
      if (value > 0) {
        j--;
        delete_clause(c);
        goto CONTINUE_WITH_NEXT_CLAUSE;
      }
      if (!value)
        simplified.push_back(lit);
    }
    new_size = simplified.size();
    assert(new_size > 1);
    if (new_size < c->size) {
      LOG(c, "unsimplified");
      for (size_t i = 0; i != new_size; i++)
        c->literals[i] = simplified[i];
      c->size = new_size;
      LOG(c, "simplified");
    }
    connect_clause(c);
  CONTINUE_WITH_NEXT_CLAUSE:;
  }
  clauses.resize(j - begin);
}

// Function for random number generation.

static unsigned next_random() {
  generator *= 6364136223846793005ul;
  generator += 1442695040888963407ul;
  assert(generator);
  return generator;
}

// Flip falsified literal.

static void flip(int lit) {
  LOG("flipping %s", LOG(lit));
  assert(values[lit] < 0);
  values[-lit] = -1;
  values[lit] = 1;
  stats.flipped++;
}

// Restart by generating new assignment.

static void restart() {
  LOG("restarting");
  stats.restarts++;
  unsatisfied.clear();
}

static void walksat() { restart(); }

static void print_values() {
  size_t printed = 0;
  for (int64_t idx = 1; idx <= variables; idx++) {
    auto value = values[idx];
    if (!value)
      continue;
    if (!(printed % 8)) {
      if (printed)
        fputc('\n', stdout);
      fputc('v', stdout);
    }
    printf(" %" PRId64, value * idx);
    printed++;
  }
  if (!(printed % 8)) {
    if (printed)
      fputc('\n', stdout);
    fputc('v', stdout);
  }
  fputs(" 0\n", stdout);
}

// Main solving routine.

static int solve() {
  if (found_empty_clause) {
    fputs("s UNSATISFIABLE\n", stdout);
    fflush(stdout);
    return 20;
  }
  if (thank) {
    for (auto p = thank; *p; p++)
      generator ^= *p, (void)next_random();
    verbose("hashed '%s' to seed '%" PRIu64, thank, generator);
  }
  walksat();
  fputs("s SATISFIABLE\n", stdout);
  fflush(stdout);
  if (!do_not_print_model)
    print_values();
  return 10;
}

// Common statistics functions.

static double average(double a, double b) { return b ? a / b : 0; }

// Report statistics.

static void report() {
  double t = time();
  message("%-21s %13zu %12.2f per second",
          "flipped-variables:", stats.flipped, average(stats.flipped, t));
  message("%-21s %26.2f seconds", "process-time:", time());
}

// Parse command line options.

static void options(int argc, char **argv) {
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-v"))
      verbosity += (verbosity != INT_MAX);
    else if (!strcmp(arg, "-q"))
      verbosity = -1;
    else if (!strcmp(arg, "-t")) {
      if (++i == argc)
        die("argument to '-t' missing (try '-h')");
      thank = argv[i];
    } else if (!strcmp(arg, "-l"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die("invalid option '-l' (compiled without logging support)");
#endif
    else if (!strcmp(arg, "-n"))
      do_not_print_model = true;
    else if (arg[0] == '-' && arg[1])
      die("invalid option '%s' (try '-h')", arg);
    else if (!input_path)
      input_path = arg;
    else
      die("too many file arguments '%s' and '%s'", input_path, arg);
  }
}

static void banner() { message("BabyWalk Local Search SAT Solver"); }

int main(int argc, char **argv) {
  options(argc, argv);
  banner();
  parse();
  simplify();
  int res = solve();
  report();
  reset();
  if (thank)
    message("thanks to '%s'", thank);
  message ("exit %d", res);
  return res;
}
