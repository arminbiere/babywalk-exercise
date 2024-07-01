// clang-format off

static const char *

usage =

"usage: babywalk [ -h ] [ <input> ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -h  print this command line option summary\n"
"  -n  do not print satisfying assignment (model)\n"
"  -v  increase verbosity level\n"
"  -q  disable all messages\n"
#ifdef LOGGING     
"  -l  enable logging for debugging\n"
#endif              
"\n"
"  --random   random literal algorithm\n"
"  --focused  focused random walk algorithm\n"
"  --walksat  WalkSAT algorithm (not implemented)\n"
"  --probsat  ProbSAT algorithm (not implemented)\n"
"\n"
"  -f <flips>        limit total number of flips\n"
"  -s <seed>         use '<seed>' to initialize random number generator\n"
"  -t <seconds>      limit to this number of seconds\n"
"  --thank <string>  hash '<string>' to random number generator seed\n"
"\n"
"  --always-restart      restart after each flip\n"
"  --never-restart       never schedule restarts\n"
"  --fixed-restart       fixed constant restart interval\n"
"  --reluctant-restart   restart interval doubled reluctantly\n"
"  --geometric-restart   restart interval with geometric increase\n"
"  --arithmetic-restart  restart interval with arithmetic increase\n"
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
#include <csignal>
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
#include <string>
#include <vector>

/*------------------------------------------------------------------------*/

// Some global common constants.

static const size_t max_size_t = ~(size_t)0;
static const uint64_t max_uint64_t = ~(uint64_t)0;
static const size_t invalid_position = max_size_t;
static const size_t invalid_minimum = max_size_t;
static const size_t invalid_break_value = max_size_t;
static const uint64_t invalid_limit = max_uint64_t;

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

static int64_t variables;                  // Total number of variables.
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
static bool *forced;        // Assigned at root-level.

// The state of the local source solver.

static std::vector<clause *> unsatisfied; // Stack of unsatisfied clauses.
static uint64_t limit = invalid_limit;    // Limit on number of flips.
static uint64_t generator;                // Random number generator state.

static size_t minimum = invalid_minimum; // Minimum unsatisfied
static size_t best = invalid_minimum;    // Best since last restart.
static uint64_t minimum_restarts;        // Number of restarts for minimum.
static uint64_t minimum_flipped;         // Number flipped for minimum.

static volatile bool terminate;         // Force termination.
static volatile int termination_signal; // Triggered by this signal.

#ifndef NDEBUG
static std::vector<int> original_literals;  // Original clauses
static std::vector<size_t> original_lineno; // and their lines.
#endif

// Restart scheduling.

static enum {
  never_restart,
  always_restart,
  fixed_restart,
  reluctant_restart,
  geometric_restart,
  arithmetic_restart,
} restart_scheduler = reluctant_restart; // Default restart method.

static uint64_t base_restart_interval; // For arithmetic restarts.
static uint64_t reluctant_state[2];    // For reluctant restart.
static uint64_t restart_interval;      // Current restart interval.
static uint64_t next_restart;          // Restart limit.

// Algorithm choice.

static enum {
  random_algorithm,
  focused_algorithm,
  walksat_algorithm,
  probsat_algorithm
} algorithm = walksat_algorithm; // Default local search algorithm.

// Parsing state.

static int close_input; // 0=stdin, 1=file, 2=pipe
static const char *input_path;
static FILE *input_file;
static size_t lineno = 1;

// Global flags.

static int verbosity;
static bool do_not_print_model;
static const char *thank_string;

// Some statistics.

static struct {
  uint64_t added;          // Number of added clauses (used for ID).
  uint64_t parsed;         // Number of parsed clauses.
  uint64_t flipped;        // Number of flipped variables.
  uint64_t restarts;       // Number of restarts.
  uint64_t make_visited;   // Number of clauses visited while making clauses.
  uint64_t break_visited;  // Number of clauses visited while breaking clauses.
  uint64_t made_clauses;   // Number of made clauses.
  uint64_t broken_clauses; // Number of broken clauses.
  uint64_t random_walks;   // Number of random walks.
} stats;

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

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

static void verbose(int level, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static void verbose(int level, const char *fmt, ...) {
  if (verbosity < level)
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

static void fatal(const char *, ...) __attribute__((format(printf, 1, 2)));

static void fatal(const char *fmt, ...) {
  fputs("babywalk: fatal error: ", stderr);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  abort();
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

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

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
  res->pos = invalid_position;
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

/*------------------------------------------------------------------------*/

// Initialize after we know how many variables are needed.

static void initialize_variables() {
  occurrences = new std::vector<clause *>[2 * variables + 1]();
  marks = new bool[2 * variables + 1]();
  values = new signed char[2 * variables + 1]();
  forced = new bool[variables + 1]();
  occurrences += variables;
  marks += variables;
  values += variables;
  LOG("initialized data-structures");
}

// Initialize signal handlers.

static void catch_signal(int sig) {
  termination_signal = sig;
  terminate = true;
}

static const char *describe_signal(int sig) {
  if (sig == SIGINT)
    return "stop signal (SIGINT)";
  if (sig == SIGKILL)
    return "kill signal (SIGKILL)";
  if (sig == SIGSEGV)
    return "segmentation fault signal (SIGSEGV)";
  if (sig == SIGTERM)
    return "forced termination signal (SIGTERM)";
  if (sig == SIGALRM)
    return "timeout signal (SIGALRM)";
  return "unknown";
}

static void init() {
  (void)signal(SIGINT, catch_signal);
  (void)signal(SIGKILL, catch_signal);
  (void)signal(SIGSEGV, catch_signal);
  (void)signal(SIGTERM, catch_signal);
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
  delete[] forced;
  verbose(2, "reset data-structures");
}

/*------------------------------------------------------------------------*/

// Assign a new unit and push it on the trail stack.

static void root_level_assign(int lit, clause *reason) {
  assert(reason);
  LOG(reason, "assign %d reason", lit);
  assert(!values[lit]);
  assert(!values[-lit]);
  values[lit] = 1;
  values[-lit] = -1;
  trail.push_back(lit);
  forced[abs(lit)] = true;
}

// Much simpler propagator than with watches.

static bool propagate() {
  assert(!found_empty_clause);
  while (propagated != trail.size()) {
    const int lit = trail[propagated++];
    LOG("propagating %s", LOG(lit));
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
      root_level_assign(unit, c);
    NEXT_CLAUSE:;
    }
  }
  return true;
}

/*------------------------------------------------------------------------*/

// Here starts the parsing part.

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
  LOG("%" PRId64 " variables specified", variables);
  if (!isdigit(ch = next()))
    error("expected digit");
  size_t expected = ch - '0';
  while (isdigit(ch = next())) {
    if (max_size_t / 10 < expected)
      error("too many clauses specified in header");
    expected *= 10;
    int digit = (ch - '0');
    if (max_size_t - digit < expected)
      error("too many clauses specified in header");
    expected += digit;
  }
  if (ch != '\n')
    error("expected new-line");
  message("found 'p cnf %" PRId64 " %zu' header", variables, expected);
  initialize_variables();
  int lit = 0;
#ifndef NDEBUG
  size_t start_of_clause_lineno = 0;
#endif
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
#ifndef NDEBUG
    start_of_clause_lineno = lineno;
#endif
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
    lit *= sign;
#ifndef NDEBUG
    original_literals.push_back(lit);
#endif
    if (lit) {
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
          verbose(1, "found empty clause");
          found_empty_clause = true;
        } else if (size == 1) {
          int unit = c->literals[0];
          LOG(simplified, "found unit %s", LOG(unit));
          root_level_assign(unit, c);
          if (!propagate()) {
            verbose(1, "root-level propagation yields conflict");
            assert(found_empty_clause);
          }
        }
      }
      unsimplified.clear();
#ifndef NDEBUG
      original_lineno.push_back(start_of_clause_lineno);
#endif
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

/*------------------------------------------------------------------------*/

// Remove falsified literals and satisfied clauses and connect remaining.

static void simplify() {
  if (found_empty_clause)
    return;
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

/*------------------------------------------------------------------------*/

// Function for random number generation.

static uint64_t next64() {
  generator *= 6364136223846793005ul;
  generator += 1442695040888963407ul;
  assert(generator);
  return generator;
}

static unsigned next32() { return next64() >> 32; }

// Return a double in the interval [0..1] (both inclusive).

static double next_double() { return next32() / 4294967295.0; }

static unsigned pick_modular(unsigned mod) {
  assert(mod);
  const unsigned tmp = next32();
  const double fraction = tmp / 4294967296.0;
  const unsigned res = mod * fraction;
  assert(res < mod);
  return res;
}

static bool next_bool() { return next32() < 2147483648u; }

/*------------------------------------------------------------------------*/

// Restart by generating new assignment.

static bool satisfied(clause *c) {
  // TODO return 'true' if the clause is satisfied.
  return false;
}

static bool critical(clause *c) {
  int unit = 0;
  // TODO find single satisfied 'unit'.
  // TODO return early with 'false' if double satisfied.
  // TODO do not set 'unit' if all literals are false.
  return unit;
}

static size_t break_value(int lit) {
  assert(values[lit] > 0);
  size_t res = 0;
  // TODO count the number of critical clauses with 'lit'.
  LOG("break-value %zu of literal %s", res, LOG(lit));
  return res;
}

/*------------------------------------------------------------------------*/

static void break_clause(clause *c) {
  LOG(c, "broken");
  // TODO push clause on 'unsatisfied'.
  // TODO remember position of 'c' on 'unsatisfied' stack.
  stats.broken_clauses++;
}

static void make_clause(clause *c) {
  LOG(c, "made");
  // TODO invalidate position in 'unsatisfied'.
  stats.made_clauses++;
}

static bool contains(clause *c, int lit) {
  // TODO check whether 'c' contains 'lit'.
  return false;
}

/*------------------------------------------------------------------------*/

static void make_clauses_along_occurrences(int lit) {
  const auto &occs = occurrences[lit];
  LOG("making clauses with %s along %zu occurrences", LOG(lit), occs.size());
  assert(values[lit] > 0);
  size_t made = 0;
  for (auto c : occs) {
    // TODO early abort is no more unsatisfied clauses left.
    stats.make_visited++;
    // TODO ignore clauses not on unsatisfied stack with invalid position.
    // TODO swap clause at 'c->pos' with last unsatisfied clause.
    // TODO make sure to adjust statistics:
    // 'stats.made_clauses' and 'stats.make_visited'.
    make_clause(c);
    made++;
  }
  LOG("made %zu clauses with flipped %s", made, LOG(lit));
  (void)made;
}

static void make_clauses_along_unsatisfied(int lit) {
  LOG("making clauses with %s along %zu unsatisfied", LOG(lit),
      unsatisfied.size());
  assert(values[lit] > 0);
  size_t made = 0;
  // TODO flush made clauses from 'unsatisfied' directly.
  // TODO make sure to adjust statistics:
  // 'stats.made_clauses' and 'stats.make_visited'.
  LOG("made %zu clauses with flipped %s", made, LOG(lit));
  (void)made;
}

static void make_clauses(int lit) {
  if (occurrences[lit].size() < unsatisfied.size())
    make_clauses_along_occurrences(lit);
  else
    make_clauses_along_unsatisfied(lit);
}

static void break_clauses(int lit) {
  LOG("breaking clauses with %s", LOG(lit));
  assert(values[lit] < 0);
  size_t broken = 0;
  // TODO go over clause with 'lit' that could now be broken.
  // TODO 'stats.break_visited++', 'broken++' appropriately.
  LOG("broken %zu clauses with flipped %s", broken, LOG(lit));
  (void)broken;
}

static void update_minimum() {
  size_t unsatisfied_size = unsatisfied.size();
  if (unsatisfied_size < minimum) {
    minimum = unsatisfied_size;
    minimum_restarts = stats.restarts;
    minimum_flipped = stats.flipped;
    verbose(1,
            "minimum %zu unsatisfied clauses after %zu flipped variables"
            " and %zu restarts",
            minimum, stats.flipped, stats.restarts);
  }
  if (restart_scheduler != always_restart && restart_scheduler != never_restart)
    if (unsatisfied_size < best) {
      best = unsatisfied_size;
      verbose(3,
              "best %zu unsatisfied clauses after %zu flipped variables"
              " and %zu restarts",
              best, stats.flipped, stats.restarts);
    }
}

/*------------------------------------------------------------------------*/

static bool is_time_to_restart() {
  if (restart_scheduler == always_restart)
    return true;
  if (restart_scheduler == never_restart)
    return false;
  if (stats.flipped < next_restart)
    return false;
  if (restart_scheduler == arithmetic_restart)
    ; // TODO update 'restart_interval' arithmetically
  else if (restart_scheduler == geometric_restart)
    ; // TODO update 'restart_interval' geometrically
  else if (restart_scheduler == reluctant_restart) {
    ; // TODO update 'restart_interval' as Knuth using
    ; // 'u = reluctant_state[0], v = reluctant_state[1]
    ; // message("reluctant %" PRIu64 " %" PRIu64 "\n", u, v);
  } else
    assert(restart_scheduler == fixed_restart);
  next_restart = stats.flipped + restart_interval;
  return true;
}

static void restart() {
  LOG("restarting");
  stats.restarts++;
  for (int64_t idx = 1; idx <= variables; idx++) {
    if (forced[idx])
      continue;
    signed char value = next_bool() ? -1 : 1;
    values[idx] = value;
    values[-idx] = -value;
    LOG("assign %" PRId64 " in restart", value < 0 ? -idx : idx);
  }
  for (auto c : unsatisfied)
    c->pos = invalid_position;
  // TODO initialize 'unsatisfied' with falsified clauses
  // (just use 'break_clause' for falsified clause).
  // TODO make sure to increment statistics:
  // 'stats.broken_clauses' and 'stats.break_visited'.
  verbose(2, "%zu clauses broken after restart %zu and %zu flipped",
          unsatisfied.size(), stats.restarts, stats.flipped);
  best = invalid_minimum;
  update_minimum();
}

/*------------------------------------------------------------------------*/

static clause *pick_unsatisfied_clause() {
  size_t pos = 0; // TODO do something better here? Random? Or BFS?
  clause *res = unsatisfied[pos];
  LOG(res, "picked at position %zu", pos);
  return res;
}

/*------------------------------------------------------------------------*/

static void flip_literal(int lit) {
  LOG("flipping %s", LOG(lit));
  assert(!forced[abs(lit)]);
  assert(values[lit] < 0);
  // TODO flip values of lit and -lit.
  stats.flipped++;
  make_clauses(lit);
  break_clauses(-lit);
  update_minimum();
}

/*------------------------------------------------------------------------*/

static int pick_random_falsified_literal() {
  int res = 1;
  // TODO pick random falsified (but not forced) variable.
  // TODO make sure 'res' has 'value[res] < 0'.
  return res;
}

static void random_literal() {
  message("using random literal picking algorithm");
  restart();
  while (!unsatisfied.empty() && stats.flipped < limit)
    if (is_time_to_restart())
      restart();
    else {
      auto lit = pick_random_falsified_literal();
      flip_literal(lit);
    }
}

/*------------------------------------------------------------------------*/

static int pick_random_literal_in_unsatisfied_clause(clause *c) {
  assert(c->size < UINT_MAX);
  const unsigned pos = 0; // TODO Pick random position instead!
  int res = c->literals[pos];
  LOG("random walk picked at position %u literal %s", pos, LOG(res));
  stats.random_walks++;
  return res;
}

static void focused_random_walk() {
  message("using focused random walk algorithm");
  restart();
  while (!unsatisfied.empty() && stats.flipped < limit)
    if (is_time_to_restart())
      restart();
    else {
      auto c = pick_unsatisfied_clause();
      auto lit = pick_random_literal_in_unsatisfied_clause(c);
      flip_literal(lit);
    }
}

/*------------------------------------------------------------------------*/

static std::vector<int> min_break_value_literals;

static int select_literal_in_unsatisfied_clause(clause *c) {
  size_t min_break_value = invalid_break_value;
  // TODO first gather minimum break value literals in
  // 'min_break_value_literals'.
  LOG(c, "minimum break value %zu in", min_break_value);
  if (min_break_value) {
    // TODO with probability 'p < 0.57' pick random literal in 'c'
    // (you can reuse 'pick_random_literal_in_unsatisfied_clause'.
  }
  // TODO otherwise pick random literal in 'min_break_value_literals'.
  const unsigned pos = 0; // TODO do pick a random one!
  int res = 0;            // TODO pick the literal at 'pos'.
  LOG("picked at position %u literal %s with break-value %zu", pos, LOG(res),
      min_break_value);
  return res;
}

static void walksat() {
  message("using WalkSAT algorithm");
  restart();
  while (!unsatisfied.empty() && stats.flipped < limit)
    if (is_time_to_restart())
      restart();
    else {
      auto c = pick_unsatisfied_clause();
      auto lit = select_literal_in_unsatisfied_clause(c);
      flip_literal(lit);
    }
}

/*------------------------------------------------------------------------*/

static int sample_literal_in_unsatisfied_clause(clause *c) {
  return c->literals[0]; // TODO+ implement ProbSAT sampling.
}

static void probsat() {
  message("using ProbSAT algorithm");
  restart();
  while (!unsatisfied.empty() && stats.flipped < limit) {
    auto c = pick_unsatisfied_clause();
    auto lit = sample_literal_in_unsatisfied_clause(c);
    flip_literal(lit);
  }
}

/*------------------------------------------------------------------------*/

// Witness/model printing.

static std::string buffer; // Used to fit 'v' lines into one terminal line.

static void flush_buffer() {
  fputs("v", stdout);
  fputs(buffer.c_str(), stdout);
  fputc('\n', stdout);
  buffer.clear();
}

static void print_value(int lit) {
  char str[32];
  sprintf(str, " %d", lit);
  size_t l = strlen(str);
  if (buffer.size() + l > 74)
    flush_buffer();
  buffer += str;
}

static void print_values() {
  for (int64_t idx = 1; idx <= variables; idx++) {
    auto value = values[idx];
    if (value)
      print_value(value * idx);
  }
  print_value(0);
  if (!buffer.empty())
    flush_buffer();
}

/*------------------------------------------------------------------------*/

// Main solving routine.

static void initialize_seed() {
  if (thank_string) {
    for (auto p = thank_string; *p; p++)
      generator ^= *p, (void)next64();
    verbose(1, "hashed '%s' to seed '%" PRIu64 "'", thank_string, generator);
  }
  message("seed %" PRIu64, generator);
}

static void initialize_restart() {
  base_restart_interval = restart_interval = 100 * (uint64_t)variables;
  if (restart_scheduler == never_restart)
    message("never restart");
  else if (restart_scheduler == always_restart)
    message("always restart");
  else if (restart_scheduler == fixed_restart)
    message("fixed restart interval of %" PRIu64, restart_interval);
  else if (restart_scheduler == reluctant_restart)
    message("reluctant restart interval of %" PRIu64, restart_interval);
  else if (restart_scheduler == geometric_restart)
    message("geometric restart interval of %" PRIu64, restart_interval);
  else
    message("arithmetic restart interval of %" PRIu64, restart_interval);
  next_restart = stats.restarts + restart_interval;
}

#ifndef NDEBUG

static void check_original_clauses_satisfied() {
  size_t start_of_last_clause = 0;
  bool satisfied = false;
  size_t id = 0;
  for (size_t i = 0; i != original_literals.size(); i++) {
    auto lit = original_literals[i];
    if (lit) {
      if (values[lit] > 0)
        satisfied = true;
    } else if (satisfied) {
      start_of_last_clause = i + 1;
      satisfied = false;
      id++;
    } else {
      fprintf(stderr,
              "babywalk: fatal error: "
              "original clause[%zu] at line %zu unsatisfied:\n",
              id + 1, original_lineno[id]);
      for (size_t j = start_of_last_clause; j != i; j++)
        fprintf(stderr, "%d ", original_literals[j]);
      fputs("0\n", stderr);
      fflush(stderr);
      abort();
      exit(1);
    }
  }
}

#endif

static int solve() {
  initialize_seed();
  if (limit == invalid_position)
    message("unlimited number of flipped variables");
  else
    message("limit %" PRIu64 " on number of flipped variables", limit);
  initialize_restart();
  int res = 0;
  if (found_empty_clause) {
    fputs("s UNSATISFIABLE\n", stdout);
    fflush(stdout);
    res = 20;
  } else {
    if (algorithm == random_algorithm)
      random_literal();
    else if (algorithm == focused_algorithm)
      focused_random_walk();
    else if (algorithm == walksat_algorithm)
      walksat();
    else {
      assert(algorithm == probsat_algorithm);
      probsat();
    }
    message("reached minimum %zu unsatisfied clauses after "
            "%" PRIu64 " flipped variables and %" PRIu64 " restarts",
            minimum, minimum_flipped, minimum_restarts);
    if (!terminate && unsatisfied.empty()) {
#ifndef NDEBUG
      check_original_clauses_satisfied();
#endif
      fputs("s SATISFIABLE\n", stdout);
      fflush(stdout);
      if (!do_not_print_model)
        print_values();
      res = 10;
    } else {
      if (terminate)
        printf("c terminated by %s\n", describe_signal(termination_signal));
      fputs("s UNKNOWN\n", stdout);
      fflush(stdout);
      res = 0;
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

// Common statistics functions.

static double average(double a, double b) { return b ? a / b : 0; }
static double percent(double a, double b) { return average(100 * a, b); }

// Report statistics.

static void report() {
  if (verbosity < 0)
    return;
  double t = time();
  printf("c %-21s %13" PRIu64 " %14.2f flipped/restart\n",
         "restarts:", stats.restarts, average(stats.flipped, stats.restarts));
  printf("c %-21s %13" PRIu64 " %14.2f per second\n",
         "flipped-variables:", stats.flipped, average(stats.flipped, t));
  printf("c %-21s %13" PRIu64 " %14.2f %% flipped\n",
         "random-walks:", stats.random_walks,
         percent(stats.random_walks, stats.flipped));
  printf("c %-21s %13" PRIu64 " %14.2f per flip\n",
         "made-clauses:", stats.made_clauses,
         average(stats.made_clauses, stats.flipped));
  printf("c %-21s %13" PRIu64 " %14.2f per flip\n",
         "make-visited:", stats.make_visited,
         average(stats.make_visited, stats.flipped));
  printf("c %-21s %13" PRIu64 " %14.2f per flip\n",
         "broken-clauses:", stats.broken_clauses,
         average(stats.broken_clauses, stats.flipped));
  printf("c %-21s %13" PRIu64 " %14.2f per flip\n",
         "break-visited:", stats.break_visited,
         average(stats.break_visited, stats.flipped));
  printf("c %-21s %28.2f seconds\n", "process-time:", t);
  fflush(stdout);
}

/*------------------------------------------------------------------------*/

// Parse command line options.

template <class T> static bool parse_unsigned(const char *str, T &res) {
  const T max = ~(T)0;
  if (!isdigit(*str))
    return false;
  res = *str - '0';
  int ch;
  for (const char *p = str + 1; (ch = *p); p++) {
    if (!isdigit(ch))
      return false;
    if (max / 10 < res)
      return false;
    res *= 10;
    const int digit = ch - '0';
    if (!res && !digit)
      return false;
    if (max - digit < res)
      return false;
    res += digit;
  }
  return true;
}

static void check_only_one_restart_scheduler(const char *prev,
                                             const char *arg) {
  if (prev)
    die("can not combine restart scheduler '%s' and '%s'", prev, arg);
}

static void options(int argc, char **argv) {
  const char *seed_string = 0;
  const char *limit_string = 0;
  const char *restart_string = 0;
  const char *timeout_string = 0;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h")) {
      fputs(usage, stdout);
      exit(0);
    } else if (!strcmp(arg, "-v"))
      verbosity += (verbosity != INT_MAX);
    else if (!strcmp(arg, "-q"))
      verbosity = -1;
    else if (!strcmp(arg, "-f")) {
      if (++i == argc)
        die("argument to '-f' missing (try '-h')");
      arg = argv[i];
      if (limit_string)
        die("multiple '-f' options ('-f %s' and '-f %s')", limit_string, arg);
      if (!parse_unsigned(arg, limit))
        die("invalid argument in '-f %s'", arg);
      limit_string = arg;
    } else if (!strcmp(arg, "-s")) {
      if (++i == argc)
        die("argument to '-s' missing (try '-h')");
      arg = argv[i];
      if (seed_string)
        die("multiple '-s' options ('-s %s' and '-s %s')", seed_string, arg);
      if (thank_string)
        die("'--thank %s' and '-s %s'", thank_string, arg);
      if (!parse_unsigned(arg, generator))
        die("invalid argument in '-s %s'", arg);
      seed_string = arg;
    } else if (!strcmp(arg, "--thank")) {
      if (++i == argc)
        die("argument to '--thank' missing (try '-h')");
      arg = argv[i];
      if (thank_string)
        die("multiple '--thank' options ('--thank %s' and '--thank %s')",
            thank_string, arg);
      if (seed_string)
        die("'-s %s' and '--thank %s'", seed_string, arg);
      thank_string = arg;
    } else if (!strcmp(arg, "-t")) {
      if (++i == argc)
        die("argument to '-t' missing (try '-h')");
      if (timeout_string)
        die("multiple '-t' options ('-t %s' and '-t %s')", timeout_string, arg);
      arg = argv[i];
      unsigned seconds;
      if (!parse_unsigned(arg, seconds))
        die("invalid argument in '-t %s'", arg);
      timeout_string = arg;
      (void)signal(SIGALRM, catch_signal);
      (void)alarm(seconds);
    } else if (!strcmp(arg, "-l"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      die("invalid option '-l' (compiled without logging support)");
#endif
    else if (!strcmp(arg, "-n"))
      do_not_print_model = true;
    else if (!strcmp(arg, "--random"))
      algorithm = random_algorithm;
    else if (!strcmp(arg, "--focused"))
      algorithm = focused_algorithm;
    else if (!strcmp(arg, "--probsat"))
      algorithm = probsat_algorithm;
    else if (!strcmp(arg, "--walksat"))
      algorithm = walksat_algorithm;
    else if (!strcmp(arg, "--always-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = always_restart;
      restart_string = arg;
    } else if (!strcmp(arg, "--never-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = never_restart;
      restart_string = arg;
    } else if (!strcmp(arg, "--fixed-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = fixed_restart;
      restart_string = arg;
    } else if (!strcmp(arg, "--reluctant-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = reluctant_restart;
      restart_string = arg;
    } else if (!strcmp(arg, "--geometric-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = geometric_restart;
      restart_string = arg;
    } else if (!strcmp(arg, "--arithmetic-restart")) {
      check_only_one_restart_scheduler(restart_string, arg);
      restart_scheduler = arithmetic_restart;
      restart_string = arg;
    } else if (arg[0] == '-' && arg[1])
      die("invalid option '%s' (try '-h')", arg);
    else if (!input_path)
      input_path = arg;
    else
      die("too many file arguments '%s' and '%s'", input_path, arg);
  }
}

/*------------------------------------------------------------------------*/

static void banner() { message("BabyWalk Local Search SAT Solver"); }

static void goodbye(int res) {
  if (thank_string)
    message("%ssolved thanks to '%s'", res ? "" : "un", thank_string);
  message("exit %d", res);
}

/*------------------------------------------------------------------------*/

int main(int argc, char **argv) {
  options(argc, argv);
  banner();
  init();
  parse();
  simplify();
  int res = solve();
  report();
  reset();
  goodbye(res);
  return res;
}
