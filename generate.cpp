// clang-format off

static const char *usage =

"usage: generate [ <option> ... ] [ <variables> [ <ratio> ] ]\n"
"\n"
"where '<option>' is one of the following\n"
"\n"
"  -h          print this command line option summary\n"
"  -p          plant a random solution (forces satisfiability)\n"
"  -s <seed>   set random number generator seed (default random)\n"
"  -k <length> set the uniform size of clauses (default '3')\n"
"\n"
"and '<variables>' is the number of variables (default '20').  If specified\n"
"'<ratio>' denotes the clause variable ratio (default is '4.267' for 'k=3').\n"
"The tool generates a random k-SAT CNF with 'k' either specified by the '-k'\n"
"option or '3' per default.  The '<seed>' if specified is the seed used for\n"
"the random number generator, which otherwise is determined pseudo-randomly\n"
"using the current system time and the process identifier into account.\n"
"\n"
"The number of variables can not be larger than 'INT_MAX' (2^31 - 1) and\n"
"the length of clauses '<length>' has to be in the range from '2' to '50'.\n"
"The clause-variable ratio can have 16 non-fractional and 3 fractional bits\n"
"(actually the mantissa has to be smaller equal to '180401726631072641').\n"

;

// clang-format on

#include <cassert>
#include <cctype>
#include <cinttypes>
#include <climits>
#include <cmath>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

extern "C" {
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
};

static unsigned length = 3;
static unsigned variables = 20;

static double ratio;
static uint64_t clauses;
static uint64_t generator;

static unsigned *indices;
static bool *picked;
static bool *signs;

static bool *planted;
static bool plant;

/*------------------------------------------------------------------------*/

// These are from the thesis of Adrian Balint who references in turn:
//
//   Stephan Mertens, Marc Mézard, and Riccardo Zecchina.
//   Threshold Values of Random K-SAT from the Cavity Method.
//   Random Struct. Algorithms, 28(3):340–373, 2006.
//
static double ratios[][2] = {
    {3, 4.267}, {4, 9.931}, {5, 21.117}, {6, 43.37}, {7, 87.79},
};

// This is a manual fit of the above values to a simple exponential.
//
static double fit() {
  return 0.001 * (uint64_t)(pow(2.15, length - 1.1) * 1000);
}

/*------------------------------------------------------------------------*/

static void die(const char *, ...) __attribute__((format(printf, 1, 2)));

static void die(const char *fmt, ...) {
  fputs("generate: error: ", stderr);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  exit(1);
}

/*------------------------------------------------------------------------*/

static uint64_t next64() {
  generator *= 6364136223846793005ul;
  generator += 1442695040888963407ul;
  return generator;
}

static unsigned next32() { return next64() >> 32; }

static unsigned pick_variable() {
  unsigned res = variables * (next32() / 4294967296.0);
  assert(res < variables);
  return res;
}

static bool pick_sign() { return next32() < 2147483648u; }

static unsigned pick_position() {
  unsigned res = length * (next32() / 4294967296.0);
  assert(res < length);
  return res;
}

static void hash(uint64_t x) {
  generator ^= x;
  (void)next64();
}

/*------------------------------------------------------------------------*/

template <class T> static bool parse_unsigned(const char *str, T &res) {
  if (!isdigit(*str))
    return false;
  res = *str - '0';
  const T max = ~(T)0;
  for (const char *p = str + 1; *p; p++) {
    if (!isdigit(*p))
      return false;
    if (*p == '0' && !res)
      return false;
    if (max / 10 < res)
      return false;
    res *= 10;
    unsigned digit = *p - '0';
    if (max - digit < res)
      return false;
    res += digit;
  }
  return true;
}

static bool parse_double(const char *str, double &res) {
  if (!isdigit(*str))
    return false;
  const unsigned max_non_fractional_digits = 16;
  unsigned non_fractional_digits = 0;
  uint64_t mantissa = *str - '0';
  const char *p = str + 1;
  char ch;
  while ((ch = *p++) && ch != '.') {
    if (!isdigit(ch))
      return false;
    if (++non_fractional_digits > max_non_fractional_digits)
      return false;
    mantissa *= 10;
    unsigned digit = ch - '0';
    mantissa += digit;
  }
  res = mantissa;
  if (ch) {
    assert(ch == '.');
    const unsigned max_fractional_digits = 3;
    unsigned fractional_digits = 0;
    double exp = 1;
    while ((ch = *p++)) {
      if (!isdigit(ch))
        return false;
      if (++fractional_digits > max_fractional_digits)
        return false;
      exp /= 10;
      unsigned digit = ch - '0';
      res += digit * exp;
    }
  }
  return res <= 180401726631072641.0; // The 'fit' ratio for 'k=50'.
}

/*------------------------------------------------------------------------*/

int main(int argc, char **argv) {
  const char *variables_parsed = 0;
  const char *ratio_parsed = 0;
  bool length_parsed = false;
  bool seed_parsed = false;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h")) {
      fputs(usage, stdout);
      return 0;
    } else if (!strcmp(arg, "-p")) {
      if (plant)
        die("multiple '%s' options", arg);
      plant = true;
    } else if (!strcmp(arg, "-s")) {
      if (++i == argc)
        die("argument to '%s' missing (try '-h')", arg);
      if (seed_parsed)
        die("multiple '%s' options", arg);
      if (!parse_unsigned(argv[i], generator))
        die("invalid argument in '%s %s'", arg, argv[i]);
      seed_parsed = true;
    } else if (!strcmp(arg, "-k")) {
      if (++i == argc)
        die("argument to '%s' missing (try '-h')", arg);
      if (length_parsed)
        die("multiple '%s' options", arg);
      if (!parse_unsigned(argv[i], length) || length < 2 || length > 50)
        die("invalid argument in '%s %s' (try '-h')", arg, argv[i]);
      length_parsed = true;
    } else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (!variables_parsed) {
      if (!parse_unsigned(arg, variables) || variables > (unsigned)INT_MAX)
        die("invalid number of variables '%s' (try '-h')", arg);
      variables_parsed = arg;
    } else if (!ratio_parsed) {
      if (!parse_double(arg, ratio))
        die("invalid clause-variable ratio '%s' (try '-h'", arg);
      ratio_parsed = arg;
    } else
      die("too many arguments '%s', '%s', and '%s' (try '-h')",
          variables_parsed, ratio_parsed, arg);
  }
  if (!seed_parsed)
    hash(getpid()), hash(clock());
  if (!ratio_parsed) {
    for (auto pair : ratios)
      if (pair[0] == length)
        ratio = pair[1];
    if (!ratio)
      ratio = fit();
  }
  clauses = variables * ratio + 0.5;
  indices = new unsigned[length];
  signs = new bool[length];
  picked = new bool[variables];
  printf("c generate%s -k %u -s %" PRIu64 " %u %.3f\n", plant ? " -p" : "",
         length, generator, variables, ratio);
  printf("p cnf %u %" PRIu64 "\n", variables, clauses);
  if (plant) {
    planted = new bool[variables];
    for (unsigned idx = 0; idx != variables; idx++)
      planted[idx] = pick_sign();
  }
  for (uint64_t i = 0; i != clauses; i++) {
    for (unsigned j = 0; j != length; j++) {
      unsigned idx;
      while (picked[idx = pick_variable()])
        ;
      picked[idx] = true;
      indices[j] = idx;
    }
    for (unsigned j = 0; j != length; j++)
      signs[j] = pick_sign();
    if (plant) {
      bool satisfied = false;
      for (unsigned j = 0; !satisfied && j != length; j++) {
        bool sign = signs[j];
        unsigned idx = indices[j];
        satisfied = (sign == planted[idx]);
      }
      if (!satisfied) {
        unsigned pos = pick_position();
        signs[pos] ^= 1;
      }
    }
    for (unsigned j = 0; j != length; j++) {
      bool sign = signs[j];
      unsigned idx = indices[j];
      assert(idx < (unsigned)INT_MAX);
      int lit = (sign ? -1 : 1) * (idx + 1);
      printf("%d ", lit);
    }
    fputs("0\n", stdout);
    for (unsigned j = 0; j != length; j++)
      picked[indices[j]] = 0;
  }
  if (plant)
    delete[] planted;
  delete[] indices;
  delete[] picked;
  delete[] signs;
  return 0;
}
