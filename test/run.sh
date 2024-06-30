#!/bin/sh

die () {
  echo "run.sh: error; $*" 1>&2
  exit 1
}

cd `dirname $0`/..

for need in babywalk checkmodel
do
  [ -f $need ] || die "could not find '$need' (build first)"
done

run () {
  name=$2
  expected=$1
  dir=test
  cnf=$dir/$name.cnf
  [ -f $cnf ] || die "could not find '$cnf'"
  log=$dir/$name.log
  err=$dir/$name.err
  chm=$dir/$name.chm
  rm -f $log $err $chm
  echo "./babywalk $cnf $out"
  ./babywalk $cnf 1>$log 2>$err
  status=$?
  [ $status = $expected ] || \
    die "simplification failed:" \
        "exit status '$status' but expected '$expected'" \
	"\n(see '$log' and '$err' for more information)"
  if [ $expected = 10 ]
  then
    ./checkmodel $cnf $log 1>$chm 2>>$err
    status=$?
    [ $status = 0 ] || \
    die "model checking failed:" \
        "exit status '$status' but expected '0'" \
        "\n(see '$chm' and '$err' for more information)"
  fi
}

run 10 true
run 20 false

run 10 trivial
run 10 simp

run 20 unit1
run 20 unit2
run 20 unit3
run 20 unit4
run 20 unit5

run 10 prime4
run 10 prime9
run 10 prime25
run 10 prime49
#run 10 prime121
#run 10 prime169

run 10 sqrt2809
run 10 sqrt3481
#run 10 sqrt3721
#run 10 sqrt4489
#run 10 sqrt5041
#run 10 sqrt5329
