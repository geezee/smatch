#!/bin/bash

PASS=0
FAIL=0

assert_true() {
  ./target/release/smatch $1 <(echo $2) > /dev/null
  if [ $? -eq 0 ]; then
    echo "[PASS] $1: $2"
    PASS=$(expr $PASS + 1)
  else
    echo "[FAIL] $1: $2"
    FAIL=$(expr $FAIL + 1)
  fi
}

assert_false() {
  ./target/release/smatch $1 <(echo $2) > /dev/null
  if [ $? -gt 0 ]; then
    echo "[PASS] $1: $2"
    PASS=$(expr $PASS + 1)
  else
    echo "[FAIL] $1: $2"
    FAIL=$(expr $FAIL + 1)
  fi
}

finish() {
  echo "Failed: $FAIL"
  echo "Passed: $PASS"
  echo $(expr $PASS "*" 100 "/" $(expr $PASS + $FAIL)) "%"

  if [ $FAIL -gt 0 ]; then
    exit 1
  else
    exit 0
  fi
}



assert_true  "@atom" "hello";
assert_false "@atom" "()";


finish;
