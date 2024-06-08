#!/bin/bash

PASS=0
FAIL=0

assert_true() {
  ./target/release/smatch "$1" <(echo "$2") > /dev/null
  if [ $? -eq 0 ]; then
    echo "[PASS] $1 :: $2"
    PASS=$(expr $PASS + 1)
  else
    echo "[FAIL] $1 :: $2"
    FAIL=$(expr $FAIL + 1)
  fi
}

assert_false() {
  ./target/release/smatch "$1" <(echo "$2") > /dev/null
  if [ $? -gt 0 ]; then
    echo "[PASS] $1 !! $2"
    PASS=$(expr $PASS + 1)
  else
    echo "[FAIL] $1 !! $2"
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



assert_true  '@atom'   'hello';
assert_true  '@atom'   '123';
assert_true  '@atom'   '"hello world"';
assert_true  '@atom'   '42.58';
assert_true  '@atom'   '|this is an identifier|';
assert_false '@atom'   '()';

assert_true  '@_'   'hello';
assert_true  '@_'   '()';
assert_true  '@_'   '(set-info :status sat)';
assert_true  '@_'   '(declare-fun foo (T T) (Vec T))';

assert_true  'hello'   'hello';
assert_false 'hello'   'world';
assert_false 'hello'   '()';
assert_false 'hello'   '(declare-fun hello (T T) (Vec T))';

assert_true  '(@re "^declare-.*$")'   'declare-fun'
assert_false '(@re "^declare-.*$")'   '(declare-fun foo)'
assert_true  '(@re ".*\(.*\).*")'     '|(declare-fun foo)|'

assert_true  '(@atom @_)'        '(assert true)'
assert_true  '(@atom @_)'        '(assert (forall ((x nat)) true))'
assert_false '(@atom @_)'        '_'
assert_false '(@atom @_)'        '(assert true true)'
assert_true  '(@atom @_ done)'   '(assert (f 0) done)'
assert_false '(@atom @_ done)'   '(assert (f 0) exit)'

finish;
