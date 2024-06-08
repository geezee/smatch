#!/bin/bash

PASS=0
FAIL=0

assert_true() {
  ./target/release/smatch "$1" <(echo "$2") > /dev/null
  if [ $? -eq 0 ]; then
    echo "[PASS] $1 :: $2"
    PASS=$(expr $PASS + 1)
  else
    printf "\e[1;31m[FAIL]\e[0m $1 :: $2\n"
    FAIL=$(expr $FAIL + 1)
  fi
}

assert_false() {
  ./target/release/smatch "$1" <(echo "$2") > /dev/null
  if [ $? -eq 1 ]; then
    echo "[PASS] $1 !! $2"
    PASS=$(expr $PASS + 1)
  else
    printf "\e[1;31m[FAIL]\e[0m $1 !! $2\n"
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

assert_true  '@_'      'hello';
assert_true  '@_'      '()';
assert_true  '@_'      '(set-info :status sat)';
assert_true  '@_'      '(declare-fun foo (T T) (Vec T))';

assert_true  'hello'   'hello';
assert_false 'hello'   'world';
assert_false 'hello'   '()';
assert_false 'hello'   '(declare-fun hello (T T) (Vec T))';

assert_true  '(@re "^declare-.*$")'   'declare-fun'
assert_false '(@re "^declare-.*$")'   '(declare-fun foo)'
assert_true  '(@re ".*\(.*\).*")'     '|(declare-fun foo)|'

assert_true  '()'                '()'
assert_false '()'                '_'
assert_false '()'                '(assert true)'
assert_true  '(@atom @_)'        '(assert true)'
assert_true  '(@atom @_)'        '(assert (forall ((x nat)) true))'
assert_false '(@atom @_)'        '_'
assert_false '(@atom @_)'        '(assert true true)'
assert_true  '(@atom @_ done)'   '(assert (f 0) done)'
assert_false '(@atom @_ done)'   '(assert (f 0) exit)'

assert_true  '(@or @atom ())'    '_'
assert_true  '(@or @atom ())'    '()'
assert_false '(@or @atom ())'    '(declare-fun foo () Bool)'
assert_true  '(@or @atom () @_)' '(declare-fun foo () Bool)'
assert_true  '((@or (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(import-fun foo)'
assert_true  '((@or (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-var foo)'

assert_false '(@and @atom ())'   '_'
assert_false '(@and @atom ())'   '()'
assert_false '(@and @atom ())'   '(declare-fun foo () Bool)'
assert_true  '(@and (@re "^.*fun$") (@re "^de.*$"))'  'declare-fun'
assert_true  '(@and (@re "^.*fun$") (@re "^de.*$"))'  'define-fun'
assert_true  '((@and (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-fun foo)'
assert_false '((@and (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-var foo)'

assert_true  '(@* @atom)'        '_'
assert_true  '(@* @atom)'        '()'
assert_true  '(@* @atom)'        '(hello)'
assert_true  '(@* @atom)'        '(hello world)'
assert_true  '(@* @atom)'        '(hello world !)'
assert_false '(@* @atom)'        '(hello world ())'
assert_false '(@* @atom)'        '(hello world (!))'

assert_true  '(@+ @atom)'        '_'
assert_false '(@+ @atom)'        '()'
assert_true  '(@+ @atom)'        '(hello world !)'
assert_false '(@+ @atom)'        '(hello world ())'

assert_true  '(@? @atom)'        '()'
assert_true  '(@? @atom)'        'hello'
assert_true  '(@? @atom)'        '(hello)'
assert_true  '(@? @atom)'        '((hello))'
assert_false '(@? @atom)'        '(hello world)'
assert_false '(@? @atom)'        '((hello) world)'

assert_true  '(@less 0 @atom)'   '()'
assert_false '(@less 0 @atom)'   'hello'
assert_false '(@less 0 @atom)'   '(hello world)'
assert_true  '(@less 1 @atom)'   '()'
assert_true  '(@less 1 @atom)'   'hello'
assert_true  '(@less 1 @atom)'   '(hello)'
assert_false '(@less 1 @atom)'   '(hello world)'
assert_true  '(@less 2 @atom)'   '(hello world)'
assert_false '(@less 2 @atom)'   '(hello world !)'

assert_false '(@more 3 @atom)'   '()'
assert_false '(@more 3 @atom)'   '_'
assert_false '(@more 3 @atom)'   '(_)'
assert_false '(@more 3 @atom)'   '(hello world)'
assert_false '(@more 3 @atom)'   '((hello) world !)'
assert_true  '(@more 3 @atom)'   '(hello world !)'
assert_true  '(@more 3 @atom)'   '(hello world ! !)'

assert_false '(@between 2 4 @atom)'   '()'
assert_false '(@between 2 4 @atom)'   '_'
assert_false '(@between 2 4 @atom)'   '(_)'
assert_true  '(@between 2 4 @atom)'   '(hello world)'
assert_true  '(@between 2 4 @atom)'   '(hello world !)'
assert_true  '(@between 2 4 @atom)'   '(hello world ! !)'
assert_false '(@between 2 4 @atom)'   '(hello world ! ! !)'
assert_false '(@between 2 4 @atom)'   '(hello world (! !) !)'

assert_true  '(@depth (@* @atom))'  '_'
assert_true  '(@depth (@* @atom))'  '(_)'
assert_false '(@depth (@* @atom))'  '()'
assert_true  '(@depth (@* @atom))'  '(() _ ())'
assert_true  '(@depth (@* @atom))'  '(() () (_))'
assert_false '(@depth (@more 2 @atom))'  '(() () _)'
assert_true  '(@depth (@more 2 @atom))'  '(() () (_))'
assert_true  '(@depth (@more 2 (= @atom @_)))'  '(assert (and (= v (f 10)) true))'
assert_false '(@depth (@more 2 (= @atom @_)))'  '(assert (= v (f 10)))'

assert_false '(@or (@depth (@* true)) (@depth (@more 4 (= @_ @_))) (assert @atom))' \
             '(assert (or (= 3 4) false))'

finish;
