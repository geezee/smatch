#!/bin/bash

PASS=0
FAIL=0

pass() {
  echo "$2" | ./target/release/smatch "$1" > /dev/null
  if [ $? -eq 0 ]; then echo "[PASS] $1 :: $2"; PASS=$(expr $PASS + 1)
  else printf "\e[1;31m[FAIL]\e[0m $1 :: $2\n"; FAIL=$(expr $FAIL + 1)
  fi
}

fail() {
  echo "$2" | ./target/release/smatch "$1" > /dev/null
  if [ $? -eq 1 ]; then echo "[PASS] $1 !! $2"; PASS=$(expr $PASS + 1)
  else printf "\e[1;31m[FAIL]\e[0m $1 !! $2\n"; FAIL=$(expr $FAIL + 1)
  fi
}

finish() {
  echo "Failed: $FAIL"
  echo "Passed: $PASS"
  echo $(expr $PASS "*" 100 "/" $(expr $PASS + $FAIL)) "%"

  if [ $FAIL -gt 0 ]; then exit 1
  else exit 0
  fi
}



pass '@atom'   'hello'
pass '@atom'   '123'
pass '@atom'   '"hello world"'
pass '@atom'   '42.58'
pass '@atom'   '|this is an identifier|'
fail '@atom'   '()'

pass '@_'      'hello'
pass '@_'      '()'
pass '@_'      '(set-info :status sat)'
pass '@_'      '(declare-fun foo (T T) (Vec T))'

pass 'hello'   'hello'
fail 'hello'   'world'
fail 'hello'   '()'
fail 'hello'   '(declare-fun hello (T T) (Vec T))'

pass '(@re "^declare-.*$")'   'declare-fun'
fail '(@re "^declare-.*$")'   '(declare-fun foo)'
pass '(@re ".*\(.*\).*")'     '|(declare-fun foo)|'
pass '(@re """")'             '|a "quoted" identifier|'
pass '(@re "a ""quote")'      '|a "quoted" identifier|'

pass '()'                '()'
fail '()'                '_'
fail '()'                '(assert true)'
pass '(@atom @_)'        '(assert true)'
pass '(@atom @_)'        '(assert (forall ((x nat)) true))'
fail '(@atom @_)'        '_'
fail '(@atom @_)'        '(assert true true)'
pass '(@atom @_ done)'   '(assert (f 0) done)'
fail '(@atom @_ done)'   '(assert (f 0) exit)'

pass '(@or @atom ())'    '_'
pass '(@or @atom ())'    '()'
fail '(@or @atom ())'    '(declare-fun foo () Bool)'
pass '(@or @atom () @_)' '(declare-fun foo () Bool)'
pass '((@or (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(import-fun foo)'
pass '((@or (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-var foo)'

fail '(@and @atom ())'   '_'
fail '(@and @atom ())'   '()'
fail '(@and @atom ())'   '(declare-fun foo () Bool)'
pass '(@and (@re "^.*fun$") (@re "^de.*$"))'  'declare-fun'
pass '(@and (@re "^.*fun$") (@re "^de.*$"))'  'define-fun'
pass '((@and (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-fun foo)'
fail '((@and (@re "^.*fun$") (@re "^de.*$")) @atom)'  '(define-var foo)'

pass '(@* @atom)'        '_'
pass '(@* @atom)'        '()'
pass '(@* @atom)'        '(hello)'
pass '(@* @atom)'        '(hello world)'
pass '(@* @atom)'        '(hello world !)'
fail '(@* @atom)'        '(hello world ())'
fail '(@* @atom)'        '(hello world (!))'

pass '(@+ @atom)'        '_'
fail '(@+ @atom)'        '()'
pass '(@+ @atom)'        '(hello world !)'
fail '(@+ @atom)'        '(hello world ())'

pass '(@? @atom)'        '()'
pass '(@? @atom)'        'hello'
pass '(@? @atom)'        '(hello)'
fail '(@? @atom)'        '((hello))'
fail '(@? @atom)'        '(hello world)'
fail '(@? @atom)'        '((hello) world)'

pass '(@less 0 @atom)'   '()'
fail '(@less 0 @atom)'   'hello'
fail '(@less 0 @atom)'   '(hello world)'
pass '(@less 1 @atom)'   '()'
pass '(@less 1 @atom)'   'hello'
pass '(@less 1 @atom)'   '(hello)'
fail '(@less 1 @atom)'   '(hello world)'
pass '(@less 2 @atom)'   '(hello world)'
fail '(@less 2 @atom)'   '(hello world !)'

fail '(@more 3 @atom)'   '()'
fail '(@more 3 @atom)'   '_'
fail '(@more 3 @atom)'   '(_)'
fail '(@more 3 @atom)'   '(hello world)'
fail '(@more 3 @atom)'   '((hello) world !)'
pass '(@more 3 @atom)'   '(hello world !)'
pass '(@more 3 @atom)'   '(hello world ! !)'

fail '(@between 2 4 @atom)'   '()'
fail '(@between 2 4 @atom)'   '_'
fail '(@between 2 4 @atom)'   '(_)'
pass '(@between 2 4 @atom)'   '(hello world)'
pass '(@between 2 4 @atom)'   '(hello world !)'
pass '(@between 2 4 @atom)'   '(hello world ! !)'
fail '(@between 2 4 @atom)'   '(hello world ! ! !)'
fail '(@between 2 4 @atom)'   '(hello world (! !) !)'

pass '(@depth (@* @atom))'  '_'
pass '(@depth (@* @atom))'  '(_)'
fail '(@depth (@* @atom))'  '()'
pass '(@depth (@* @atom))'  '(() _ ())'
pass '(@depth (@* @atom))'  '(() () (_))'
fail '(@depth (@more 2 @atom))'  '(() () _)'
pass '(@depth (@more 2 @atom))'  '(() () (_))'
pass '(@depth (@more 2 (= @atom @_)))'  '(assert (and (= v (f 10)) true))'
fail '(@depth (@more 2 (= @atom @_)))'  '(assert (= v (f 10)))'

fail '(@or (@depth (@* true)) (@depth (@more 4 (= @_ @_))) (assert @atom))' \
     '(assert (or (= 3 4) false))'

finish;
