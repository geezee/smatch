;;; smatch patterns are themselves expressed using s-expressions
;;; so we can describe the smatch patterns using smatch patterns!
;;;
;;; this demonstrates the following:
;;;   1. smatch patterns are pretty expressive,
;;;   2. they can be pretty large and complicated,
;;;   3. pattern matching smatch patterns using this file is fast enough.
;;;
;;; this file is used in the test file like so:
;;; ./test.sh reads its own source code, compiles a list of all the patterns used in the test file,
;;; then checks that all these pattern match against this file.
;;;
;;; moreover this file itself is an s-expression file, so we can pattern match this file on itself:
;;;   smatch -f smatch-syntax.lisp smatch-syntax.lisp
;;; and it must succeed!
;;;
;;; one small caveat is that smatch patterns cannot match only numbers, or only strings, or only
;;; identifiers. Thus the grammar defined here cannot represent grammar rules that require having
;;; numbers (e.g. arguments to @between) or only strings (e.g. arguments to @re)


(@let (@wildcard         (@re "^@_$"))

      (@_atom            (@re "^@atom$"))

      (@literal          (@re "^[^@].*$"))

                         ; as there are no special syntax to match string atoms, but rather any atom
                         ; this check is not entirely correct. It allows `@re 1` for example
      (@_re              ((@re "^@re$") @atom))

      (@_and             ((@re "^@and$") (@+ @smatch-pattern)))

      (@_or              ((@re "^@or$") (@+ @smatch-pattern)))

      (@_depth           ((@re "^@depth") @repeat))

      (@repeat           (@or ((@re "^@\*$") @smatch-pattern)
                              ((@re "^@\?$") @smatch-pattern)
                              ((@re "^@\+$") @smatch-pattern)
                              ((@re "^@less$") @atom @smatch-pattern) ; can't enforce args to be integers
                              ((@re "^@more$") @atom @smatch-pattern) ; ditto
                              ((@re "^@between$") @atom @atom @smatch-pattern))) ; ditto

      (@var              (@and (@re "^@(_.+|[^_].*)$")
                               ; following is a complicated regex to say anything but "@atom"
                               ; the regexes in [[@valid-fun-symb]] are in the same spirit
                               ; This python function takes a string and outputs a regex like this one:
                               ; ```
                               ; def regex_not_word(word):
                               ;     result = []
                               ;     for i in range(0, len(word)):
                               ;         if i > 0:
                               ;             result.append(word[0:i])
                               ;         result.append(word[0:i] + "[^" + word[i] + "].*")
                               ;     result.append(word + ".+")
                               ;     return "^(" + "|".join(result) +")$"
                               ; ```
                               (@re "^@([^a].*|a|a[^t].*|at|at[^o].*|ato|ato[^m].*|atom.+)$")))

      (@_let             ((@re "^@let$") (@* (@var @smatch-pattern)) @smatch-pattern))

      (@list             (@or ()
                              (@valid-fun-symb (@* @smatch-pattern))
                              ((@smatch-pattern) (@* @smatch-pattern))
                              ))

      (@valid-fun-symb  (@and
                          (@re "^([^@].*|@|@[^r].*|@r|@r[^e].*|@re.+)$")
                          (@re "^([^@].*|@|@[^d].*|@d|@d[^e].*|@de|@de[^p].*|@dep|@dep[^t].*|@dept|@dept[^h].*|@depth.+)$")
                          (@re "^([^@].*|@|@[^o].*|@o|@o[^r].*|@or.+)$")
                          (@re "^([^@].*|@|@[^a].*|@a|@a[^n].*|@an|@an[^d].*|@and.+)$")
                          (@re "^([^@].*|@|@[^l].*|@l|@l[^e].*|@le|@le[^t].*|@let.+)$")
                          (@re "^([^@].*|@|@[^*].*|@*.+)$")
                          (@re "^([^@].*|@|@[^+].*|@+.+)$")
                          (@re "^([^@].*|@|@[^?].*|@?.+)$")
                          (@re "^([^@].*|@|@[^l].*|@l|@l[^e].*|@le|@le[^s].*|@les|@les[^s].*|@less.+)$")
                          (@re "^([^@].*|@|@[^m].*|@m|@m[^o].*|@mo|@mo[^r].*|@mor|@mor[^e].*|@more.+)$")
                          (@re "^([^@].*|@|@[^b].*|@b|@b[^e].*|@be|@be[^t].*|@bet|@bet[^w].*|@betw|@betw[^e].*|@betwe|@betwe[^e].*|@betwee|@betwee[^n].*|@between.+)$")))

      (@smatch-pattern   (@or @wildcard
                              @_atom
                              @literal
                              @var
                              @_re
                              @_and
                              @_or
                              @repeat
                              @_depth
                              @_let
                              @list))

      @smatch-pattern)
