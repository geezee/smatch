# Wildcard

The wildcard `@_` matches against any S-expr

```
smatch @_ <(printf "hello \n world \n") # 2 matches
smatch @_ <(printf "(hello world)\n")   # 1 match
smatch @_ <(printf "()\n")              # 1 match
```

# Atom Wildcard

The atom wildcard `@atom` matches only against atoms

```
smatch @atom <(printf "hello \n world \n") # 2 matches
smatch @atom <(printf "()\n")              # 0 matches
smatch @atom <(printf "(hello world)")     # 0 matches
```

# Literal Atoms

A literal atom matches only against the same literal

```
smatch hello <(printf "hello \n world \n") # 1 match
smatch hello <(printf "world\n")           # 0 match
smatch hello <(printf "(hello world)")     # 0 match
```

# Regular Expression Identifier

An identifier can be matched against with a regular expression but making that regular expression a
string and surrounding it with `@re`

```
smatch '(@re "^declare-.*")' <(printf "declare-fun \n set-info \n declare-sort") # 2 matchs
```

# List

A list matches a list, if no repeats are used then the list pattern matches a list term if and only
if their length match and the members match pairwise.

```
smatch '((@re "^declare-.*") @atom @_ @atom)' \
       <(printf "(declare-fun hello (U U) U)  \
                 (set-info :status sat)       \
                 (declare-sort A 0)")         # 1 match
```

# And

The `@and` pattern builder takes at least one pattern and matches a term if and only if the term
matches all the provided patterns

```
smatch "(@and @atom hello)" <(printf "hello \n") # 1 match
smatch "(@and @atom hello)" <(printf "world \n") # 0 match
```

# Or

The `@or` pattern builder takes at least one pattern and matches a term if and only if the term
matches at least one of the provided patterns

```
smatch "(@or @atom hello)" <(printf "hello \n") # 1 match
smatch "(@or @atom hello)" <(printf "world \n") # 1 match
smatch "(@or @atom hello)" <(printf "() \n")    # 0 match
```

# Repeats

Repeats look like this:

```
(@* <pattern>)               # 0 or more matches of pattern
(@? <pattern>)               # 0 or one matches of pattern
(@+ <pattern>)               # one or more matches of pattern
(@less <n> <pattern>)        # less than n (inclusive) matches of pattern
(@more <n> <pattern>)        # more than n (inclusive) matches of pattern
(@between <n> <m> <pattern>) # between n (inclusive) and m (inclusive) matches of pattern
```

Here's some examples:

```
# all these match
smatch '(@* @atom)' <(printf "()")
smatch '(@* @atom)' <(printf "hello")
smatch '(@* @atom)' <(printf "(hello)")
smatch '(@* @atom)' <(printf "(hello world)")
smatch '(@* @atom)' <(printf "(hello world !)")

# this one matches too
smatch '(declare-fun @atom ( (@* (@atom @atom)) ) @atom)' \
       <(printf "(declare-fun foo ((a nat) (b nat)) bool)")
```

# Depth

All patterns start matching at the first level of a given term.
It's possible to search at any depth using the repeats notation by surrounding it with a `@depth`.

Here's examples that match:

```
smatch '(@depth (@* hello))' <(printf "hello")
smatch '(@depth (@* hello))' <(printf "(assert (= (f hello) world))")
smatch '(@depth (@between 2 4 hello))' <(printf "(assert (= (f hello) world))")
```

