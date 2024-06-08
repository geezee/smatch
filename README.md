# Smatch

A grep-like command line utility to search for s-expressions matching some given patterns.
Patterns are wildcards that match any s-expression,
atom wildcards that match any atom,
literals that match literal atoms,
regular expressions that match literals matching the regular expression,
conjunctions of patterns,
disjunctions of patterns,
and flat and depth repetitions allowing to pattern match at particular depth levels in an
s-expression and at particular flat positions.

The flavor of s-expressions that Smatch parses is the SMTLIB flavor which is described in the
manual.

Smatch is pronounced like smash.

# A Note on Source Code

The tool is meant to do one thing and one thing alone:
fundamentally there's a pattern matching algorithm and everything around it is boilerplate which
should be kept at a minimum.
Thus smatch is offered in a single file `smatch.rs`.

## Building

To build your own copy of smatch run the following command.

```
cargo build --release
```

It will first install and build smatch's two dependencies: regex and clap.
This is a one-time operation unless you have chosen to update the locked version of either.

The resulting binary is in `target/release/smatch`.

## A Note on Tests

The tests are also provided in a single bash script that also serves as a list of examples to better
understand what patterns are designed to match.

### A Note on Cargo Test

Ideally the tests would be run with `cargo test`.
Sadly this requires giving names to the 90+ tests and examples in `test.sh` which is a silly thing
to spend time on.

# Syntax of Patterns

For more examples look in `test.sh`.

## Wildcard

The wildcard `@_` matches against any S-expr

```
smatch @_ <(printf "hello \n world \n") # 2 matches
smatch @_ <(printf "(hello world)\n")   # 1 match
smatch @_ <(printf "()\n")              # 1 match
```

## Atom Wildcard

The atom wildcard `@atom` matches only against atoms

```
smatch @atom <(printf "hello \n world \n") # 2 matches
smatch @atom <(printf "()\n")              # 0 matches
smatch @atom <(printf "(hello world)")     # 0 matches
```

## Literal Atoms

A literal atom matches only against the same literal

```
smatch hello <(printf "hello \n world \n") # 1 match
smatch hello <(printf "world\n")           # 0 match
smatch hello <(printf "(hello world)")     # 0 match
```

## Regular Expression Identifier

An identifier can be matched against with a regular expression but making that regular expression a
string and surrounding it with `@re`

```
smatch '(@re "^declare-.*")' <(printf "declare-fun \n set-info \n declare-sort") # 2 matchs
```

## List

A list matches a list, if no repeats are used then the list pattern matches a list term if and only
if their length match and the members match pairwise.

```
smatch '((@re "^declare-.*") @atom @_ @atom)' \
       <(printf "(declare-fun hello (U U) U)  \
                 (set-info :status sat)       \
                 (declare-sort A 0)")         # 1 match
```

## And

The `@and` pattern builder takes at least one pattern and matches a term if and only if the term
matches all the provided patterns

```
smatch "(@and @atom hello)" <(printf "hello \n") # 1 match
smatch "(@and @atom hello)" <(printf "world \n") # 0 match
```

## Or

The `@or` pattern builder takes at least one pattern and matches a term if and only if the term
matches at least one of the provided patterns

```
smatch "(@or @atom hello)" <(printf "hello \n") # 1 match
smatch "(@or @atom hello)" <(printf "world \n") # 1 match
smatch "(@or @atom hello)" <(printf "() \n")    # 0 match
```

## Repeats

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

## Depth

All patterns start matching at the first level of a given term.
It's possible to search at any depth using the repeats notation by surrounding it with a `@depth`.

Here's examples that match:

```
smatch '(@depth (@* hello))' <(printf "hello")
smatch '(@depth (@* hello))' <(printf "(assert (= (f hello) world))")
smatch '(@depth (@between 2 4 hello))' <(printf "(assert (= (f hello) world))")
```

