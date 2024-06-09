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

The flavor of s-expressions that Smatch parses is the SMTLIB v2.6 flavor which is described in the
[manual (PDF)](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf).

Smatch is pronounced like smash.

## A Note on Source Code

The tool is meant to do one thing and one thing alone:
fundamentally there's a pattern matching algorithm and everything around it is boilerplate which
should be kept at a minimum.
Thus smatch is offered in a single file `smatch.rs`.

### Installing

A statically linked binary for x86_64 is always provided in the
[releases](https://github.com/geezee/smatch/releases).

If you prefer to build and install it on your own you can run:

```
cargo install --git https://github.com/geezee/smatch
```

### Building

To build your own copy of smatch run the following command.

```
cargo build --release
```

It will first install and build smatch's two dependencies: regex and clap.
This is a one-time operation unless you have chosen to update the locked version of either.

The resulting binary is in `target/release/smatch`.

### A Note on Tests

The tests are also provided in a single bash script that also serves as a list of examples to better
understand what patterns are designed to match.

### A Note on Cargo Test

Ideally the tests would be run with `cargo test`.
Sadly this requires giving names to the 90+ tests and examples in `test.sh` which is a silly thing
to spend time on.

## Syntax of Patterns

For more examples look in `test.sh`.

### Wildcard

The wildcard `@_` matches against any S-expr

```
printf "hello \n world"  | smatch @_   # 2 matches
printf "(hello world)"   | smatch @_   # 1 match
printf "()"              | smatch @_   # 1 match
```

### Atom Wildcard

The atom wildcard `@atom` matches only against atoms

```
printf "hello \n world \n" | smatch @atom   # 2 matches
printf "()\n"              | smatch @atom   # 0 matches
printf "(hello world)"     | smatch @atom   # 0 matches
```

### Literal Atoms

A literal atom matches only against the same literal

```
printf "hello \n world \n" | smatch hello   # 1 match
printf "world\n"           | smatch hello   # 0 match
printf "(hello world)"     | smatch hello   # 0 match
```

### Regular Expression Identifier

An identifier can be matched against with a regular expression but making that regular expression a
string and surrounding it with `@re`

```
printf "declare-fun \n set-info \n declare-sort" | smatch '(@re "^declare-.*")'  # 2 matchs
```

### List

A list matches a list, if no repeats are used then the list pattern matches a list term if and only
if their length match and the members match pairwise.

```
printf "(declare-fun hello (U U) U)             \
                 (set-info :status sat)         \
                 (declare-sort A 0)"            \
| smatch '((@re "^declare-.*") @atom @_ @atom)' # 1 match
```

### And

The `@and` pattern builder takes at least one pattern and matches a term if and only if the term
matches all the provided patterns

```
printf "hello \n" | smatch "(@and @atom hello)"    # 1 match
printf "world \n" | smatch "(@and @atom hello)"    # 0 match
```

### Or

The `@or` pattern builder takes at least one pattern and matches a term if and only if the term
matches at least one of the provided patterns

```
printf "hello \n" | smatch "(@or @atom hello)"    # 1 match
printf "world \n" | smatch "(@or @atom hello)"    # 1 match
printf "() \n"    | smatch "(@or @atom hello)"    # 0 match
```

### Repeats

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
printf "()"              | smatch '(@* @atom)'
printf "hello"           | smatch '(@* @atom)'
printf "(hello)"         | smatch '(@* @atom)'
printf "(hello world)"   | smatch '(@* @atom)'
printf "(hello world !)" | smatch '(@* @atom)'

# this one matches too
printf "(declare-fun foo ((a nat) (b nat)) bool)" \
| smatch '(declare-fun @atom ( (@* (@atom @atom)) ) @atom)'
```

### Depth

All patterns start matching at the first level of a given term.
It's possible to search at any depth using the repeats notation by surrounding it with a `@depth`.

Here's examples that match:

```
printf "hello"                        | smatch '(@depth (@* hello))'
printf "(assert (= (f hello) world))" | smatch '(@depth (@* hello))'
printf "(assert (= (f hello) world))" | smatch '(@depth (@between 2 4 hello))'
```

### Let bindings

Patterns can be given names and reused later.
Pattern names are of the shape `@<name>` with the obvious exception that `atom` and `_` being illegal names.

A simple example is the following pattern:

```
(@let (@t true) (@f false)
  (@or @t @f))
```

which is equivalent to `(@or true false)`.

Patterns can be nested and the usual lexical scoping rules apply, so:

```
(@let (@t true)
  (@or @t (@let (@t false)
    @t)))
```

is still equivalent to `(@or true false)`

Patterns can also be recursive which allows for cool patterns to be defined.
Just beware infinite recursion and the order of your variables!
Patterns are evaluated left to right and are greedy (they try to match as much as possible first before backtracking).

For example, the following pattern:

```
(@let (@bexpr (@or @atom (not @bexpr) (or (@+ @bexpr)) (and (@+ @bexpr))))
      @bexpr)
```

matches the following

```
(or x (and (not y) z (or x z)) t (not r))
```

but does not match the following expressions:

```
(or x (and (not y) z (or x z)) t (not r) (=> x y))
```

```
(or x (and (not y) z (or x z)) t (not r) (and))
```

```
(assert (or x (and (not y) z (or x z)) t (not r)))
```
