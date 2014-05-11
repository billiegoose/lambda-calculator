lambda-calculator
=================

A small parser for the λ-calculus written in Haskell that I'm making for fun.

> "You made _what?_" See http://en.wikipedia.org/wiki/Lambda_calculus

Usage
-----
Load the program in ghci.
Type `cal "some lambda expression"` to see the output of small step reduction.
Example:
```Haskell
*Main> cal "/x./y.(y x) y /z.z"
((/x./y.(y x) y) /z.z)
(/_y.(_y y) /z.z)
(/z.z y)
y
```

Syntax
------
Variables: any word using only lowercase, uppercase, or numbers.

Abstraction: λ_var_._term_ is written as `/var.term` 

Application: a single space, e.g. `/id.id 1` == `1`

Grouping: done using parentheses, e.g. `/x.x x 1` == `(x 1)` but `/x.(x x) 1` == `(1 1)`
