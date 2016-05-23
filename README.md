# categorial-grammar.rkt
Author: Daniel J. Rothblatt, April 2016

Description: A categorial grammar is a bottom-up grammar formalism
common in linguistics (especially semantics).
In a categorial grammar, lexical items are associated with a type, and
the rules of the grammar are rules for combining types. (Compare this
to a phrase structure grammar, in which the rules are rules for
breaking down non-terminals.) A type is either primitive (atomic) or a
function from an input type to an output type. (This recursive
definition allows for infinitely many types.) This notion parallels
the types of mathematical functions (e.g., f: Naturals ->
Integers) and programming languages like ML and Haskell. The major difference
between a categorial grammar's types and mathematical function types is
that categorial types are non-commutative: A/B != A\B.
A/B is read "A over B", and indicates that an object of
this type takes an object of type B on the right and produces an
object of type A; A\B is read "A under B", and indicates that an
object of this type takes an object of type A on the left and
produces an object of type B.

Purpose: Position's importance in a categorial grammar is part of the
reason for its value as a linguistic formalism: It captures the notion
that word order matters in many languages, so that, for example, "The
cat bit Wakko" is not the same as "Wakko bit the cat". This program
uses a categorial grammar because its goal is to compile a large
part of speech-tagged dictionary of English that enables the user to
create larger phrases and determine their syntactic category.
The parallels with type systems in mathematics and programming
languages suggest that a categorial grammar could be used in a
statically-typed programming language, and this possibility is hinted
at in the

Use: Load categorial-grammar.rkt in a Racket REPL (such as DrRacket,
which the author uses). To add a category to the grammar, use the
define-category macro. To define words of a specified category, use
the define-word or define-words macros. To parse a string represented
as a list, use parse-1 [e.g., (parse-1 (list yakko schemed))]. To
parse a string represented as a sequence of arguments, use parse-2
[e.g., (parse-2 yakko schemed)].

To do: This categorial grammar parser is unfinished. It does not yet handle
variable types, e.g., conjunctions in natural language, where the
types being resolved are not specified when the category is
specified.
