Overview
========

Isabelle’s Simplifier is a powerful tool for reasoning using term
rewriting, with rewrite rules given as equations. While this is more
than sufficient in many cases, there are situations where it would be
great if automated rewriting could be done using mere equivalences as
rewrite rules. The `equivalence-reasoner` library makes this possible.

Of course, rewriting based on equivalences is generally not sound.
However, there are situations where it is indeed valid. For example, if
the goal is of the Form `R x y` where `R` is known to be an equivalence
relation, it is okay to use a fact of the form `R x x'` as a rewrite
rule to turn that goal into `R x' y`. A more complex example would be
that of a goal `R (f x) y` where `R` is a congruence with respect
to `f`. This goal can be safely turned into `R (f x') y`.

The facilities of the `equivalence-reasoner` library go even beyond
these kinds of rewriting, making it a versatile tool for automated
reasoning with equivalences. In particular, it is able to automatically
turn a given rewrite rule `R x x'` into a rewrite rule `S x x'` if `R`
is known to be included in `S`, thus making the former rule usable for
goals that involve `S` instead of `R`.


Requirements
============

You need Isabelle2021-1 to use this Isabelle library. You can obtain
Isabelle2021-1 from the [Isabelle website][isabelle].

[isabelle]:
    https://isabelle.in.tum.de/
    "Isabelle"


Setup
=====

To make this Isabelle library available to your Isabelle installation,
add the path of the `src` directory to the file
`$ISABELLE_HOME_USER/ROOTS`. You can find out the value of
`$ISABELLE_HOME_USER` by running the following command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF file that includes the documentation and
the code and places it in `$ISABELLE_BROWSER_INFO/IOG`. You can find out
the value of `$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO

The makefile specifies two targets: `properly`, which is the default,
and `qnd`. With `properly`, fake proofs (`sorry`) are not accepted; with
`qnd`, quick-and-dirty mode is used and thus fake proofs are accepted.
