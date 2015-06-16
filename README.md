# proof-trees

An implementation of proof trees for propositional logic. Some first-order logic is also handled.

## Build and Run

    $ javac *.java
    $ java prove test/arg01.txt

The parameter should be a text file that has the premises of an argument listed one per line, and the conclusion listed on the last line. Alternatively, if no argument is specified, the program will prompt the user to enter the premises and the conclusion.

## Symbols

The following symbols are used:

* `~` for negation
* `+` for disjunction
* `&` for conjunction
* `>` for implication
* `:` for biconditional
* `@` for universal quantification
* `#` for existential quantification

Arguments can be specified in either infix or prefix notation.
