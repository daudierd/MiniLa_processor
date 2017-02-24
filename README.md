# Verified MiniLa language processor with CafeOBJ

MiniLa_processor is a language processor implemented with CafeOBJ, an algebraic specification and verification language.
The documentation and installation files for the CafeOBJ interpreter used to execute specifications can be found on
the [official website] (https://cafeobj.org/) of the project.

## What is MiniLa?

MiniLa is an imperative programming language on natural numbers. It currently supports five kinds of statements:
the empty statement, assignment statements, conditional statements, loop statements and sequential composition statements.

## Organization of the code

The language processor is specified in [_minila.cafe_] (./minila.cafe) (_calculator.mod_ in former versions) and consists in:
-	an Interpreter, used as an oracle for verification
-	a Compiler
-	a Virtual Machine

Verification consists in proof scores implemented in [_verify-comp.cafe_] (./verify-comp.cafe) (_calculator-verif.mod_
in former versions), and other files such as _lem1.cafe_, _lem2.cafe_, _lem3.cafe_, _lem4.cafe_ and _lemY.cafe_ that verify
supporting lemmas.

The files _del.cafe_ and _del-verif.cafe_ as well as _eval.cafe_ and _eval-verif.cafe_ define and verify new operators
usable in proof scores.
