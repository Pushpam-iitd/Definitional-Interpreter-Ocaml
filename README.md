# Definitional-Interpreter-Ocaml
Defined abstract syntax (data type exp) and a definitional interpreter eval for a simple arithmetic and boolean calculation language.

Defined abstract syntax (data type exp) and a definitional interpreter eval for a simple arithmetic and boolean calculation language. The expressions in the language are of the following forms

    1. Integer constants

    2. Unary arithmetic operations: abs

    3. Identifiers, represented as (alphanumeric) strings

    4. binary operations: + (addition), - (subtraction), * (multiplication), div, mod, ^ (exponentiation)

    5. Boolean constants: T and F

    6. Unary boolean operation: not

    7. binary boolean operations: /\ (and), / (or), -> (implies)

    8. Comparison operators: = (equal) , > (greater than), < (less than) , >= (greater or equal), <= (less or equal) on integer expressions

    9. n-tuples for each n > 2

    10. Projection operators proj(i,n) which project the ith element of an n-tuple.

Assume all inputs are of proper type (we will study type-checking later). Defined a suitable data type answer.

eval: exp -> answer.

Next, defined a suitable set of opcodes for a stack-and-table machine to evaluate this language and define a compiler for this language to sequences of these opcodes.

compile: exp -> opcode list

Third, defined the stack machine execution functions, which takes a sequence of opcodes and executes them starting from a given stack and table.

execute: stack * table * opcode list -> answer

It has enough exaples to support check the interpreter.
