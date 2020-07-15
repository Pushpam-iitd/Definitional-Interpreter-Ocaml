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



# Most General Unifier Substitution
Follow this link for theory regarding unifiers and most general unifier substitution. http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node6.html

Consider the representation of "pre-terms" using the following data type definition

type term = V of variable | Node of symbol * (term list);;

Choose suitable type representations for types variable and symbol.

    1. Given a signature consisting of symbols and their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs, or as a function from symbols to         arities, write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)

    2. Given a valid signature (checked using check_sig), define a function wfterm that checks that a given preterm is well-formed according to the signature.
    3. Define functions ht, size and vars that given a well-formed term, return its height (leaves are at height 0) , its size (number of nodes) and the set of variables               appearing in it respectively.  Use map, foldl and other such functions as far as possible wherever you use lists.  
    4. Define a suitable representation for substitutions.  
    5. Come up with an efficient representation of composition of substitutions. 
    6. Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) substitution s to t.  Ensure that subst is                     efficiently implemented. 
    7. Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.

The code is well commented and explanatory.
