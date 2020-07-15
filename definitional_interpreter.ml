(*
In this assignment, you will define the abstract syntax (data type exp) and a definitional interpreter eval for a simple arithmetic and boolean calculation language.
The expressions in the language are of the following forms

Integer constants, 
Unary arithmetic operations: abs, (and any other sensible ones you can think of),
Identifiers, represented as (alphanumeric) strings
binary operations: + (addition), - (subtraction), * (multiplication), div, mod, ^ (exponentiation)
Boolean constants: T and F
Unary boolean operation: not
binary boolean operations:  /\ (and), \/ (or), -> (implies)
Comparison operators: = (equal) , > (greater than), < (less than) , >= (greater or equal), <= (less or equal) on integer expressions
n-tuples for each n > 2
Projection operators proj(i,n) which project the ith element of an n-tuple.
Assume all inputs are of proper type (we will study type-checking later).  Define a suitable data type answer.

eval: exp -> answer.

Next, define a suitable set of opcodes for a stack-and-table machine to evaluate this language and define a compiler for this language to sequences of these opcodes.
compile: exp -> opcode list

Third, define the stack machine execution functions, which takes a sequence of opcodes and executes them starting from a given stack and table.
execute: stack * table * opcode list -> answer

Provide enough examples 
*)



type exp = Const of int|
           Abs of exp|
	         Var of string|
           Add of exp*exp|
           Sub of exp*exp|
           Mul of exp*exp|
           Div of exp*exp|
	         Mod of exp*exp|
           Pow of exp*exp|
           T|F|Not of exp|
           LAnd of exp*exp|LOr of exp*exp|
           LIm of exp*exp|
           Eq of exp*exp|Gt of exp*exp|Lt of exp*exp|Ge of exp*exp|Le of exp*exp|
           Ntupl of exp list|
           Proj of int*exp;;
exception DNE;;
type answer = Num of int| Boo of bool| Tup of answer list;;
let makebool t = match t with Boo(t) -> t|_-> raise DNE;;
let makeint t = match t with Num(n) -> n| _ -> raise DNE;;
let makeneg t = match t with Num(n) -> Num (-n)|_-> raise DNE;;
let maketup t = match t with Tup(n) -> n|_-> raise DNE;;
let makentup t = match t with Ntupl(n) -> n|_-> raise DNE;;
open List;;



let rho s = match s with "x"->Num(2)|"y"->Num(3)|"z"->Num(4)|_->raise DNE;;

let rec eval rho t = match t with
                 Const(n) ->Num (n)|
                 Abs(n) ->if eval rho n>Num(0) then eval rho n else makeneg(eval rho n) |
                 Add(n1,n2) -> Num(makeint (eval rho n1)+ makeint (eval rho n2))|
                 Var (n) -> rho(n)|
                 Sub(n1,n2) -> Num(makeint (eval rho n1)-makeint (eval rho n2))|
                 Div(n1,n2) -> Num(makeint (eval rho n1) / makeint (eval rho n2))|
                 Mul(n1,n2) -> Num(makeint (eval rho n1) * makeint (eval rho n2))|
	               Mod(n1,n2) -> Num(makeint (eval rho n1) mod makeint (eval rho n2))|
                 T-> Boo(true)| F->Boo(false)|
                 Ntupl(n) -> Tup(List.map (eval rho) (n))|
                 Not(n) -> if eval rho n = Boo(true) then Boo(false) else Boo(true)|
                 LAnd(n1,n2) -> Boo(makebool(eval rho n1) && makebool(eval rho n2))|
                 LOr(n1,n2) -> Boo(makebool(eval rho n1) || makebool(eval rho n2))|
                 LIm (n1,n2) -> Boo(makebool(eval rho n1) && not(makebool(eval rho n2)))|
                 Eq(n1,n2) -> if makeint(eval rho n1) = makeint(eval rho n2) then Boo(true) else Boo(false)|
                 Gt(n1,n2) -> if makeint(eval rho n1) > makeint(eval rho n2) then Boo(true) else Boo(false)|
                 Lt(n1,n2) -> if makeint(eval rho n1) < makeint(eval rho n2) then Boo(true) else Boo(false)|
                 Le(n1,n2) -> if makeint(eval rho n1) <= makeint(eval rho n2) then Boo(true) else Boo(false)|
                 Ge(n1,n2) -> if makeint(eval rho n1) >= makeint(eval rho n2) then Boo(true) else Boo(false)|
                 Pow(n1,n2)-> Num(int_of_float((float(makeint(eval rho n1)))**float(makeint(eval rho n2))))|
                 Proj(i,n) -> eval rho (List.nth (makentup n) i);;




let rec evaltupl x = match x with
                 []-> []|
                 x::xs->(eval rho (x))::(evaltupl xs);;


type opcode = CONST of int | ABS |ADD|SUB |DIV |MUL|VAR of string|TRUE|FALSE|NOT|AND|OR|IMP|EQ|GT|LT|LE|GE|POW|PROJ|MOD|NTUPL of opcode list list|TUP;;


let rec compile e = match e with
                    Const(n)-> [CONST(n)]|
                    Abs(n) -> (compile n)@[ABS]|
                    Var(n) -> [VAR(n)]|
                    Mod(a,b) -> (compile a)@(compile b)@[MOD]|
                    Add(a,b) -> (compile a)@(compile b)@[ADD]|
                    Sub(a,b) -> (compile a)@(compile b)@[SUB]|
                    Div(a,b) -> (compile a)@(compile b)@[DIV]|
                    Mul(a,b) -> (compile a)@(compile b)@[MUL]|
                    Ntupl(n) ->   [NTUPL(List.map compile n)]|
                    T->[TRUE]|F->[FALSE]|
                    Not(n)-> (compile n)@[NOT]|
                    LAnd(a,b)-> (compile a)@(compile b)@[AND]|
                    LOr(a,b)-> (compile a)@(compile b)@[OR]|
                    LIm(a,b)-> (compile a)@(compile b)@[IMP]|
                    Eq(a,b)-> (compile a)@(compile b)@[EQ]|
Gt(a,b)-> (compile a)@(compile b)@[GT]|
Lt(a,b)-> (compile a)@(compile b)@[LT]|
Le(a,b)-> (compile a)@(compile b)@[LE]|
Ge(a,b)-> (compile a)@(compile b)@[GE]|
Pow(a,b)-> (compile a)@(compile b)@[POW]|
Proj(i,n)-> if (eval rho (Proj(i,n)))=Boo(true) then [TRUE]@[PROJ]
else if (eval rho (Proj(i,n)))=Boo(false) then  [FALSE]@[PROJ] else
[CONST(makeint(eval rho (Proj(i,n))))]@[PROJ];;

open List;;

let matchbool t = match t with Boo(true)->T|Boo(false)->F|_->raise DNE;;








type duet = Duet of string*int;;
type table = Table of duet list;;


let rec lookup x t = match t with
                 Table[]-> raise DNE|
                 Table (e::es) -> match e with
Duet(a,b)->if a = x then b else lookup (x) (Table(es));;



let curry execute s table c = execute(s,table,c);;




let rec execute (s,table,c) = match (s,table,c) with
                        (s,table,[]) -> hd s|
                        (s,table,CONST(n)::c') -> execute(Num(n)::s,table,c')|
                        (s,table,VAR(x)::c')-> execute(Num(lookup(x)(table))::s,table,c')|
                        (Num(n)::s,table,ABS::c') -> execute (eval rho(Abs(Const(n)))::s,table,c')|
(Num(m)::Num(n)::s',table,ADD::c') -> execute (eval rho(Add(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,SUB::c') -> execute (eval rho(Sub(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,MUL::c') -> execute (eval rho(Mul(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,DIV::c') -> execute (eval rho(Div(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,MOD::c') -> execute (eval rho(Mod(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,POW::c') -> execute (eval rho(Pow(Const(n),Const(m)))::s',table,c')|
(s',table,NTUPL(n)::c')   ->  execute( Tup(List.map (curry execute s table) (n) )::s',table,c')|
(s,table,TRUE::c') -> execute(Boo(true)::s,table,c')|
(s,table,FALSE::c') -> execute(Boo(false)::s,table,c')|
(Boo(n)::s,table,NOT::c') -> execute (eval rho(Not(matchbool(Boo(n))))::s,table,c')|
(Boo(m)::Boo(n)::s',table,AND::c') -> execute (eval rho(LAnd(matchbool(Boo(n)),matchbool(Boo(m))))::s',table,c')|
(Boo(m)::Boo(n)::s',table,OR::c') -> execute (eval rho(LOr(matchbool(Boo(n)),matchbool(Boo(m))))::s',table,c')|
(Boo(m)::Boo(n)::s',table,IMP::c') -> execute (eval rho(LIm(matchbool(Boo(n)),matchbool(Boo(m))))::s',table,c')|
(Num(m)::Num(n)::s',table,EQ::c') -> execute (eval rho(Eq(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,GT::c') -> execute (eval rho(Gt(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,LT::c') -> execute (eval rho(Lt(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,LE::c') -> execute (eval rho(Le(Const(n),Const(m)))::s',table,c')|
(Num(m)::Num(n)::s',table,GE::c') -> execute (eval rho(Ge(Const(n),Const(m)))::s',table,c')|
(n::s',table,PROJ::c') -> execute (n::s',table,c');;









let tab = Table[Duet("x",2);Duet("y",3);Duet("z",4)];;





let y =  Mod(Proj(2,Ntupl[Const(1);Const(1);Add(Sub(Const(5),Const(4)),Add(Const(3),Const(4)))]),Var("y"));;
let w = compile y;;
execute([],tab,w);;
eval rho y;;
let ex = Mul(Proj(1,Ntupl[Const(1);Const(4);Add(Sub(Const(5),Const(4)),Add(Const(3),Const(4)))]),Mod(Const(8),Const(3)));;
let w = compile ex;;
execute([],tab,w);;
eval rho ex;;




let z= Proj(2,Ntupl[Const(1);Const(2);Const(3)]);;
let w = compile z;;
execute([],tab,w);;
eval rho z;;


let z= Ntupl[Div(Const(32),Const(8));Const(2);Const(3); Pow(Const(2),Const(3));Eq(Const(5),Const(9)); LAnd(LOr(T,F),F); Abs(Const(-32)); Proj(1,Ntupl[Const(1);Const(2);Const(3)])];;
let w = compile z;;
execute([],tab,w);;
eval rho z;;


let z= Ntupl[Div(Const(32),Const(8));Const(2);Const(3); Pow(Const(2),Const(3));Eq(Const(5),Const(9)) ];;
let w = compile z;;
execute([],tab,w);;
eval rho z;;




let z= Ntupl[Div(Const(32),Const(8));Const(2);Const(3)];;
let w = compile z;;
execute([],tab,w);;
eval rho z;;



let z=  Proj(2,Ntupl[Const(1);Const(2); Proj(2,Ntupl[Const(1);Const(2);Const(45)])]);;
let w = compile z;;
execute([],tab,w);;
eval rho z;;
