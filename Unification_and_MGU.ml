(**                             Assignment 3 Programing Languages

Consider the representation of "pre-terms" using the following data type definition

type term = V of variable | Node of symbol * (term list);;

Choose suitable type representations for types variable and symbol.
1. Given a signature consisting of symbols and their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs, or as a function from symbols to arities, write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)
2. Given a valid signature (checked using check_sig), define a function wfterm that checks that a given preterm is well-formed according to the signature.
3. Define functions ht, size and vars that given a well-formed term, return its height (leaves are at height 0) , its size (number of nodes) and the set of variables appearing in it respectively.  Use map, foldl and other such functions as far as possible wherever you use lists.  
4. Define a suitable representation for substitutions.  
5. Come up with an efficient representation of composition of substitutions. 
6. Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) substitution s to t.  Ensure that subst is efficiently implemented. 
7. Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.
For each of your programs provide adequate suitable test cases and comment your programs.

**)


(*Local function to check_sig :To make a list of first elements of a pair from a list of pairs *)
let rec makelist x =  match x with
                  []-> []|(a,b)::zs->a::makelist zs;;

(*Local function to check_sig :To check repetition of a symbol in a signature*)
let rec check_present x = match x with
                          []-> false|z::zs->match z with
                                                (a,b)-> if List.mem (a) (makelist zs) then true else check_present zs;;


(*To check the validity of a signature*)
(* valid -> 1 ; invalid -> 0 *)
let rec check_sig x = if (check_present x = true) then 0 else match x with
                  []-> 1|x::xs->match x with
                                  (a,b)-> if b<0 then 0 else check_sig xs;;

(*exception DoesNotExist *)
exception DNE;;


type variable = string;;
type symbol = string;;
type term = V of variable | Node of symbol * (term list);;


(*Local function to wfterm :to check the arity of a term x in signature s*)
let rec check_arity x s =match s with
                    []-> raise DNE|b::bs -> match b with (m,n)->if m = x then n else check_arity x bs;;

(*Checking the validity of node n in term t wrt signature s*)
(* valid -> 1 ; invalid -> 0 *)
let check_node n s = match n with
                     Node(a,l) -> if List.mem (a) (makelist s) = false then 0 else if check_arity a s != List.length l then 0 else 1|
                     V(n) -> 1;;

let logical_and a b = match (a,b)  with
                       (1,1) ->1|(_,0)->0|(0,_)->0;;

(*Local function to wfterm :Checking the validity of node n in term t wrt signature s*)
let rec check_list l s = match l with
                         []->1|
                         x::xs -> logical_and (check_node x s) (check_list xs s);;

(* output of wfterm is 1 if valid and 0 for invalid  *)
(* to check the validity of a term I first check the validity of the symbol by check_node and then check the validity of the
   list associated with it by check_list recursively *)
let rec wfterm t s = match t with
                     Node(a,b)-> if (check_node (Node(a,b)) s)=1 && (check_list b s)= 1 then 1 else 0;;



let rec sumlist l = match l with
                    [] ->0|x::xs->x+sumlist xs;;

let rec maxlist l = match l with
                    [n]-> n|x::xs -> if x>maxlist(xs) then x else maxlist(xs);;

let rec ht t = match t with
               Node(_,[])->0|
               V(x) -> 0|
               Node(a,b) -> 1 + maxlist (List.map ht b);;


(* variable are not taken into size ca;lculation according to question*)
let rec size t = match t with
                 Node(_,[])->1|
                 V(x) -> 0|
                 Node(a,b) -> 1 + sumlist (List.map size b);;

(*local function for vars *)
let rec remlist l = match l with
                    [n] -> n | x::xs ->(x)@remlist(xs);;

let rec vars t = match t with
                 Node(_,[])->[]|
                 V(x) -> [x]|
                 Node(a,b)-> remlist(List.map vars b);;

(*Representation of substitution *)
type subsi = D of term*term | Sub of subsi list list;;


(*local function for subst :checks the mapping of a variable in the substitution *)
let rec check_pair x s =match s with
                    Sub[[]]-> raise DNE|Sub[(b::bs)] -> match b with D(m,n)->if m = x then n else check_pair (x) (Sub[(bs)]);;


(*makes the list of domain in the substitution *)
let rec makelist2 x =  match x with
                       Sub[[]]-> []|Sub[((D(a,b))::zs)]->a::makelist2 (Sub[(zs)]);;

(*local function for subst1: for substitution in a list*)
let rec substlist l st =  match l with
                          V(x)::y ->if List.mem (V(x)) (makelist2 st) = true then  (check_pair (V(x)) (st))::(substlist y st) else  V(x)::(substlist y st)|
                          Node(a,b)::y->Node(a,(substlist b st))::(substlist y st)|
                          []->[]
                          ;;


(*local function for subst : for substitution of one sigma*)
let subst1 st t = match t with
                  V(x) ->if List.mem (V(x)) (makelist2 st) = true then (check_pair (V(x)) (st)) else V(x)|
                  Node(a,[])->Node(a,[])|
                  Node(a,b)-> Node(a,substlist b st);;

(* substitution UHE *)
let rec subst st t = match st with
                     Sub[[D(n,m)]] -> subst1 (Sub[[D(n,m)]]) (t)|
                     Sub(c::cs)   ->  subst (Sub(cs)) (subst1 (Sub[c]) (t));;

(* composition of two substitutions*)
let compose_subst s1 s2 = match (s1,s2) with
                          (Sub[[(D(x,y))]],Sub(b)) -> if x = y then b else [[(D(x,y))]]@b|
                          (Sub (a),Sub(b)) -> a@b;;

exception NOT_UNIFIABLE;;

(* Identity Substitution*)
let id x y = Sub[[(D(x,x))]];;

open List;;

(*outputs a substitution*)
let rec mgu t1 t2 = match (t1,t2) with
                    (V(x),V(y)) -> if x =y then  (Sub[[D(V(x),V(x))]]) else  (Sub[[D(V(x),V(y))]])|
                    (V(x),Node(a,[])) ->  (Sub[[D(V(x),Node(a,[]))]])|
                    (V(x),Node(a,b)) -> if List.mem ((x)) (vars t2) then raise NOT_UNIFIABLE else  (Sub[[D(V(x),Node(a,b))]])|

                    (Node(a,[]),Node(a1,b)) -> raise NOT_UNIFIABLE|
                    (Node(a,b),Node(c,d)) -> if (a=c)&&(List.length b =0)&&(List.length d =0) then (id t1 t2)  else if
                                             a<>c then raise DNE else if List.length b != List.length d then raise NOT_UNIFIABLE else
                                             let sg = ref (id t1 t2) in
                                             for i = 0 to (List.length b)-1 do
                                             sg := Sub(compose_subst (!sg) (mgu (subst (!sg) (List.nth b i)) (subst (!sg) (List.nth d i))))
                                             done;  !sg                                    ;;


(*Examples*)
let ex1=Node(("Abs"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let ex2=Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let y = mgu ex1 ex2;;
(*Answer: val y : subsi =  Sub [[D (V "a1", V "x")]; [D (V "b1", V "y")]; [D (V "z", V "z")]]  *)
subst y ex1 = subst y ex1;;


let exa1=Node(("Abs"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("x");V("x")])  ]))])])  ]))]) ;;
let exa2=Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let y0 = mgu exa1 exa2;;
(*Answer:
val y0 : subsi =Sub[[D (V "a1", V "x")]; [D (V "b1", V "y")]; [D (V "x", V "y")];[D (V "y", V "z")]]
*)


let t1 = Node("b",[]);;
let t2 = Node("a",[]);;
let y1 = mgu t1 t2;;
(*Answer: Exception: NOT_UNIFIABLE.*)



let t11 = V("f");;
let t22 = Node("a",[]);;
let y2 = mgu t11 t22;;
(*Answer: val y2 : subsi = Sub [[D (V "f", Node ("a", []))]]*)



let t3 = Node("add",[V("a");Node("add",[V("a");V("b")])]);;
let t4 = Node("add",[V("x");Node("add",[V("y");V("z")])]);;
let y3 = mgu t3 t4;;
(*Answer: val y3 : subsi = Sub [[D (V "a", V "x")]; [D (V "a", V "y")]; [D (V "b", V "z")]]*)




(* Examples for check_sig*)
let x1 = [("a",2);("b",3);("c",4);("c",3);("d",11)];;
let x2 = [("a",2);("b",3);("c",4);("e",3);("d",11)];;
let x3 = [("a",2);("b",3);("c",4);("f",-3);("d",11)];;

check_sig x1;;
(*Answer:  - : int = 0*)
check_sig x2;;
(*Answer:  - : int = 1*)
check_sig x3;;
(*Answer:  - : int = 0*)




(*Examples for wfterm *)
let sign = [("a1",0);("a2",0);("a3",0);("f3",3);("f1",1);("b1",1);("f2",2) ];;
let ter = Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
wfterm ter sign;;
(*Answer: 1 *)

let ter1 = Node("f",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
wfterm ter1 sign;;
(*Answer: 0 *)

let ter2 = Node("f3",[Node("a1",[]);Node("a2",[]);Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])])]);;
wfterm ter2 sign;;
(*Answer: 1 *)

let ter3 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[])]);;
wfterm ter3 sign;;
(*Answer: 1 *)

let ter4 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[]);V("e") ]);;
wfterm ter4 sign;;
(*Answer: 0 *)



(*Examples for size,ht,vars *)
let sign = [("a1",0);("a2",0);("a3",0);("f3",3);("f1",1);("b1",1);("f2",2) ];;
let ter = Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
ht ter;; size ter;; vars ter;;
(*Answer:
- : int = 1
- : int = 4
- : variable list = [] *)

let ter1 = Node("f",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
ht ter1;; size ter1;; vars ter1;;
(*Answer:
- : int = 1
- : int = 4
- : variable list = []
  *)

let ter2 = Node("f3",[V("d");Node("a2",[]);Node("f3",[Node("a1",[]);V("ss");Node("a3",[])])]);;
ht ter2;; size ter2;; vars ter2;;
(*Answer:
- : int = 2
- : int = 5
- : variable list = ["d"; "ss"]
 *)

let ter3 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[])]);;
ht ter3;; size ter3;; vars ter3;;
(*Answer:
- : int = 1
- : int = 3
- : variable list = ["d"]
*)

let ter4 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[]);V("e") ]);;
ht ter4;; size ter4;; vars ter4;;
(*Answer:
- : int = 1
- : int = 3
- : variable list = ["d"; "e"]
*)


let ex1 = Node(("Abs"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
ht ex1;; size ex1;; vars ex1;;
(*Answer :
- : int = 6
- : int = 6
- : variable list = ["a1"; "b1"; "x"; "y"; "z"]
*)


(*Examples for subst *)

let sss1 = Sub[[D(V("x"),V("y"))];[D(V("z"),V("t"))];[D(V("s"),V("q"))];[D(V("d"),V("r"))]];;
let sss2 = Sub[[D(V("a"),V("b"))]];;
let ttt = Node("add",[V("a");Node("add",[V("z");V("b")])]);;
subst sss1 ttt;;
(*Answer: - : term = Node ("add", [V "a"; Node ("add", [V "t"; V "b"])]) *)
subst sss2 ttt;;
(*Answer: - : term = Node ("add", [V "b"; Node ("add", [V "z"; V "b"])])*)
let ter = Node("f3",[V("d");Node("a2",[]);Node("a3",[Node("add",[V("a");Node("add",[V("g");V("b")])])])]);;
subst sss1 ter;;
(*Answer:  - : term = Node ("f3",[V "r"; Node ("a2", []);Node ("a3", [Node ("add", [V "a"; Node ("add", [V "g"; V "b"])])])])*)
