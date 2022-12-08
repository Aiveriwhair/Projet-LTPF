(*
On considère une variante appelelée WHILEb du langage WHILE vu en LT, où un programme est :
— soit ne rien faire,
— soit une affectation (d’une expression à une variable),
— soit deux programmes mis bout-à-bout (séquence),
— soit une instruction conditionnelle (constituée d’une expression, d’un programme à exécuter si l’expression vaut 1, et d’un second programme à exécuter si l’expression vaut 0),
— soit une boucle while (constitué d’une expression et d’un corps; la condition d’arrêt étant que l’expression vaut 0).
Dans un premier temps, on considérera un version simplifiée de WHILEb nommée WHILEb- - où :
— que toutes les variables sont booléennes (et valent 0 ou 1)
— que la condition d’un if ou d’un while est toujours constituée d’une variable seulement
— que le membre droit d’une affectation peut être : soit 0, soit, 1, soit une autre variable.
— Enfin on se contentera de 4 variables booléennes a, b, c et d.

On pourrait ainsi écrire un programme WHILEb-- comme :
  a := 1 ;
  b := 1 ;
  c := 1 ;
  while(a) {
  if(c) {
  c := 0 ;
  a := b
  } else {
  b := 0 ;
  c := a
  }
  }   
*)

(*Question 1.1.1*)

type var = A | B | C | D;;

type cons = Zero | Un;;

type expr = Var of var | Cons of cons | And of expr * expr | Or of expr * expr | Not of expr | Concat of expr * expr | Fin | Trou of prog;;

type prog = Nop | Affect of var * expr | Seq of prog * prog | If of expr * prog * prog | While of expr * prog;;



(*Donner une grammaire décrivant le langage WHILEb-- sans recursivité gauche)*)

(* Question 1.1.2 - 1.1.3

  Grammaire du langage WHILEb--:
  
  
  C :: '1' | '0' 
  V :: 'a' | 'b' | 'c' | 'd'
  L :: '\n' | '\t' | ' ' | SI
  A :: V.':'.'='.(CV)
  I :: 'w'.'('.V.')'.'{'.(SI).'}' | 'i'.'('.V.')'.'{'.(SI).'}'.'{'.(SI).'}'
  S :: A.';'.S | A.';'.I.S | I.S | ε 
  CV:: C | V
  SI:: S | I | L

*)


(*Implémenter un analyseur syntaxique en OCaml pour la grammaire du langage
WHILEb--. Utiliser des combinateurs d'analyseurs *)

type analist = char list -> char list
(* Le type des fonctions qui épluchent une liste et rendent un résultat *)
type ('r, 'term) ranalist = 'term list -> 'r * 'term list;;

exception Echec

let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

(* Non terminal vide *)
let epsilon : analist = fun l -> l

let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Choix entre a ou b informatifs *)
let (+|) (a : ('res, 'term) ranalist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> try a l with Echec -> b l

(* Choix entre a1 ou a2 *)
let (-|) (a1 : analist) (a2 : analist) : analist =
  fun l -> try a1 l with Echec -> a2 l

(* a sans résultat suivi de b sans résultat *)
let ( -->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : analist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : ('res, 'term) ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) : ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l

let pa_C = (terminal '1' -| terminal '0');;

let pa_V = (terminal 'a' -| terminal 'b' -| terminal 'c' -| terminal 'd');;

let pa_CV = (pa_C -| pa_V);;

let pa_A = (pa_V --> terminal ':' --> terminal '=' --> pa_CV);;

let rec pa_I = fun l -> l|>
   terminal 'w' --> terminal '(' --> pa_V --> terminal ')'--> terminal '{' --> pa_SI --> terminal '}'
   -|
     terminal 'i' --> terminal '(' --> pa_V --> terminal ')' --> terminal '{' --> pa_SI --> terminal '}'
   --> terminal '{' --> pa_SI --> terminal '}'
and  pa_SI = fun l -> l|>  pa_S -| pa_I
and  pa_S = fun l -> l|>
   (pa_A  --> terminal ';' --> pa_S) -|
   (pa_A --> terminal ';' --> pa_I --> pa_S) -|
     ( pa_I --> pa_S);;

let pr_C : (cons, char) ranalist = fun l ->
  l|> 
  (terminal '0' -+> epsilon_res Zero) +| (terminal '1' -+> epsilon_res Un)


let pr_V : (var,char) ranalist = fun l -> l |>
(terminal 'a' -+> epsilon_res A) +| (terminal 'b' -+> epsilon_res B)
+| (terminal 'c' -+> epsilon_res C) +| (terminal 'd' -+> epsilon_res D);;

let pr_CV : (expr, char) ranalist = fun l -> l |>
(pr_C ++> fun c -> epsilon_res (Cons c)) +| (pr_V ++> fun v -> epsilon_res (Var v));;


(* 

C ::= ’0’ | ’1’
V ::= ’a’ | ’b’ | ’c’ | ’d’
CV ::= C | V

E ::= T.E'
E'::= '+'.T.E' |  ε
T ::== F.T'
T'::= '.'.F.T' |  ε
F ::= ’!’.F | CV | ’(’.E.’)’ 

 *)








 (* let rec pr_SI : (prog,char) ranalist = fun l -> l|> pr_S +| pr_I
 and pr_S : (prog,char) ranalist = fun l -> l|>
 (pr_A ++> fun a -> terminal ';' -+> pr_S ++> fun s -> epsilon_res (Seq (a,s))) +|
   (pr_A ++> fun a -> terminal ';' -+> pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (a,Seq (i,s)))) +|
   (pr_A ++> fun a -> epsilon_res (Seq(a, Nop))) +|
   (pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (i,s))) +|
 (epsilon_res Nop)
 and pr_I : (prog,char) ranalist = fun l -> l|>
   (terminal 'w' --> terminal '(' -+> pr_V ++> fun v -> terminal ')' --> terminal '{' -+> pr_SI 
   ++> fun p -> terminal '}' -+> epsilon_res (While (Var v, p)))
   +|
   (terminal 'i' --> terminal '(' -+> pr_V ++> fun v -> terminal ')' --> terminal '{' -+> pr_SI 
  ++> fun p1 -> terminal '}' --> terminal '{' -+> pr_SI ++> fun p2 -> terminal '}' -+> epsilon_res (If (Var v,p1,p2))) *)


let rec pr_L : (prog,char) ranalist = fun l -> l|>
    (terminal '\n' -+> pr_L) +|
    (terminal '\t' -+> pr_L) +|
    (terminal ' ' -+> pr_L) +|
    pr_SI
  and pr_SI : (prog,char) ranalist = fun l -> l|> pr_S +| pr_I +| pr_L
  and pr_S : (prog,char) ranalist = fun l -> l|>
  (pr_A ++> fun a -> terminal ';' -+> pr_S ++> fun s -> epsilon_res (Seq (a,s))) +|
    (pr_A ++> fun a -> terminal ';' -+> pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (a,Seq (i,s)))) +|
    (pr_A ++> fun a -> epsilon_res (Seq(a, Nop))) +|
    (pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (i,s))) +|
  (epsilon_res Nop) +|
  pr_L
  and pr_I : (prog,char) ranalist = fun l -> l|>
    (terminal 'w' --> terminal '(' -+> pr_V ++> fun v -> terminal ')' --> terminal '{' -+> pr_SI 
    ++> fun p -> terminal '}' -+> epsilon_res (While (Var v, p)))
    +|
    (terminal 'i' --> terminal '(' -+> pr_V ++> fun v -> terminal ')' --> terminal '{' -+> pr_SI 
   ++> fun p1 -> terminal '}' --> terminal '{' -+> pr_SI ++> fun p2 -> terminal '}' -+> epsilon_res (If (Var v,p1,p2)))
    +|
    pr_L
  and pr_A : (prog,char) ranalist = fun l ->
    l|>
    (pr_V ++> fun v -> terminal ':' --> terminal '=' -+> pr_E ++> fun e -> epsilon_res (Affect (v,e)))
    +|
    pr_L
  and pr_E : (expr, char) ranalist = fun l -> l|>
    (pr_T ++> fun t -> pr_E' ++> fun e -> epsilon_res (Concat (t,e))) +|
     pr_L
   and pr_E' : (expr, char) ranalist = fun l -> l|>
    (terminal '+' -+> pr_T ++> fun t -> pr_E' ++> fun e -> epsilon_res (Or (t,e))) +|
    (epsilon_res Fin)
   and pr_T : (expr, char) ranalist = fun l -> l|>
    (pr_F ++> fun f -> pr_T' ++> fun t -> epsilon_res (Concat (f,t)))
   and pr_T' : (expr, char) ranalist = fun l -> l|>
    (terminal '.' -+> pr_F ++> fun f -> pr_T' ++> fun t -> epsilon_res (And (f,t))) +|
    (epsilon_res Fin)
   and pr_F : (expr, char) ranalist = fun l -> l|>
    (terminal '!' -+> pr_F ++> fun f -> epsilon_res (Not f)) +|
    (pr_CV ++> fun cv -> epsilon_res cv) +|
    (terminal '(' -+> pr_E ++> fun e -> terminal ')' -+> epsilon_res e)
;;
   




  

(*
  a := 1 ;
  b := 1 ;
  c := 1 ;
  while(a) {
    if(c) {
      c := 0 ;
      a := b 
  } else {
      b := 0 ;
      c := a 
  }
}

*)


let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then []
    else s.[i] :: boucle (i+1)
  in boucle 0
;;

let test s= pr_L (list_of_string s);;

(*Réécrire de vrais gros tests tout jolie mhmmm les chocapik*)
let p = test "a:= b;"
let p1 = test "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}"
let p2= test "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}"

let pa = test "a:=1;b:=1;c:=1;"

let p5 = test "a:=1;c:=1;w(a){c:=0;a:=b}"
let p6 = test "w(a)
{}"
let p7 = test "i(a){b:=1}{}"



let testBool s = pr_E (list_of_string s);;
let p8 = testBool "a"
let p9 = testBool "a+b"
let p10 = testBool "a+b.c"
let p11 = testBool "a+b.c.d"
let p12 = testBool "a+b.0+!1"
let p13 = testBool "a+b.0+!(1+0)"
let p14 = testBool "(a+(b.0))+(!1)" 

let test_total s = pr_SI (list_of_string s);;


