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

type expr = Var of var | Cons of cons | And of expr * expr | Or of expr * expr | Not of expr  | Fin ;;

type prog = Nop | Affect of var * expr | Seq of prog * prog | If of expr * prog * prog | While of expr * prog;;

type state = (var*int) list;;

(*Donner une grammaire décrivant le langage WHILEb-- sans recursivité gauche)*)

(* Question 1.1.2 - 1.1.3

  Grammaire du langage WHILEb--:
  
  
  C :: '1' | '0' 
  V :: 'a' | 'b' | 'c' | 'd'
  A :: V.':'.'='.(CV)
  I :: 'w'.'('.V.')'.'{'.(SI).'}' | 'i'.'('.V.')'.'{'.(SI).'}'.'{'.(SI).'}'
  S :: A.';'.S | A.';'.I.S | I.S | ε 
  CV:: C | V
  SI:: S | I 

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

 let rec pr_E : (expr, char) ranalist = fun l -> l|>
 (pr_T ++> fun t -> pr_E' ++> fun e -> match e with
                                       |Fin -> epsilon_res t
                                       |_ -> epsilon_res (Or (t,e)))

                                                                              
and pr_E' : (expr, char) ranalist = fun l -> l|>
  (terminal '+' -+> pr_T ++> fun t -> pr_E' ++> fun e -> match e with
                                                         |Fin -> epsilon_res t                                                                             |_ ->  epsilon_res (Or (t,e)))
  +|
 (epsilon_res Fin)
and pr_T : (expr, char) ranalist = fun l -> l|>
 (pr_F ++> fun f -> pr_T' ++> fun t -> match t with
                                       |Fin -> epsilon_res f
                                       |_ -> epsilon_res (And (f,t)))
and pr_T' : (expr, char) ranalist = fun l -> l|>
 (terminal '.' -+> pr_F ++> fun f -> pr_T' ++> fun t -> match t with 
                                                        |Fin -> epsilon_res f                                                                             |_ -> epsilon_res (And (f,t)))
 +|
 (epsilon_res Fin)
and pr_F : (expr, char) ranalist = fun l -> l|>
 (terminal '!' -+> pr_F ++> fun f -> epsilon_res (Not f)) +|
 (pr_CV ++> fun cv -> epsilon_res cv) +|
 (terminal '(' -+> pr_E ++> fun e -> terminal ')' -+> epsilon_res e)
;;


let pr_A : (prog,char) ranalist = fun l ->
  l|>
  (pr_V ++> fun v -> terminal ':' --> terminal '=' -+> pr_E ++> fun e -> epsilon_res (Affect (v,e)));;





let rec pr_SI : (prog,char) ranalist = fun l -> l|> pr_S +| pr_I
  and pr_S : (prog,char) ranalist = fun l -> l|>
  (pr_A ++> fun a -> terminal ';' -+> pr_S ++> fun s -> epsilon_res (Seq (a,s))) +|
    (pr_A ++> fun a -> terminal ';' -+> pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (a,Seq (i,s)))) +|
    (pr_A ++> fun a -> epsilon_res (Seq(a, Nop))) +|
    (pr_I ++> fun i -> pr_S ++> fun s -> epsilon_res (Seq (i,s))) +|
  (epsilon_res Nop)
  and pr_I : (prog,char) ranalist = fun l -> l|>
    (terminal 'w' --> terminal '(' -+> pr_E ++> fun cond -> terminal ')' --> terminal '{' -+> pr_SI 
    ++> fun p -> terminal '}' -+> epsilon_res (While (cond, p)))
    +|
    (terminal 'i' --> terminal '(' -+> pr_E ++> fun cond -> terminal ')' --> terminal '{' -+> pr_SI 
   ++> fun p1 -> terminal '}' --> terminal '{' -+> pr_SI ++> fun p2 -> terminal '}' -+> epsilon_res (If (cond,p1,p2)))
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

let test s= pr_SI (list_of_string s);;

(*Test Whileb *)
let p = test "a:=b;"
let p1 = test "a:=1;b:=1;c:=!1;w(a){i(c){c:=0;a:=a+b}{b:=0;c:=a}}"
let p2= test "a:=1;b:=1;c:=1;w(!a){i(!c){c:=0;a:=b}{b:=0;c:=a}}"

let pa = test "a:=1;b:=1;c:=1;"

let p5 = test "a:=1;c:=1;w(a){c:=0;a:=b}"
let p6 = test "w(a){}"
let p7 = test "a:=1;i(a){b:=1}{}"



let testBool s = pr_E (list_of_string s);;
let p8 = testBool "!a"
let p9 = testBool "a.b"
let p10 = testBool "a+b.c"
let p11 = testBool "a+b.c.d"
let p12 = testBool "a+b.0+!1"
let p13 = testBool "a+b.0+!(1+0)"
let p14 = testBool "(a+(b.0))+(!1)" 

let test_total s = pr_SI (list_of_string s);;

let s = [(A,1);(B,0)];;

let rec (get : var -> state -> int) = fun c s ->
  match s with
  |(var,value) :: suite -> if var=c then value else get c suite
  |[] -> raise Echec;;

let test = get A s;; 



let rec (evalA : expr -> state ->  int) = fun e s ->
  match e with
  |Cons Zero -> 0
  |Cons Un -> 1
  |Var x -> get x s
  |And(e1,e2) -> let a=evalA e1 s in
                 let b=evalA e2 s in
                 if a=b then 1 else 0

  |Or(e1,e2) ->  let a=evalA e1 s in
                 let b=evalA e2 s in
                 if a=1||b=1 then 1 else 0
  |Not(f) -> let a=evalA f s in
             if a=1 then 0 else 1

  |Fin -> raise Echec
 ;;


 let rec (update: state -> int -> var -> state) = fun s i v ->
   match s with
   | [] -> (v,i) :: []
   | (var,value) :: suite -> if var=v then (v,i)::suite else (var,value)::(update suite i v)

   ;;
  


let rec (evalW : prog -> state -> state) = fun p s ->
  match p with
  | Nop -> s
  | Affect(var,exp) -> update s (evalA exp s) var
  | Seq(prog1,prog2) -> if prog1=Nop
                        then evalW prog2 s
                        else let s1 = evalW prog1 s in
                             evalW prog2 s1
  | If(cond,prog1,prog2) -> let evalcond=evalA cond s in
                            if evalcond=1 then evalW prog1 s
                                          else evalW prog2 s


 |While(cond,prog1) -> let evalcond=evalA cond s in
                       if evalcond=1
                       then let s1= evalW prog1 s in
                            evalW (While(cond,prog1)) s1
                       else s;;



let (final : string  -> state) = fun s ->
  let programme=pr_SI (list_of_string s) in
  let (e,char)=programme in
  evalW e [];;



(* Test sur les affectations *)
let resultp7 = let (exp,c)=p7 in evalW exp [];;





(* Test différents programmes *)


let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then []
    else s.[i] :: boucle (i+1)
  in boucle 0
;;

let test s= pr_SI (list_of_string s);;

(* Exécution else *)
let test_prog1 = test "a:=0;b:=1;c:=1;i(!c){c:=0;a:=b}{b:=0;c:=a}"

let result1 =  let (exp,c)=test_prog1 in evalW exp [];;

let test_final1 = final "a:=0;b:=1;c:=1;i(!c){c:=0;a:=b}{b:=0;c:=a}";;

(* Exécution then *)
let test_prog2 = test "a:=0;b:=1;c:=1;i(c){c:=0;a:=b}{b:=0;c:=a}"

let result2 =  let (exp,c)=test_prog2 in evalW exp [];;

let test_final2 = final "a:=0;b:=1;c:=1;i(c){c:=0;a:=b}{b:=0;c:=a}";;

(* Test while avec passage 2 fois dans la boucle, une fois dans le else puis dans le then *)
let test_prog3= test "a:=0;b:=1;c:=1;w(!a){i(!c){c:=0;a:=1}{b:=0;c:=a}}"

let result3 =  let (exp,c)=test_prog3 in evalW exp [];;

let test_final3 = final "a:=0;b:=1;c:=1;w(!a){i(!c){c:=0;a:=1}{b:=0;c:=a}}";;

(* Test booléen *)

let test_prog4= test "a:=0;b:=1;c:=1;w(!a){i(c.b){c:=0;a:=1}{b:=0;c:=a}}"
let result4 =  let (exp,c)=test_prog4 in evalW exp [];;

let test_final4 = final  "a:=0;b:=1;c:=1;w(!a){i(c.b){c:=0;a:=1}{b:=0;c:=a}}";;

let test_prog5= test "a:=0;b:=0;c:=1;w(!a){i(a+b){c:=0;a:=1}{b:=0;c:=a;a:=1}}"
let result5 =  let (exp,c)=test_prog5 in evalW exp [];;

let test_final5 = final  "a:=0;b:=0;c:=1;w(!a){i(a+b){c:=0;a:=1}{b:=0;c:=a;a:=1}}";;
