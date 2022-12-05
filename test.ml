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

type cons = Zero | Un

type expr = Var of var | Cons of cons;;

type prog = Nop | Affect of var * expr | Seq of prog * prog | If of expr * prog * prog | While of expr * prog;;

(*Donner une grammaire décrivant le langage WHILEb-- sans recursivité gauche)*)

(* Question 1.1.2 - 1.1.3

  Grammaire du langage WHILEb--:
  
  
  C :: '1' | '0' 
  V :: 'a' | 'b' | 'c' | 'd'
  A :: V.':'.'='.(CV)
  I :: 'w'.'('.V.')'.'{'.(SI).'}' | 'i'.'('.V.')'.'{'.(SI).'}'.'{'.(SI).'}'
  P :: ε | I | A.P
  S :: A.';'.S | A.';'.I.S | I.S |ε
  CV:: C | V
  SI:: S | I 

*)


(*Implémenter un analyseur syntaxique en OCaml pour la grammaire du langage
WHILEb--. Utiliser des combinateurs d'analyseurs *)

(* Le type des aspirateurs de listes de caractères  *)
type analist = char list -> char list

(*type 'term analist = 'term list -> 'term list*)
exception Echec

(* terminal constant *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : analist = fun l -> l

(* Composition séquentielle : a1 suivi de a2 *)
let (-->) (a1 : analist) (a2 : analist) : analist =
  fun l -> let l = a1 l in a2 l

(* Choix entre a1 ou a2 *)
let (-|) (a1 : analist) (a2 : analist) : analist =
  fun l -> try a1 l with Echec -> a2 l

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type ('res, 'term) ranalist = 'term list -> 'res * 'term list

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec

(* a1 sans résultat suivi de a2 donnant un résultat *)
let ( -+>) (a1 : 'term analist) (a2 : ('res, 'term) ranalist) :
     
      ('res, 'term) ranalist =
  fun l -> let l = a1 l in a2 l 


let (+->) (a1 : ('res,'term) ranalist ) (a2 : 'term analist) : ('res, 'term) ranalist =
  fun l -> let (rep,l) = a1 l in let l =a2 l in (rep,l);;

let (++>) (a1 : ('resa, 'term) ranalist) (a2 : 'resa -> ('resb, 'term) ranalist) :
      ('resb, 'term) ranalist =
  fun l -> let (x, l) = a1 l in a2 x l

(* a1 rendant un résultat suivi de a2 sans résultat est peu utile *)

(* Choix entre a1 ou a2 informatifs *)
let (+|) (a1 : ('res, 'term) ranalist) (a2 : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> try a1 l with Echec -> a2 l

(* ==================================================================== *)
(* Facultatif *)

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let (<<) f g = fun x -> f (g x)
let (>>) f g = fun x -> g (f x)

(* Pipeline right to left*)
let star_pipe_R2L (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f << f_star) )
      +|
        epsilon_res (fun x -> x)
    ) l
  in a_star

let star_R2L (a : ('r -> 'r, 'term) ranalist) (r0 : 'r) : ('r, 'term) ranalist =
  star_pipe_R2L a ++> fun f -> epsilon_res (f r0)

(* Special case: building lists *)
let star_list (a : ('a, 'term) ranalist) : ('a list, 'term) ranalist =
  star_R2L (a ++> fun x -> epsilon_res (fun l -> x :: l)) []

(* Pipeline left to right*)
let star_pipe_L2R (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f >> f_star) )
      +|
        epsilon_res (fun x -> x)
    ) l
  in a_star

let star_L2R (r0 : 'r) (a : ('r -> 'r, 'term) ranalist) : ('r, 'term) ranalist =
  star_pipe_L2R a ++> fun f -> epsilon_res (r0 |> f)



(*  C :: '1' | '0' *)
let pa_C  =
                      (terminal '0') -| ( terminal '1');;


(* V :: 'a' | 'b' | 'c' | 'd'*)


 
let pa_V=
     terminal 'a' -| terminal 'b' -| terminal 'c' -| terminal 'd';;

(* CV :: C | V *)

let pa_CV = fun l -> l|>
    pa_C -| pa_V ;; 


(* A :: V.':'.'='.(CV) *)

let pa_A = fun l -> l|>
  (pa_V --> terminal ':' --> terminal '=' --> pa_CV) ;;

(* I :: 'w'.'('.V.')'.'{'.(SI).'}' | 'i'.'('.V.')'.'{'.(SI).'}'.'{'.(SI).'}' *)

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


      (* SI:: S | I *)


(*  S :: A.';'.S | A.';'.I.S | I.S |ε *)


(* type var = A | B | C | D;;

type expr = Var of var | Zero | Un;;

type prog = Nop | Affect of var * expr | Seq of prog * prog | If of expr * prog * prog | While of expr * prog;;*)


let pr_C : (cons,char) ranalist = fun l ->
  l|>
  (terminal '1' -+> epsilon_res Un) +| (terminal '0' -+> epsilon_res Zero);;




let pr_V : (var,char) ranalist = fun l ->
 l|>
  (terminal 'a' -+> epsilon_res A) +| (terminal 'b'  -+> epsilon_res B) +|
    (terminal 'c'  -+> epsilon_res C) +| (terminal 'd'  -+> epsilon_res D) ;;




 let pr_CV : (expr,char) ranalist  = fun l -> l|>
   (pr_C ++> fun c -> epsilon_res (Cons c)) +| (pr_V ++> fun v -> epsilon_res (Var v)) ;;


    

 
let pr_A : (prog, char) ranalist  = fun l -> l|>
  ((pr_V +-> terminal ':'  +-> terminal '=' ++> pr_CV) --> fun e -> espilon_res Affect(v,e)) ;;


let rec pr_I = fun l -> l|>
   (terminal_res 'w'  --> terminal '(' -+> pr_V --> terminal ')'--> terminal '{' --> pr_SI --> terminal '}' ++> fun w -> epsilon_res (While(e,p)))
   +|
     terminal 'i' -+> fun i -> epsilon_res (If(e,p1,p2)) --> terminal '(' -+> pa_V --> terminal ')' --> terminal '{' -+> pr_SI +-> terminal '}' 
   --> terminal '{' -+> pr_SI +-> terminal '}'
and  pr_SI = fun l -> l|>  pr_S ++> fun s -> espilon_res Seq(p1,p2) +| pr_I ++> fun i -> epsilon_res If(e,p1,p2)
and  pr_S = fun l -> l|>
   (pr_A  +-> terminal ';' -+> pr_S) -|
   (pr_A --> terminal ';' --> pr_I --> pr_S) -|
     ( pr_I --> pr_S);;
