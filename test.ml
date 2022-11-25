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

(*Définir une hiérarchie de types OCaml permettant de représenter tous les programmes admis par WHILEb--.*)

type var = A | B | C | D;;

type expr = Var of var | Zero | Un;;

type prog = Nop | Affect of var * expr | Seq of prog * prog | If of expr * prog * prog | While of expr * prog;;

