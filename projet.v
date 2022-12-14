(* TD9 - Sémantique petit pas                *)
(* Structural Operational Semantics (SOS)    *)
(*
Constitution du groupe : 
Louise GUERIN
Mathis Courant
Jérémy PUCCI
William ISABELLE


|-------+--------------+--------------+--------------+--------------|				
	William	Jérémy Mathis Louise
|-------+--------------+--------------+--------------+--------------|				
| 1.1.1 | | | | |	x	x	x	x
| 1.1.2 | | | | |	x	x	x	x
| 1.1.3 | | | | |	x	x	x	x
| 1.1.4 | | | | |	x	x	x	x
| 1.2.1 | | | | |	x	x	x	x
|-------+--------------+--------------+--------------+--------------|				
| 2.1.1 | | | | |	x	x	x	x
| 2.1.2 | | | | |	x	x	x	x
| 2.1.3 | | | | |	x	x	x	x
| 2.1.4 | | | | |				
| 2.2.1 | | | | |	x	x	x	x
| 2.2.2 | | | | |	x	x	x	x
| 2.3.1 | | | | |				x
| 2.3.2 | | | | |				x
| 2.3.3 | | | | |				
| 2.4.1 | | | | |	x	x	x	x
| 2.4.2 | | | | |	x	x	x	x
| 2.4.3 | | | | |	x	x	x	x
| 2.4.4 | | | | |				
|-------+--------------+--------------+--------------+--------------|				
| 3.1 | | | | |				
| 3.2 | | | | |				
| 3.3.1 | | | | |				
| 3.3.2 | | | | |				
| 3.3.3 | | | | |				
| 3.4 | | | | |				
| 3.5 | | | | |				
| 3.6 | | | | |				
| 3.7.1 | | | | |				
| 3.7.2 | | | | |				
| 3.7.3 | | | | |				
| 3.7.4 | | | | |				
| 3.7.5 | | | | |				
| 3.8 | | | | |				
| 3.9 | | | | |				
|-------+--------------+--------------+--------------+--------------|				
*)


(* On importe les bibliothèques de Coq utiles pour le TD   *)

Require Import Bool Arith List.
Import List.ListNotations.

(* ========================================================================== *)
(** * Préliminaires *)
(** ** Syntaxe des expressions arithétiques *)

Inductive aexp :=
| Aco : nat -> aexp (** constantes *)
| Ava : nat -> aexp (** variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive bexp :=
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp    (* test égalité de bexp *)
| Beqnat : aexp -> aexp -> bexp (* test égalité de aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive winstr :=
| Skip   : winstr
| Assign : nat -> aexp -> winstr
| Seq    : winstr -> winstr -> winstr
| If     : bexp -> winstr -> winstr -> winstr
| While  : bexp -> winstr -> winstr
.

(* -------------------------------------------------- *)
(** ** États *)

Definition state := list nat.


Fixpoint get (x:nat) (s:state) : nat :=
  match x,s with
  | 0   , v::_      => v
  | S x1, _::l1 => get x1 l1
  | _   , _         => 0
  end.


Fixpoint update (s:state) (v:nat) (n:nat): state :=
  match v,s with
  | 0   , a :: l1 => n :: l1
  | 0   , nil     => n :: nil
  | S v1, a :: l1 => a :: (update l1 v1 n)
  | S v1, nil     => 0 :: (update nil v1 n)
  end.

(* ----------------------------------------------- *)
(** ** Sémantique fonctionnelle de aexp et de bexp *)

Fixpoint evalA (a: aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.


(* ========================================================================== *)

(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

Inductive config :=
| Inter : winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: winstr -> state -> config -> Prop :=
| SOS_Skip     : forall s,
    SOS_1 Skip s (Final s)

| SOS_Assign   : forall x a s,
    SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS_Seqf     : forall i1 i2 s s1,
    SOS_1 i1 s (Final s1) ->
    SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
    SOS_1 i1 s (Inter i1' s1) ->
    SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS_If_true  : forall b i1 i2 s,
    evalB b s = true  ->
    SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS_If_false : forall b i1 i2 s,
    evalB b s = false ->
    SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS_While    : forall b i s,
    SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
    SOS_1 i1 s1 c2 -> SOS c2 c3 ->
    SOS (Inter i1 s1) c3.


(* ========================================================================== *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.


(** * I *)

(** *** Calcul du carré avec des additions *)
(** On code dans While un programme Pcarre correspondant à
    while not (i=n) do {i:= 1+i; x:= y+x ; y:= 2+y} *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
(** Nouveau : on peut jouer avec des programmes qui bouclent *)
Definition Pcarre_inf := While Btrue corps_carre.

Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again. 
  {apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {cbv[corps_carre]. apply SOS_Seqi. apply SOS_Seqf. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. cbv[incrX]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. cbn. cbv[incrY]. apply SOS_Assign. }
  eapply SOS_stop.
Qed.

(****************************************************************************
Ce théorème montre que Pcarre_inf mène d’un état avec i = 0, x = 0 et y = 1 à une configuration intermédiaire
où Pcarre_inf peut être exécuté en partant d’un état avec i = 1, x = 1 et y = 3.
 ****************************************************************************)
Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again.
  {apply SOS_While. }
  eapply SOS_again. 
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {apply SOS_Seqi. cbv[corps_carre]. apply SOS_Seqf. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  {apply SOS_Seqi. cbn. apply SOS_Seqf. cbv[incrX]. apply SOS_Assign. }
  eapply SOS_again.
  { cbn. apply SOS_Seqf. cbv[incrY]. apply SOS_Assign. }
  eapply SOS_stop.
Qed.

Theorem SOS_Pcarre_2_V0 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { cbv[corps_carre]. apply SOS_Seqi. apply SOS_Seqf. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. cbn. apply SOS_Seqf. cbv[incrX]. apply SOS_Assign.  }
  eapply SOS_again.
  { cbn. apply SOS_Seqf. cbv[incrY].  apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  {apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. cbn. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. cbn. cbv[incrX]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. cbn. cbv[incrY]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_false. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  eapply SOS_stop.
Qed.


(** Le but de la suite est d'éviter les redites, puis éventuellement
    de considérer le cas général Pcarre. *)

(** Propriété essentielle de SOS, qui a un intérêt pratique. *)
Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  intros.
  induction H.
  - apply H0.
  - eapply SOS_again.
    + apply H.
    + apply IHSOS. apply H0.
Qed.

(** Il n'est pas demandé de faire celui-ci
    (bien qu'un copié-collé d'un lemme précédent fonctionne). *)
(****************************************************************************
Ce lemme montre que Pcarre_2 mène d’un état avec i = 1, x = 1 et y = 3 à une configuration intermédiaire
où Pcarre_2 peut être exécuté en partant d’un état avec i = 2, x = 4 et y = 5.
 ****************************************************************************)
Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
    eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again. 
  {apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {cbv[corps_carre]. apply SOS_Seqi. apply SOS_Seqf. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. cbv[incrX]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. cbn. cbv[incrY]. apply SOS_Assign. }
  eapply SOS_stop.
Qed.

(****************************************************************************
Ce théorème montre que Pcarre_2 mène d’un état avec i = 2, x = 4 et y = 5 à un état final avec i = 2, x = 4 et y = 5
 ****************************************************************************)
Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  eapply SOS_again.
  { cbv[Pcarre_2]. cbv[corps_carre]. apply SOS_While.
  }
  eapply SOS_again.
  { apply SOS_If_false. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  eapply SOS_stop.
Qed.


(** Même énoncé que SOS_Pcarre_2_V0. Utiliser SOS_trans *)
Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
  - apply SOS_Pcarre_2_1er_tour.
  - apply SOS_trans with (Inter Pcarre_2 [2; 4; 5] ).
    + apply SOS_Pcarre_2_2e_tour.
    + apply SOS_Pcarre_2_fini.
Qed.

(** Généralisation à Pcarre *)

(** On a besoin de deux lemmes arithmétiques, démontrables avec la tactique ring. *)
Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].

(*********************************************************************
Ce théorème montre que corps_carre avec i = n, x = n*n et y = n + n + 1 mène à
l'état final avec i = n+1, x = (n+1)*(n+1) et y = (n+1) + (n+1) + 1
 *********************************************************************)
Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  eapply SOS_again.
  { cbv[corps_carre]. apply SOS_Seqf. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { cbn. apply SOS_Seqf. cbv[incrX]. apply SOS_Assign. }
  eapply SOS_again.
  { cbn. cbv[incrY]. apply SOS_Assign. }
  cbn. rewrite <- Sn_carre. rewrite <- Sn_2. cbv[invar_cc].
  eapply SOS_stop.
Qed. 



(** Celui-ci est court mais difficile. Laisser Admitted au début. *)
(*
 *************************************************************************************************
Pour toutes instructions i1, i2 et états s1, s2,
tels que l'instruction intermédiare i1 avec l'état s1 mène à l'état final s2,

La séquence intermédiare d'instructions i1 i2 à l'état s1 mène à une configuration où i2 peut être exécuté avec l'état s2

*************************************************************************************************
*)
Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
Admitted.

(************************************************************************************************
Pour toute instruction I et entier n, la séquence des instructions corps_carre et I avec l'état i = n, x = n*n et y = n + n + 1 mène à la configuration intermédaire de où I peut être exécuté avec i = n+1, x = (n+1)*(n+1) et y = (n+1) + (n+1) + 1
 ************************************************************************************************)
(** Réutiliser les lemmes précédents (facile et très court). *)
Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  apply SOS_seq.
  apply SOS_corps_carre.
Qed.


Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
  intros.
  induction n.
  - cbn. reflexivity.
  - apply IHn.
Qed.

(*******************************************************************
Pour tout entiers n m,
(Pcarre n) mène d’un état avec i = m, x = m*m et y = m+m+1 à une configuration intermédiaire
où (Pcarre n) peut être exécuté en partant d’un état avec i = m+1, x = (m+1)*(m+1) et y = (m+1)+(m+1)+1.
 *******************************************************************)
(** Réutiliser les lemmes précédents (facile). *)
Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
              SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros. cbv[Pcarre]. eapply SOS_again.
  { eapply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_true. cbn. rewrite H. cbn. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(*******************************************************************
Pour tout entier n,
(Pcarre n) mène d’un état avec i = n, x = n*n et y = n+n+1 à une configuration intermédiaire
où (Pcarre n) peut être exécuté en partant d’un état avec i = n, x = n*n et y = n+n+1.
 *******************************************************************)
(** Facile *)
Theorem SOS_Pcarre_n_fini :
  forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intros.
  cbv[Pcarre]. eapply SOS_again.
  { eapply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_false. cbn. rewrite eqnatb_refl. cbn. reflexivity. }
  eapply SOS_again.
  { eapply SOS_Skip. }
  eapply SOS_stop.
Qed.

(********************************************************************
On a :
SOS (Inter Pcarre_2 [0; 0; 1]) (Inter Pcarre_2 [1; 1; 3])
,
SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5])
et
SOS (Inter Pcarre_2 [2; 4; 5]) (Final Pcarre_2 [2; 4; 5])

Donc, par transitivités successives :
SOS (Inter Pcarre_2 [0; 0; 1]) (Final Pcarre_2 [2; 4; 5])
 ********************************************************************)
Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof. 
  eapply SOS_trans. 
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. }
  apply SOS_stop.
Qed.

(*******************************************************************
Pour tout entier n,
Pcarre_inf mène d’un état avec i = n, x = n*n et y = n+n+1 à une configuration intermédiaire
où Pcarre_inf peut être exécuté en partant d’un état avec i = n+1, x = (n+1)*(n+1) et y = (n+1)+(n+1)+1.
 *******************************************************************)
(** On peut dire des choses sur la version qui boucle. *)
Lemma SOS_Pcarre_inf_tour :
  forall i,
    SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intros.
  cbv[Pcarre_inf]. eapply SOS_again.
  { eapply SOS_While. }
  eapply SOS_again.
  { eapply SOS_If_true. cbn. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(*******************************************************************
Pour tout entier n,
Pcarre_inf mène d’un état avec i = 0, x = 0 et y = 1 à une configuration intermédiaire
où Pcarre_inf peut être exécuté en partant d’un état avec i = n, x = n*n et y = n+n+1.
 *******************************************************************)
Theorem SOS_Pcarre_inf_n :
  forall i,
    SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  induction i.
  apply SOS_stop.
  eapply SOS_trans.
  + apply IHi.
  + apply SOS_Pcarre_inf_tour.
Qed.


(** Énoncer et démontrer le théorème général pour Pcarre *)

(* ========================================================================== *)


(** * II *)

(** ** Définir une version fonctionnelle de SOS_1 *)
Fixpoint f_SOS_1 (i : winstr) (s : state) : config :=
  match i with
  | Skip => Final s
  | Assign x a => Final (update s x (evalA a s))
  | Seq i1 i2 => let c1:=f_SOS_1 i1 s in
                 match c1 with
                 | Inter i1' s' => Inter (Seq i1' i2) s'
                 | Final s' => Inter i2 s'
                 end
  | If b i1 i2 => if evalB b s then Inter i1 s else Inter i2 s
  | While b i => Inter (If b (Seq i (While b i)) Skip) s
end.

(** ** Utilisation de f_SOS_1 pour éviter les eapply SOS_again *)

(** PC = pt de contrôle *)
Definition PC0 := Pcarre_2.
Eval cbn in (f_SOS_1 PC0 [0;0;1]).

(** Il faut un peu désosser le code pour y retrouver les points de contrôle *)

Definition PC2 := Seq corps_carre PC0.
Definition PC1 := If (Bnot (Beqnat Ir (Aco 2))) PC2 Skip.
Definition PC3 := Seq (Seq incrX incrY) PC0.
Definition PC4 := Seq incrY PC0.

(** On vérifie la progression *)
Fact fa1 : f_SOS_1 PC0 [0;0;1] = Inter PC1 [0;0;1]. reflexivity. Qed.
Eval cbn in (f_SOS_1 PC1 [0;0;1]).
(** Continuer, on retombe sur PC0 après quelques étapes. *)

(** Utilisation sur un lemme SOS *)
Lemma SOS_Pcarre_2_1er_tour_V1 :
  SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  change Pcarre_2 with PC0.
  apply SOS_again with (f_SOS_1 PC0 [0; 0; 1]).
  { apply SOS_While. }
  apply SOS_again with (f_SOS_1 PC1 [0;0;1]).
  { apply SOS_If_true. reflexivity. }
  cbn.
  apply SOS_again with (f_SOS_1 PC2 [0;0;1]).
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  apply SOS_again with (f_SOS_1 PC3 [1;0;1]).
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  apply SOS_again with (f_SOS_1 PC4 [1;1;1]).
  { apply SOS_Seqf. apply SOS_Assign. }    
  apply SOS_stop.
Qed.

(** ** Théorèmes généraux reliant SOS_1 et f_SOS_1 *)

(** Court mais non trivial. *)
Lemma f_SOS_1_corr : forall i s, SOS_1 i s (f_SOS_1 i s).
Proof.
Admitted.

(** Court. Attention : utiliser la tactique injection. *)
Lemma f_SOS_1_compl : forall i s c, SOS_1 i s c -> c = f_SOS_1 i s.
Proof.
Admitted.
