(*
Copyright 2019 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype.
From pcm Require Import options axioms pred prelude.

(**************************************************)
(* This file develops some basic domain theory of *)
(* posets, complete lattices, complete partial    *)
(* orders (CPOs). It developes the standard fixed *)
(* point theorems: Knaster-Tarski's for complete  *)
(* lattices, and Kleene's for CPOs.               *)
(**************************************************)

(**********)
(* Posets *)
(**********)

Definition poset_axiom T (leq : T -> T -> Prop) := 
  [/\ forall x, leq x x, 
      forall x y, leq x y -> leq y x -> x = y &
      forall x y z, leq x y -> leq y z -> leq x z].

HB.mixin Record isPoset T := {
  poset_leq : T -> T -> Prop;
  poset_subproof : poset_axiom poset_leq}.

#[short(type="poset")]
HB.structure Definition Poset := {T of isPoset T}.

Notation "x <== y" := (poset_leq x y) (at level 70).

Section Repack.
Variable T : poset.
Lemma poset_refl (x : T) : x <== x.
Proof. by case: (@poset_subproof T). Qed.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Proof. by case: (@poset_subproof T)=>_ H _; apply: H. Qed.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
Proof. by case: (@poset_subproof T)=>_ _; apply. Qed.
End Repack.

#[export] Hint Resolve poset_refl : core.

Add Parametric Relation (T : poset) : T (@poset_leq T)
  reflexivity proved by (@poset_refl _)
  transitivity proved by (fun x y => @poset_trans _ y x) as poset_rel.

(**********************)
(* monotone functions *)
(**********************)

Definition monofun_axiom (T1 T2 : poset) (f : T1 -> T2) :=
  forall x y, x <== y -> f x <== f y.

HB.mixin Record isMonoFun (T1 T2 : poset) (f : T1 -> T2) := {
  monofun_subproof : monofun_axiom f}.

#[short(type="mono_fun")]
HB.structure Definition MonoFun (T1 T2 : poset) := 
  {f of isMonoFun T1 T2 f}.

Lemma monofunP (T1 T2 : poset) (f : mono_fun T1 T2) x y : 
        x <== y -> f x <== f y.
Proof. exact: monofun_subproof. Qed.

(**************************)
(* some basic definitions *)
(**************************)

Section IdealDef.
Variable T : poset.

Structure ideal (P : T) := Ideal {id_val : T; id_pf : id_val <== P}.

(* Changing the type of the ideal *)

Lemma relaxP (P1 P2 : T) : P1 <== P2 -> forall p, p <== P1 -> p <== P2.
Proof. by move=>H1 p H2; apply: poset_trans H1. Qed.

Definition relax (P1 P2 : T) (x : ideal P1) (pf : P1 <== P2) :=
  Ideal (relaxP pf (id_pf x)).

End IdealDef.

(***********************)
(* poset constructions *)
(***********************)

Section SubPoset.
Variables (T : poset) (s : Pred T).
Local Notation tp := {x : T | x \In s}.

Definition sub_leq (p1 p2 : tp) := sval p1 <== sval p2.

Lemma sub_is_poset : poset_axiom sub_leq.
Proof. 
split=>[x|[x Hx][y Hy]|[x Hx][y Hy][z Hz]]; rewrite /sub_leq //=.
- move=>H1 H2; rewrite -(poset_asym H1 H2) in Hy *.
  by rewrite (pf_irr Hx).
by apply: poset_trans.
Qed.
HB.instance Definition _ := isPoset.Build tp sub_is_poset.
End SubPoset.

(* pairing of posets *)

Section ProdPoset.
Variables A B : poset.
Local Notation tp := (A * B)%type.

Definition poset_prod_leq := 
  [fun p1 p2 : tp => p1.1 <== p2.1 /\ p1.2 <== p2.2].

Lemma prod_is_poset : poset_axiom poset_prod_leq.
Proof. 
split=>[//|[x1 x2][y1 y2]|[x1 x2][y1 y2][z1 z2]] /=.
- by case=>H1 H2 [H3 H4]; congr (_, _); apply: poset_asym.
case=>H1 H2 [H3 H4]; split; 
by [apply: poset_trans H3|apply: poset_trans H4].
Qed.
HB.instance Definition _ := isPoset.Build tp prod_is_poset.
End ProdPoset.

(* functions into poset form a poset *)

Section FunPoset.
Variable (A : Type) (B : poset).
Local Notation tp := (A -> B).

Definition poset_fun_leq := [fun p1 p2 : tp => forall x, p1 x <== p2 x].

Lemma fun_is_poset : poset_axiom poset_fun_leq.
Proof.
split=>[x|x y H1 H2|x y z H1 H2 t] //=.
- by apply: fext=>z; apply: poset_asym; [apply: H1|apply: H2].
by apply: poset_trans (H2 t). 
Qed.
HB.instance Definition _ := isPoset.Build tp fun_is_poset.
End FunPoset.

(* dependent functions into a poset form a poset *)

Section DFunPoset.
Variables (A : Type) (B : A -> poset).
Local Notation tp := (forall x, B x).

Definition poset_dfun_leq := [fun p1 p2 : tp => forall x, p1 x <== p2 x].

Lemma dfun_is_poset : poset_axiom poset_dfun_leq.
Proof.
split=>[x|x y H1 H2|x y z H1 H2 t] //.
- by apply: fext=>z; apply: poset_asym; [apply: H1|apply: H2].
by apply: poset_trans (H2 t). 
Qed.

(* no instance declaration, since it's keyed on forall *)
(* and forall is not a symbol *)
Definition dfun_poset_mix := isPoset.Build tp dfun_is_poset.
Definition dfun_poset : poset := Poset.pack_ dfun_poset_mix.
End DFunPoset.

(* ideal of poset is poset *)

Section IdealPoset.
Variable (T : poset) (P : T).

Definition poset_ideal_leq := 
  [fun p1 p2 : ideal P => id_val p1 <== id_val p2].

Lemma ideal_is_poset : poset_axiom poset_ideal_leq.
Proof.
split=>[[x]|[x1 H1][x2 H2]|[x1 H1][x2 H2][x3 H3]] //=.
- move=>H3 H4; rewrite (poset_asym H3 H4) in H1 H2 *.
  by rewrite (pf_irr H1).
by apply: poset_trans. 
Qed.
HB.instance Definition _ := isPoset.Build (ideal P) ideal_is_poset.
End IdealPoset.

(* Prop is poset *)
Definition poset_prop_leq := [fun p1 p2 : Prop => p1 -> p2].
Lemma prop_is_poset : poset_axiom poset_prop_leq.
Proof. by split=>[x|x y H1 H2|x y z H1 H2 /H1] //; apply: pext. Qed.
HB.instance Definition _ := isPoset.Build Prop prop_is_poset.


(*********************)
(* Complete lattices *)
(*********************)

Definition lattice_axiom (T : poset) (sup : Pred T -> T) := 
  [/\ (* sup is upper bound *)
      forall (s : Pred T) x, x \In s -> x <== sup s &
      (* sup is least upper bound *)
      forall (s : Pred T) x,
        (forall y, y \In s -> y <== x) -> sup s <== x].  

HB.mixin Record isLattice T of Poset T := {
  sup : Pred T -> T; 
  lattice_subproof : lattice_axiom sup}.

#[short(type="lattice")]
HB.structure Definition Lattice := {T of Poset T & isLattice T}.

Section Repack.
Variable T : lattice.
Lemma supP (s : Pred T) x : x \In s -> x <== sup s.
Proof. by case: (@lattice_subproof T)=>H _; apply: H. Qed.
Lemma supM (s : Pred T) x : (forall y, y \In s -> y <== x) -> sup s <== x.
Proof. by case: (@lattice_subproof T)=>_; apply. Qed.
End Repack.

(* infima follow *)
Section Infimum.
Variable T : lattice.

Definition inf (s : Pred T) := 
  sup [Pred x : T | forall y, y \In s -> x <== y].

Lemma infP s x : x \In s -> inf s <== x.
Proof. by move=>H; apply: supM=>y; apply. Qed.

Lemma infM s x : (forall y, y \In s -> x <== y) -> x <== inf s.
Proof. by apply: supP. Qed.

End Infimum.

(* least and greatest fixed points by Knaster-Tarski construction *)
Section KnasterTarskiDefs.
Variable T : lattice.

Definition lbot : T := sup Pred0.

Definition tarski_lfp (f : T -> T) := inf [Pred x : T | f x <== x].
Definition tarski_gfp (f : T -> T) := sup [Pred x : T | x <== f x].

Definition sup_closed (T : lattice) :=
  [Pred s : Pred T | forall d, d <=p s -> sup d \In s].

Definition sup_closure (T : lattice) (s : Pred T) :=
  [Pred p : T | forall t : Pred T, s <=p t -> t \In sup_closed T -> p \In t].

End KnasterTarskiDefs.

Arguments lbot {T}.
Arguments sup_closed {T}.
Arguments sup_closure [T] s.
Prenex Implicits sup_closed sup_closure.

Section BasicProperties.
Variable T : lattice.

Lemma sup_mono (s1 s2 : Pred T) : s1 <=p s2 -> sup s1 <== sup s2.
Proof. by move=>H; apply: supM=>y /H/supP. Qed.

Lemma supE (s1 s2 : Pred T) : s1 =p s2 -> sup s1 = sup s2.
Proof. by move=>H; apply: poset_asym; apply: supM=>y /H/supP. Qed.

(* Knaster-Tarski theorem *)
Lemma tarski_lfp_fixed (f : mono_fun T T) :
        f (tarski_lfp f) = tarski_lfp f.
Proof.
suff L : f (tarski_lfp f) <== tarski_lfp f.
- by apply: poset_asym=>//; apply/infP/monofunP. 
by apply: infM=>x L; apply: poset_trans (L); apply/monofunP/infP.
Qed.

Lemma tarski_lfp_least f (x : T) : f x <== x -> tarski_lfp f <== x.
Proof. by move=>H; apply: infP. Qed.

Lemma tarski_gfp_fixed (f : mono_fun T T) :
        f (tarski_gfp f) = tarski_gfp f.
Proof.
suff L: tarski_gfp f <== f (tarski_gfp f).
- by apply: poset_asym=>//; apply/supP/monofunP.
by apply: supM=>x L; apply: poset_trans (L) _; apply/monofunP/supP.
Qed.

Lemma tarski_gfp_greatest f (x : T) : x <== f x -> x <== tarski_gfp f.
Proof. by move=>H; apply: supP. Qed.

Lemma tarski_lfp_mono (f1 : T -> T) (f2 : mono_fun T T) :
        f1 <== f2 -> tarski_lfp f1 <== tarski_lfp f2.
Proof.
move=>H; apply: infP; apply: poset_trans (H (tarski_lfp f2)) _.
by rewrite tarski_lfp_fixed.
Qed.

Lemma tarski_gfp_mono (f1 : mono_fun T T) (f2 : T -> T) :
        (f1 : T -> T) <== f2 -> tarski_gfp f1 <== tarski_gfp f2.
Proof.
move=>H; apply/supP/poset_trans/(H (tarski_gfp f1)).
by rewrite tarski_gfp_fixed.
Qed.

(* closure contains s *)
Lemma sup_clos_sub (s : Pred T) : s <=p sup_closure s.
Proof. by move=>p H1 t H2 H3; apply: H2 H1. Qed.

(* closure is smallest *)
Lemma sup_clos_min (s : Pred T) :
        forall t, s <=p t -> sup_closed t -> sup_closure s <=p t.
Proof. by move=>t H1 H2 p; move/(_ _ H1 H2). Qed.

(* closure is closed *)
Lemma sup_closP (s : Pred T) : sup_closed (sup_closure s).
Proof.
move=>d H1 t H3 H4; move: (sup_clos_min H3 H4)=>{}H3.
by apply: H4=>x; move/H1; move/H3.
Qed.

Lemma sup_clos_idemp (s : Pred T) : sup_closed s -> sup_closure s =p s.
Proof. by move=>p; split; [apply: sup_clos_min | apply: sup_clos_sub]. Qed.

Lemma sup_clos_mono (s1 s2 : Pred T) :
        s1 <=p s2 -> sup_closure s1 <=p sup_closure s2.
Proof.
move=>H1; apply: sup_clos_min (@sup_closP s2).
by move=>t /H1; apply: sup_clos_sub.
Qed.

End BasicProperties.

(* lattice constructions *)

(* subset lattice *)
Section SubLattice.
Variables (T : lattice) (s : Pred T) (C : sup_closed s).
Local Notation tp := {x : T | x \In s}.

Definition lattice_sub_sup' (u : Pred tp) : T :=
  sup [Pred x : T | exists y, y \In u /\ x = sval y].
Lemma lattice_sub_supX (u : Pred tp) : lattice_sub_sup' u \In s.
Proof. by apply: C=>x [][y H][_] ->. Qed.
Definition lattice_sub_sup (u : Pred tp) : tp :=
  exist _ (lattice_sub_sup' u) (lattice_sub_supX u).

Lemma sub_is_lattice : lattice_axiom lattice_sub_sup.
Proof.
split=>u x H; first by apply: supP; exists x. 
by apply: supM=>y [z][H1] ->; apply: H H1.
Qed.
HB.instance Definition _ := isLattice.Build tp sub_is_lattice.
End SubLattice.

(* product *)
Section ProdLattice.
Variables (A B : lattice).
Local Notation tp := (A * B)%type.

Definition lattice_prod_sup (s : Pred tp) : tp :=
            (sup [Pred p | exists f, p = f.1 /\ f \In s],
             sup [Pred p | exists f, p = f.2 /\ f \In s]).

Lemma prod_is_lattice : lattice_axiom lattice_prod_sup.
Proof. 
split=>s p H; first by split; apply: supP; exists p. 
by split; apply: supM=>y [f][->]; case/H. 
Qed.
HB.instance Definition _ := isLattice.Build tp prod_is_lattice.
End ProdLattice.

(* functions into latice form lattice *)
Section FunLattice.
Variables (A : Type) (B : lattice).
Local Notation tp := (A -> B).

Definition lattice_fun_sup (s : Pred tp) : tp :=
  fun x => sup [Pred p | exists f, f \In s /\ p = f x].

Lemma fun_is_lattice : lattice_axiom lattice_fun_sup.
Proof.
split=>s p H x; first by apply: supP; exists p.
by apply: supM=>y [f][H1] ->; apply: H. 
Qed.
HB.instance Definition _ := isLattice.Build tp fun_is_lattice.
End FunLattice.

(* dependent functions into a lattice form a lattice *)
Section DFunLattice.
Variables (A : Type) (B : A -> lattice).
Local Notation tp := (dfun_poset B).

Definition lattice_dfun_sup (s : Pred tp) : tp :=
  fun x => sup [Pred p | exists f, f \In s /\ p = f x].

Lemma dfun_is_lattice : lattice_axiom lattice_dfun_sup.
Proof.
split=>s p H x; first by apply: supP; exists p.
by apply: supM=>y [f][H1] ->; apply: H. 
Qed.

Definition dfun_lattice_mix := isLattice.Build tp dfun_is_lattice.
Definition dfun_lattice : lattice := Lattice.pack_ dfun_lattice_mix.
End DFunLattice.

(* applied sup equals the sup of applications *)
Lemma sup_appE A (B : lattice) (s : Pred (A -> B)) (x : A) :
        sup s x = sup [Pred y : B | exists f, f \In s /\ y = f x].
Proof. by []. Qed.

Lemma sup_dappE A (B : A -> lattice) (s : Pred (dfun_lattice B)) (x : A) :
        sup s x = sup [Pred y : B x | exists f, f \In s /\ y = f x].
Proof. by []. Qed.

(* ideal of a lattice forms a lattice *)
Section IdealLattice.
Variables (T : lattice) (P : T).

Definition lattice_ideal_sup' (s : Pred (ideal P)) :=
  sup [Pred x | exists p, p \In s /\ id_val p = x].
Lemma lattice_ideal_supP' (s : Pred (ideal P)) : lattice_ideal_sup' s <== P.
Proof. by apply: supM=>y [[x]] H /= [_] <-. Qed.
Definition lattice_ideal_sup (s : Pred (ideal P)) := 
  Ideal (lattice_ideal_supP' s).

Lemma ideal_is_lattice : lattice_axiom lattice_ideal_sup.
Proof.
split=>s p H; first by apply: supP; exists p.
by apply: supM=>y [q][H1] <-; apply: H. 
Qed.
HB.instance Definition _ := isLattice.Build (ideal P) ideal_is_lattice.
End IdealLattice.

(* Prop is a lattice *)
Definition lattice_prop_sup (s : Pred Prop) : Prop := 
  exists p, p \In s /\ p.
Lemma prop_is_lattice : lattice_axiom lattice_prop_sup.
Proof. by split=>s p; [exists p|move=>H [r][]; move/H]. Qed. 
HB.instance Definition _ := isLattice.Build Prop prop_is_lattice.

(****************)
(* Monotonicity *)
(****************)

Section MonoCanonicals.
Variables T T1 T2 T3 S1 S2 : poset.

Lemma idfun_is_mono : monofun_axiom (@idfun T). Proof. by []. Qed.
HB.instance Definition _ := isMonoFun.Build T T idfun idfun_is_mono.

Definition const_fun (y : T2) (_ : T1) := y.
Lemma const_is_mono (y : T2) : monofun_axiom (const_fun y). Proof. by []. Qed.
HB.instance Definition _ y := 
  isMonoFun.Build T1 T2 (const_fun y) (const_is_mono y).

Lemma fst_is_mono : monofun_axiom (@fst T1 T2).
Proof. by case=>x1 x2 [y1 y2][]. Qed.
HB.instance Definition _ := isMonoFun.Build (T1*T2)%type T1 fst fst_is_mono.

Lemma snd_is_mono : monofun_axiom (@snd T1 T2).
Proof. by case=>x1 x2 [y1 y2][]. Qed.
HB.instance Definition _ := isMonoFun.Build (T1*T2)%type T2 snd snd_is_mono.

Definition diag (x : T) := (x, x).
Lemma diag_is_mono : monofun_axiom diag. Proof. by []. Qed.
HB.instance Definition _ := isMonoFun.Build T (T*T)%type diag diag_is_mono.

Lemma sval_is_mono (P : Pred T) : monofun_axiom (@sval T P). 
Proof. by []. Qed. 
HB.instance Definition _ P :=  
  isMonoFun.Build {x : T | P x} T sval (@sval_is_mono P).

Definition app A B (x : A) := fun f : A -> B => f x.
Lemma app_is_mono A (x : A) : monofun_axiom (@app A T x).
Proof. by move=>f1 f2; apply. Qed.
HB.instance Definition _ A x := 
  isMonoFun.Build (A -> T) T (@app A T x) (app_is_mono x).

Definition dapp A (B : A -> poset) (x : A) := fun f : dfun_poset B => f x.
Lemma dapp_is_mono A (B : A -> poset) (x : A) : monofun_axiom (@dapp A B x).
Proof. by move=>f1 f2; apply. Qed.
HB.instance Definition _ A B x := 
  isMonoFun.Build (dfun_poset B) (B x) (@dapp A B x) (dapp_is_mono x).

Section Comp.
Variables (f1 : mono_fun T2 T1) (f2 : mono_fun T3 T2).
Lemma comp_is_mono : monofun_axiom (f1 \o f2).
Proof. by move=>x y H; apply/monofunP/monofunP. Qed.
HB.instance Definition _ := isMonoFun.Build T3 T1 (f1 \o f2) comp_is_mono.
End Comp.

Section Prod.
Variables (f1 : mono_fun S1 T1) (f2 : mono_fun S2 T2).
Lemma funprod_is_mono : monofun_axiom (f1 \* f2).
Proof. by case=>x1 x2 [y1 y2][/= H1 H2]; split=>/=; apply: monofunP. Qed.
HB.instance Definition _ := 
  isMonoFun.Build (S1 * S2)%type (T1 * T2)%type (f1 \* f2) funprod_is_mono.
End Prod.
End MonoCanonicals.

Prenex Implicits diag app.

(**********)
(* Chains *)
(**********)

Definition chain_axiom (T : poset) (s : Pred T) :=
  (exists d, d \In s) /\
  (forall x y, x \In s -> y \In s -> x <== y \/ y <== x).

HB.mixin Record isChain (T : poset) (s : Pred T) := {
  chain_subproof : chain_axiom s}.
  
#[short(type="chain")]
HB.structure Definition Chain (T : poset) := {s of isChain T s}.

Arguments chain T%_type.

(* \In notation *)
Definition chain_pred (T : poset) (x : chain T) : Pred T := x.
Canonical chainPredType (T : poset) := PropPredType (@chain_pred T).

Lemma chainE (T : poset) (s1 s2 : chain T) : 
        s1 = s2 <-> chain_pred s1 =p chain_pred s2.
Proof.
split=>[->//|]; case: s1 s2=>s1 H1 [s2 H2] /= E; move: H1 H2.
suff: s1 = s2.
- move=>-> [[H1]][[H2]]; congr (Chain.Pack (Chain.Class _)).
  by rewrite (pf_irr H1).
by apply: fext=>x; apply: pext; split=> /E.
Qed.

Section ImageChain.
Variables (T1 T2 : poset) (f : mono_fun T1 T2) (s : chain T1).

Lemma image_is_chain : chain_axiom (Image f s).
Proof. 
case: s=>p [[[[d H1] H2]]] /=.
split=>[|x y]; first by exists (f d); exists d.
case=>x1 -> H3 [y1 -> H4]; rewrite -!toPredE /= in H3 H4.
by case: (H2 x1 y1 H3 H4)=>L; [left | right]; apply: monofunP L.
Qed.
HB.instance Definition _ := isChain.Build T2 (Image f s) image_is_chain.
End ImageChain.

Lemma id_chainE T (s : chain T) f : f =1 idfun -> Image f s =p s.
Proof.
move=>H x; split; first by case=>y ->; rewrite H.
by exists x=>//; rewrite H.
Qed.

Section ChainConst.
Variables (T1 T2 : poset) (y : T2).

Definition const_chain : Pred _ := xPred1 y.
Lemma const_is_chain : chain_axiom const_chain.
Proof. by split; [exists y | move=>x1 x2 ->->; left]. Qed.
HB.instance Definition _ := isChain.Build T2 const_chain const_is_chain.

Lemma const_chainE (s : chain T1) : Image (const_fun y) s =p const_chain.
Proof.
move=>z1; split; first by case=>z2 ->.
by case: s=>s [[[[d H1]] H2]] /= <-; exists d.
Qed.
End ChainConst.

Section ChainCompose.
Variables T1 T2 T3 : poset.
Variables (f1 : mono_fun T2 T1) (f2 : mono_fun T3 T2).
Variable s : chain T3.
Lemma comp_chainE : Image f1 (Image f2 s) =p Image (f1 \o f2) s.
Proof. by move=>x; apply: ImageIm. Qed.
End ChainCompose.

Section ProjChain.
Variables T1 T2 : poset.
Variables s : chain (T1 * T2).
Definition proj1_chain : Pred T1 := Image fst s.
HB.instance Definition _ := Chain.copy proj1_chain proj1_chain.
Definition proj2_chain : Pred T2 := Image snd s.
HB.instance Definition _ := Chain.copy proj2_chain proj2_chain.
End ProjChain.

Section DiagChain.
Variables (T : poset) (s : chain T).
Definition diag_chain : Pred (T * T) := Image diag s.
HB.instance Definition _ := Chain.copy diag_chain diag_chain.
End DiagChain.


(*********)
(* CPO's *)
(*********)

Definition cpo_axiom (T : poset) (bot : T) (lim : chain T -> T) := 
  [/\ forall x, bot <== x, 
      forall (s : chain T) x, x \In s -> x <== lim s &
      forall (s : chain T) x,
        (forall y, y \In s -> y <== x) -> lim s <== x].

HB.mixin Record isCPO T of Poset T := {
  bot : T; 
  lim_op : chain T -> T; 
  cpo_subproof: cpo_axiom bot lim_op}.

#[short(type="cpo")]
HB.structure Definition CPO := {T of Poset T & isCPO T}.

Definition limx (D : cpo) (s : chain D) of phantom (Pred _) s := lim_op s.
Notation lim s := (limx (Phantom (Pred _) s)).

Section Repack.
Variable D : cpo.
Lemma botP (x : D) : bot <== x.
Proof. by case: (@cpo_subproof D). Qed.
Lemma limP (s : chain D) x : x \In s -> x <== lim s.
Proof. by case: (@cpo_subproof D)=>_ H _; apply: H. Qed.
Lemma limM (s : chain D) x : (forall y, y \In s -> y <== x) -> lim s <== x.
Proof. by case: (@cpo_subproof D)=>_ _; apply. Qed.
End Repack.

#[export] Hint Resolve botP : core.

Lemma limE (D : cpo) (s1 s2 : chain D) : s1 =p s2 -> lim s1 = lim s2.
Proof. by move/chainE=>->. Qed.

(* common chain constructions *)

(* adding bot to a chain *)

Definition lift (D : cpo) (s : Pred D) : Pred D :=
  fun x => x = bot \/ x \In s.

Lemma lift_is_chain (D : cpo) (s : chain D) : chain_axiom (lift s).
Proof.
case: s=>p [[[[d H1]] H2]] /=.
split=>[|x y]; first by exists d; right.
by case=>[->|H3][->|H4]; auto.
Qed.

HB.instance Definition _ (D : cpo) (s : chain D) := 
  isChain.Build D (lift s) (@lift_is_chain D s).


(****************************)
(* common cpo constructions *)
(****************************)

(* products *)
Section ProdCPO.
Variables (A B : cpo).
Definition cpo_prod_bot := (@bot A, @bot B).
Definition cpo_prod_lim (s : chain (A * B)) := 
  (lim (Image fst s), lim (Image snd s)).

Lemma prod_is_cpo : cpo_axiom cpo_prod_bot cpo_prod_lim.
Proof.
split=>[x|s x|s x].
- by split; apply: botP. 
- by split; apply: limP; exists x. 
by split; apply: limM=>y [z ->]; case/H. 
Qed.
HB.instance Definition _ := isCPO.Build (A * B)%type prod_is_cpo.
End ProdCPO.

(* functions *)
Section FunCPO.
Variable (A : Type) (B : cpo).
Definition cpo_fun_bot (x : A) := @bot B.
Definition cpo_fun_lim (s : chain (A -> B)) x := 
  lim (Image (app x) s).

Lemma fun_is_cpo : cpo_axiom cpo_fun_bot cpo_fun_lim.
Proof.
split=>[f|s f|s f].
- by move=>y; apply: botP. 
- by move=>H t; apply: limP; exists f. 
by move=>H1 t; apply: limM=>y [g ->] H2; apply: H1. 
Qed.
HB.instance Definition _ := isCPO.Build (A -> B) fun_is_cpo.
End FunCPO.

(* dependent functions *)
Section DFunCPO.
Variables (A : Type) (B : A -> cpo).

Definition cpo_dfun_bot : dfun_poset B := fun x => bot.
Definition cpo_dfun_lim (s : chain (dfun_poset B)) : dfun_poset B :=
  fun x => lim (Image (dapp x) s).

Lemma dfun_is_cpo : cpo_axiom cpo_dfun_bot cpo_dfun_lim.
Proof.
split=>[x|s x|s x].
- by move=>y; apply: botP. 
- by move=>H t; apply: limP; exists x. 
by move=>H1 t; apply: limM=>y [f ->] H2; apply: H1. 
Qed.

Definition dfun_cpo_mix := isCPO.Build (dfun_poset B) dfun_is_cpo.
Definition dfun_cpo : cpo := CPO.pack_ dfun_cpo_mix.
End DFunCPO.

(* Prop *)
Definition cpo_prop_bot : Prop := False.
Definition cpo_prop_lim (s : chain Prop) : Prop := 
  exists p, p \In s /\ p.
Lemma prop_is_cpo : cpo_axiom cpo_prop_bot cpo_prop_lim.
Proof. by split=>[x|s p|s p H] //=; [exists p|case=>r []; move/H]. Qed.
HB.instance Definition _ := isCPO.Build Prop prop_is_cpo.

(* Pred *)
HB.instance Definition _ A := CPO.copy (Pred A) _.

(* every complete lattice is cpo *)
Section LatticeCPO.
Variable A : lattice. 

Definition lat_bot : A := lbot.
Definition lat_lim (s : Pred A) : A := sup s.

Lemma lat_is_cpo : cpo_axiom lat_bot lat_lim.
Proof. by split=>[x|s x|s x]; [apply: supM|apply: supP|apply: supM]. Qed.

(* no instance declaration as nothing to *)
(* hang the new structure onto *)
Definition lat_cpo_mix := isCPO.Build A lat_is_cpo.
Definition lat_cpo := CPO.pack_ lat_cpo_mix.
End LatticeCPO.

(* sub-CPO's *)

(* every chain-closed subset of a cpo is a cpo *)

Section AdmissibleClosure.
Variable T : cpo.

Definition chain_closed :=
  [Pred s : Pred T |
     bot \In s /\ forall d : chain T, d <=p s -> lim d \In s].

(* admissible closure of s is the smallest closed set containing s *)
(* basically extends s to include the sups of chains *)
Definition chain_closure (s : Pred T) :=
  [Pred p : T | forall t : Pred T, s <=p t -> chain_closed t -> p \In t].

(* admissible closure contains s *)
Lemma chain_clos_sub (s : Pred T) : s <=p chain_closure s.
Proof. by move=>p H1 t H2 H3; apply: H2 H1. Qed.

(* admissible closure is smallest *)
Lemma chain_clos_min (s : Pred T) t :
        s <=p t -> chain_closed t -> chain_closure s <=p t.
Proof. by move=>H1 H2 p; move/(_ _ H1 H2). Qed.

(* admissible closure is closed *)
Lemma chain_closP (s : Pred T) : chain_closed (chain_closure s).
Proof.
split; first by move=>t _ [].
move=>d H1 t H3 H4; move: (chain_clos_min H3 H4)=>{}H3.
by case: H4=>_; apply=>// x; move/H1; move/H3.
Qed.

Lemma chain_clos_idemp (s : Pred T) :
        chain_closed s -> chain_closure s =p s.
Proof.
move=>p; split; last by apply: chain_clos_sub.
by apply: chain_clos_min=>// /chain_closP.
Qed.

Lemma chain_clos_mono (s1 s2 : Pred T) :
        s1 <=p s2 -> chain_closure s1 <=p chain_closure s2.
Proof.
move=>H1; apply: chain_clos_min (chain_closP s2)=>p H2.
by apply: chain_clos_sub; apply: H1.
Qed.

(* intersection of admissible sets is admissible *)
Lemma chain_closI (s1 s2 : Pred T) :
       chain_closed s1 -> chain_closed s2 -> chain_closed (PredI s1 s2).
Proof.
move=>[H1 S1][H2 S2]; split=>// d H.
by split; [apply: S1 | apply: S2]=>// x; case/H.
Qed.

End AdmissibleClosure.

Arguments chain_closed {T}.
Prenex Implicits chain_closed.

(* diagonal of an admissible set of pairs is admissible *)
Lemma chain_clos_diag (T : cpo) (s : Pred (T * T)) :
        chain_closed s -> chain_closed [Pred t : T | (t, t) \In s].
Proof.
case=>B H1; split=>// d H2; move: (H1 (Image diag d)).
rewrite /limx/=/lim_op /= /cpo_prod_lim /=.
rewrite !(limE (comp_chainE _ _ _)) !(limE (id_chainE _ _)) //=.
by apply; case=>x1 x2 [z ->]; apply: H2.
Qed.

Section SubCPO.
Variables (D : cpo) (s : Pred D) (C : chain_closed s).
Local Notation tp := {x : D | x \In s}.

Definition subcpo_bot := exist _ (@bot D) (proj1 C).
Lemma subcpo_limX (u : chain tp) : lim (Image sval u) \In s.
Proof. by case: C u=>P H u; apply: (H)=>t [[y H1 ->]]. Qed.
Definition subcpo_lim (u : chain tp) : tp :=
  exist _ (lim (Image sval u)) (subcpo_limX u).

Lemma subcpo_is_cpo : cpo_axiom subcpo_bot subcpo_lim.
Proof.
split=>[x|u x H|u x H] //=.
- by apply: botP.
- by apply: limP; exists x. 
by apply: limM=>y [z ->]; apply: H. 
Qed.
HB.instance Definition _ := isCPO.Build tp subcpo_is_cpo.
End SubCPO.

(***********************************************)
(* Continuity and Kleene's fixed point theorem *)
(***********************************************)

Lemma lim_mono (D : cpo) (s1 s2 : chain D) :
        s1 <=p s2 -> lim s1 <== lim s2.
Proof. by move=>H; apply: limM=>y /H/limP. Qed.

Lemma lim_liftE (D : cpo) (s : chain D) : lim s = lim (lift s).
Proof.
apply: poset_asym; apply: limM=>y H; first by apply: limP; right.
by case: H; [move=>-> | apply: limP].
Qed.

(* applied lim equals the lim of applications *)
(* ie., part of continuity of application *)
(* but is so often used, I give it a name *)
Lemma lim_appE A (D : cpo) (s : chain (A -> D)) (x : A) :
        lim s x = lim (Image (app x) s).
Proof. by []. Qed.

Lemma lim_dappE A (D : A -> cpo) (s : chain (dfun_cpo D)) (x : A) :
        lim s x = lim (Image (dapp x) s).
Proof. by []. Qed.

(************************)
(* continuous functions *)
(************************)

Definition contfun_axiom (D1 D2 : cpo) (f : mono_fun D1 D2) := 
  forall s : chain D1, f (lim s) <== lim (Image f s).  

HB.mixin Record isContFun (D1 D2 : cpo) (f : D1 -> D2) 
  of @MonoFun D1 D2 f := {contfun_subproof : contfun_axiom f}.

#[short(type="cont_fun")]
HB.structure Definition ContFun (D1 D2 : cpo) := 
  {f of @MonoFun D1 D2 f & isContFun D1 D2 f}.

Lemma contE (D1 D2 : cpo) (f : cont_fun D1 D2) (s : chain D1) : 
        f (lim s) = lim (Image f s).
Proof. 
apply: poset_asym; first by apply: contfun_subproof.
by apply: limM=>y [x1 ->] /limP/monofunP.
Qed.

(* just for this proof, we want that nat is a poset under <= *)
(* in other scopes, we'll use the equality as ordering *)
(* Thus, we encapsulate under module. *)

Module Kleene.

Lemma nat_is_poset : poset_axiom leq.
Proof. 
split=>[|x y H1 H2|x y z] //; last by apply: leq_trans.
by apply: anti_leq; rewrite H1 H2.
Qed.
HB.instance Definition _ := isPoset.Build nat nat_is_poset.

(* nats form a chain *)
Definition nats : Pred nat := PredT.
Lemma nats_chain_axiom : chain_axiom nats.
Proof.
split=>[|x y _ _]; first by exists 0.
rewrite /poset_leq /= [y <= x]leq_eqVlt.
by case: leqP; [left | rewrite orbT; right].
Qed.
HB.instance Definition _ := isChain.Build nat nats nats_chain_axiom.

Section Kleene.
Variables (D : cpo) (f : cont_fun D D).

Fixpoint pow m := if m is n.+1 then f (pow n) else bot.

Lemma pow_is_mono : monofun_axiom pow.
Proof.
move=>m n; elim: n m=>[|n IH] m /=; first by case: m.
rewrite {1}/poset_leq /= leq_eqVlt ltnS.
case/orP; first by move/eqP=>->.
move/IH=>{IH} H; apply: poset_trans H _.
by elim: n=>[|n IH] //=; apply: monofunP IH.
Qed.
HB.instance Definition _ := isMonoFun.Build nat D pow pow_is_mono.

Lemma reindex : Image pow nats =p lift (Image f (Image pow nats)).
Proof.
move=>x; split.
- case; case=>[|n] -> _; first by left.
  by right; exists (pow n)=>//; exists n.
case=>/=; first by move=>->; exists 0.
by case=>y -> [n ->]; exists n.+1.
Qed.

Definition kleene_lfp := lim (Image pow nats).

Lemma kleene_lfp_fixed : f kleene_lfp = kleene_lfp.
Proof. by rewrite /kleene_lfp contE /= (limE reindex) /= lim_liftE. Qed.

Lemma kleene_lfp_least x : f x = x -> kleene_lfp <== x.
Proof.
move=>H; apply: limM=>y [n ->] _.
by elim: n=>[|n IH] //=; rewrite -H; apply: monofunP IH.
Qed.

End Kleene.

Lemma kleene_lfp_mono (D : cpo) (f1 f2 : cont_fun D D) :
        (f1 : D -> D) <== f2 -> 
        kleene_lfp f1 <== kleene_lfp f2.
Proof.
move=>H; apply: limM=>x [n ->] X.
have N : forall n, pow f1 n <== pow f2 n.
- by elim=>//= m /(monofunP f2); apply: poset_trans (H _).
by apply: poset_trans (N n) _; apply: limP; exists n.
Qed.

Module Exports.
Notation kleene_lfp := kleene_lfp.
Notation kleene_lfp_fixed := kleene_lfp_fixed.
Notation kleene_lfp_least := kleene_lfp_least.
Notation kleene_lfp_mono := kleene_lfp_mono.
End Exports.

End Kleene.

Export Kleene.Exports.


(**********************************)
(* Continuity of common functions *)
(**********************************)

Lemma idfun_is_cont (D : cpo) : contfun_axiom (@idfun D). 
Proof. by move=>d; rewrite (limE (id_chainE _ _)). Qed.
HB.instance Definition _ (D : cpo) := 
  isContFun.Build D D idfun (@idfun_is_cont D).

Lemma const_is_cont (D1 D2 : cpo) (y : D2) :
        contfun_axiom (@const_fun D1 D2 y).
Proof.
by move=>s; apply: limP; case: s=>[p][[[[d H1] H2]]]; exists d.
Qed.
HB.instance Definition _ (D1 D2 : cpo) (y : D2) := 
  isContFun.Build D1 D2 (const_fun y) (const_is_cont y).

Section ContCompose.
Variables D1 D2 D3 : cpo.
Variable (f1 : cont_fun D2 D1) (f2 : cont_fun D3 D2).
Lemma comp_is_cont : contfun_axiom (f1 \o f2).
Proof. by move=>s; rewrite /= !contE (limE (comp_chainE _ _ _)). Qed.
HB.instance Definition _ := isContFun.Build D3 D1 (f1 \o f2) comp_is_cont.
End ContCompose.

Lemma fst_is_cont (D1 D2 : cpo) : contfun_axiom (@fst D1 D2). 
Proof. by []. Qed.
HB.instance Definition _ (D1 D2 : cpo) := 
  isContFun.Build (D1*D2)%type D1 fst (@fst_is_cont D1 D2).

Lemma snd_is_cont (D1 D2 : cpo) : contfun_axiom (@snd D1 D2).
Proof. by []. Qed.
HB.instance Definition _ (D1 D2 : cpo) :=  
  isContFun.Build (D1*D2)%type D2 snd (@snd_is_cont D1 D2).

Lemma diag_is_cont (D : cpo) : contfun_axiom (@diag D).
Proof.
move=>d; split=>/=;
by rewrite (limE (comp_chainE _ _ _)) (limE (id_chainE _ _)).
Qed.
HB.instance Definition _ (D : cpo) := 
  isContFun.Build D (D*D)%type diag (@diag_is_cont D).

Lemma app_is_cont A (D : cpo) x : contfun_axiom (@app A D x).
Proof. by []. Qed.
HB.instance Definition _ A (D : cpo) x := 
  isContFun.Build (A -> D) D (@app A D x) (app_is_cont x).

(* can't reuse dapp and it's proof of monotonicity *)
(* because inheritance doesn't propagate properly *)
(* for dependent functions; so we duplicate *)
(* See mathcomp/finfun.v for solution (dfun vs. dffun). *)
Definition dapp2 A (B : A -> cpo) (x : A) := 
  fun f : dfun_cpo B => f x.
Lemma dapp2_is_mono A (B : A -> cpo) x : monofun_axiom (@dapp2 A B x).
Proof. by move=>f1 f2; apply. Qed.
HB.instance Definition _ A (B : A -> cpo) x := 
  isMonoFun.Build (dfun_poset B) (B x) (@dapp2 A B x) (dapp2_is_mono x).
Lemma dapp2_is_cont A (B : A -> cpo) (x : A) : contfun_axiom (@dapp2 A B x).
Proof. 
move=>s; have <- // : dapp2 x (lim s) = lim [Image dapp2 x i | i <- s].
by apply: limE=>/=. 
Qed.
HB.instance Definition _ A (B : A -> cpo) x := 
  isContFun.Build (dfun_cpo B) (B x) (@dapp2 A B x) (dapp2_is_cont x).

Section ProdCont.
Variables S1 S2 T1 T2 : cpo.
Variables (f1 : cont_fun S1 T1) (f2 : cont_fun S2 T2).

Lemma prod_is_cont : contfun_axiom (f1 \* f2).
Proof.
move=>d; split=>//=;
by rewrite contE !(limE (comp_chainE _ _ _)); apply: lim_mono.
Qed.
HB.instance Definition _ := 
  isContFun.Build (S1*S2)%type (T1*T2)%type (f1 \* f2) prod_is_cont.
End ProdCont.


