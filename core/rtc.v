(*
Copyright 2020 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq choice fintype path fingraph.
From pcm Require Import options axioms pred prelude finmap seqext.

(* Reflexive and Transitive closures of a relation with finite domain *)
(* The domain is currently taken to a finite set of nats *)

Section TransitiveClosure.
Variables (h : seq nat) (R : rel nat).
Hypothesis Rclosed : forall x y, R x y -> (x \in h) = (y \in h).

Local Definition tp := Finite.clone (seq_sub h) _.

Definition Rtp (x y : tp) : bool := R (eqtype.val x) (eqtype.val y).

(* reflexive transitive closure *)
Definition rtc (x y : nat) : bool :=
  if decP (@idP (x \in h)) is left pfx then
    if decP (@idP (y \in h)) is left pfy then
      connect Rtp (Sub x pfx) (Sub y pfy)
    else false
  else false.

(* irreflexive transitive closure *)
(* i.e., we make at least one step by R *)
Definition tc (x y : nat) :=
  (x \in h) && has (fun z => R x z && rtc z y) h.

(* lemmas about rtc *)

Lemma path_closed x p : path R x p -> (x \in h) = (last x p \in h).
Proof. by elim: p x=>[|z p IH] x //= /andP [Rxz /IH <-]; apply: Rclosed. Qed.

Lemma iter'_path n x y :
        iter' R n x y <-> exists p, [/\ size p = n, path R x p & y = last x p].
Proof.
split.
- elim: n x=>[|n IH] x /=; first by move=>->; exists [::].
  by case=>z [Rxz] /IH [p][Sp Pzp Ly]; exists (z::p)=>//=; rewrite Sp Rxz.
elim: n x=>[|n IH] x /=; first by case=>p [/size0nil ->].
case=>p []; case: p=>//= z p [Sp] /andP [Rxz Pzp] Ly.
by exists z; split=>//; apply: IH; exists p.
Qed.

Lemma iter_path x y : iter R x y <-> exists2 p, path R x p & y = last x p.
Proof.
split; first by case=>n /iter'_path [p][Sp Pxp Ly]; exists p.
by case=>p Pxp Ly; exists (size p); apply/iter'_path; exists p.
Qed.

Lemma rtc_pathP x y :
        reflect (x \in h /\ exists2 p, path R x p & y = last x p)
                (rtc x y).
Proof.
case V : (rtc x y); constructor.
- move: V; rewrite /rtc; case: decP=>// pfx; case: decP=>// pfy.
  case/connectP=>p P E; split=>//; rewrite (_ : x = ssval (Sub x pfx)) //.
  have {E} Ey : y = ssval (last (Sub x pfx) p) by rewrite -E.
  exists (map (@ssval _ _) p); last by rewrite last_map.
  by rewrite (map_path (e':=Rtp) (b:=pred0)) //; apply/hasP; case.
case=>Mx [p P Ey]; move: V; rewrite /rtc.
case: decP=>// {Mx} pfx; case: decP=>[pfy|]; last first.
- move: (mem_last x p) pfx; rewrite -Ey inE=>/orP [/eqP ->->//|].
  elim: p x P Ey=>[|p ps IH] //= x /andP [Rxp P] Ey.
  by rewrite inE (Rclosed Rxp); case: eqP=>[-> _|_ My] //; apply: IH.
case/connectP; elim: p x pfx P Ey=>[|p ps IH] /= x pfx P Ey.
- by rewrite Ey /= in pfy *; rewrite (bool_irrelevance pfx); exists [::].
case/andP: P=>Rxp P; move: {-}(pfx); rewrite (Rclosed Rxp)=>pfp.
by case: (IH p pfp P Ey)=>q; exists (Sub p pfp :: q)=>//; apply/andP.
Qed.

Lemma rtcP x y : reflect (x \in h /\ iter R x y) (rtc x y).
Proof. by case: rtc_pathP=>[[pfx]|] H; constructor; rewrite iter_path. Qed.

Lemma rtc_closed x y : rtc x y -> (x \in h) && (y \in h).
Proof. by case/rtc_pathP=>Px [p] /path_closed Mx ->; rewrite -Mx Px. Qed.

Lemma rtc_cond x y : rtc x y -> (x \in h) = (y \in h).
Proof. by case/rtc_closed/andP=>->->. Qed.

(* sometimes we start from the end of the path *)

Lemma rtc_pathP_last x y :
        reflect (y \in h /\ exists2 p, path R x p & y = last x p)
                (rtc x y).
Proof.
case: rtc_pathP=>[[pfx]|] H; constructor.
- by split=>//; case: H pfx=>p /path_closed ->->.
by case=>pfy X; apply: H; split=>//; case: X pfy=>p /path_closed ->->.
Qed.

Lemma rtcP_last x y : reflect (y \in h /\ iter R x y) (rtc x y).
Proof. by case: rtc_pathP_last=>[[pfx]|] H; constructor; rewrite iter_path. Qed.

(* lemmas about tc *)

Lemma tc_pathP x y :
        reflect (x \in h /\ exists z p, [/\ R x z, path R z p & y = last z p])
        (tc x y).
Proof.
rewrite /tc; case: andP=>[[Mx /hasP]|] H; constructor.
- by case: H=>z ? /andP [?] /rtc_pathP [_][p]; split=>//; exists z, p.
case=>Mx [z][p][Rxz P E]; have Mz : z \in h by rewrite -(Rclosed Rxz).
apply: H; case: hasP=>//; case; exists z=>//; rewrite Rxz.
by apply/rtc_pathP; split=>//; exists p.
Qed.

Lemma tcP x y : reflect (x \in h /\ exists n, iter' R n.+1 x y) (tc x y).
Proof.
case: tc_pathP=>H; constructor.
- case: H=>Mx [z][p][Rxz P E]; split=>//; exists (size p).
  by exists z; split=>//; apply/iter'_path; exists p.
case=>Mx [n /= [z][Rxz] /iter'_path [p][Sp Pzp Ly]].
by apply: H; split=>//; exists z, p.
Qed.

Lemma tc_closed x y : tc x y -> (x \in h) && (y \in h).
Proof.
case/tc_pathP=>Mx [z][p][Rxz /path_closed Px ->].
by rewrite -Px -(Rclosed Rxz) Mx.
Qed.

Lemma tc_cond x y : tc x y -> (x \in h) = (y \in h).
Proof. by case/tc_closed/andP=>->->. Qed.

Lemma tc_pathP_last x y :
        reflect (y \in h /\ exists z p, [/\ R z y, path R x p & z = last x p])
                (tc x y).
Proof.
case: tc_pathP=>H; constructor.
- case: H=>Mx [z][p][Rxz Pzp Ly]; split.
  - by rewrite {1}Ly -(path_closed Pzp) -(Rclosed Rxz).
  case: (lastP p) Pzp Ly=>[|q w]; first by move=>_ ->; exists x, [::].
  rewrite rcons_path last_rcons=>/andP [Pzw Rwq ->{y}].
  by exists (last z q), (z::q); rewrite /= Rxz.
case=>My [z][p][Rzy Pxp Lz]; apply: H; split.
- by rewrite (path_closed Pxp) -Lz (Rclosed Rzy).
case: p Pxp Lz=>[|w q] /=; first by move=>_ <-; exists y, [::].
case/andP=>Rxw Pwq E; exists w, (rcons q y).
by rewrite rcons_path last_rcons -E Pwq.
Qed.

Lemma tcP_last x y : reflect (y \in h /\ exists n, iter' R n.+1 x y) (tc x y).
Proof.
case: tc_pathP_last=>H; constructor.
 case: H=>My [z][p][Rzy Pxp Lz]; split=>//; exists (size p); apply/iterS.
 by exists z; split=>//; apply/iter'_path; exists p.
case=>My [n] /iterS [z][/iter'_path [p][Sp Pxp Lz] Rzy].
by apply: H; split=>//; exists z, p.
Qed.

Lemma rtc1 x y : x \in h -> y \in h -> R x y -> rtc x y.
Proof.
rewrite /rtc=>Dx Dy Rxy; case: decP=>// Dx'; case: decP=>// Dy'.
by apply/connectP; exists [:: Sub y Dy']=>//=; rewrite andbT.
Qed.

Lemma rtc_refl x : x \in h -> rtc x x.
Proof. by rewrite /rtc; case: decP. Qed.

Lemma tc1 x y : x \in h -> y \in h -> R x y -> tc x y.
Proof.
by rewrite /tc=>-> Dy Rxy; apply/hasP; exists y=>//; rewrite Rxy rtc_refl.
Qed.

Lemma rtc_trans : transitive rtc.
Proof.
rewrite /rtc=>x y z; case: decP=>// Dy; case: decP=>// Dx.
by case: decP=>// Dz; apply: connect_trans.
Qed.

Lemma tc_trans : transitive tc.
Proof.
rewrite /tc=>x y z /andP [Dy /hasP [y' Dy' /andP [Ry Ry'x]]].
case/andP=>Dx /hasP [x' Dx' /andP [Rx Rx'z]].
rewrite Dy; apply/hasP; exists y'=>//; rewrite Ry.
by apply: rtc_trans (rtc_trans Ry'x (rtc1 _ _ _)) Rx'z.
Qed.

Lemma rtc_tc x y : tc x y -> rtc x y.
Proof.
case/andP=>Dx /hasP [z Dz] /andP [Rxz].
by apply: rtc_trans (rtc1 Dx Dz Rxz).
Qed.

End TransitiveClosure.


(* some helper lemmas *)

Lemma connect_idemp (T : finType) (R : rel T) :
        reflexive R -> transitive R -> connect R =2 R.
Proof.
move=>Rr Tr x y; apply/connectP; case: ifP=>[Rxy|H [p P Ly]].
- by exists [:: y]=>//=; rewrite Rxy.
by move: (path_lastR Rr Tr P); rewrite -Ly H.
Qed.

Lemma rtcT (h : seq nat) (R : rel nat) x y :
       (forall x y, R x y -> (x \in h) && (y \in h)) ->
       transitive R -> rtc h R x y -> R x y || (x == y) && (x \in h).
Proof.
move=>Rcond Tr /rtcP [|Dx [n]]; first by move=>?? /Rcond/andP [->->].
elim: n x Dx=>[|n IH] x Dx /=; first by move=><-; rewrite eq_refl Dx orbT.
case=>z [Rxz]; case/Rcond/andP: (Rxz)=>-> Dz /(IH _ Dz).
by case: eqP Rxz=>[<- ->//|_ Rxz]; rewrite orbF=>/(Tr _ _ _ Rxz)=>->.
Qed.

Lemma rtc_idemp (h : seq nat) (R : rel nat) :
        (forall x y, R x y -> (x \in h) && (y \in h)) ->
        rtc h (rtc h R) =2 rtc h R.
Proof.
move=>Rcond x y.
have X : forall x y, R x y -> (x \in h) = (y \in h).
- by move=>?? /Rcond/andP [->->].
apply/idP/idP; last first.
- by move=>H; case/andP: (rtc_closed X H)=>Dx Dy; apply: rtc1.
case/(rtcT (rtc_closed X) (@rtc_trans h R))/orP=>//.
by case/andP=>/eqP <-; apply: rtc_refl.
Qed.

Lemma rtc_sub (h : seq nat) (R1 R2 : rel nat) x y :
        (forall x y, R2 x y -> (x \in h) && (y \in h)) ->
        (forall x y, R1 x y -> R2 x y) ->
        rtc h R1 x y -> rtc h R2 x y.
Proof.
move=>Rcond Rsub.
have X : forall x y, R2 x y -> (x \in h) = (y \in h).
- by move=>?? /Rcond /andP [->->].
case/rtcP=>[?? /Rsub/X //|Dx H]; apply/rtcP=>//.
by split=>//; apply: iter_sub H; apply: Rsub.
Qed.

Lemma tcT (h : seq nat) (R : rel nat) :
        (forall x y, R x y -> (x \in h) && (y \in h)) ->
        transitive R -> tc h R =2 R.
Proof.
move=>Rcond Tr x y; apply/idP/idP; last first.
- by move=>H; case/andP: (Rcond _ _ H)=>Dx Dy; apply: tc1.
case/andP=>Dx /hasP [z Dz] /andP [Rxz] /(rtcT Rcond Tr).
by case: eqP=>[<-|_] //; rewrite orbF; apply: Tr Rxz.
Qed.

Lemma tc_idemp (h : seq nat) (R : rel nat) :
        (forall x y, R x y -> (x \in h) && (y \in h)) ->
        tc h (tc h R) =2 tc h R.
Proof.
move=>Rcond x y; rewrite (tcT _ (@tc_trans _ _)) //.
by apply: tc_closed=>?? /Rcond/andP [->->].
Qed.

Lemma tc_sub (h : seq nat) (R1 R2 : rel nat) x y :
        (forall x y, R2 x y -> (x \in h) && (y \in h)) ->
        (forall x y, R1 x y -> R2 x y) ->
        tc h R1 x y -> tc h R2 x y.
Proof.
move=>Rcond Rsub /andP [Dx] /hasP [z Dz] /andP [Rxz R].
rewrite /tc Dx; apply/hasP; exists z=>//.
by rewrite (Rsub _ _ Rxz) (rtc_sub _ _ R).
Qed.
