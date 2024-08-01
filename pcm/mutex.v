(*
Copyright 2013 IMDEA Software Institute
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

(******************************************************************************)
(* This file defines the generalized mutex type.                              *)
(* We need a notion of mutex where the options are not just nown/own but      *)
(* an arbitrary number of elements in-between. This reflects the possible     *)
(* stages of acquiring a lock. Once a thread embarks on the first stage, it   *)
(* excludes others, but it may require more steps to fully acquire the lock.  *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From Coq Require Setoid.
From mathcomp Require Import ssrnat eqtype seq.
From pcm Require Import options prelude pred.
From pcm Require Import pcm morphism natmap.

(***********************)
(* Generalized mutexes *)
(***********************)

(* T encodes mutex stages, excluding undef and unit *)

Inductive mutex T := mx_undef | nown | mx of T.

Arguments mx_undef {T}.
Arguments nown {T}.
Prenex Implicits mx_undef nown.

Section GeneralizedMutex.
Variable T : Type.
Definition def_mx_valid := [fun x : mutex T =>
  if x is mx_undef then false else true].
Definition def_mx_join := [fun x y : mutex T =>
  match x, y with
    mx_undef, _ => mx_undef
  | _, mx_undef => mx_undef
  | nown, x => x
  | x, nown => x
  | mx _, mx _ => mx_undef
  end].
Definition def_mx_unitb := [fun x : mutex T =>
  if x is nown then true else false].

Lemma mutex_is_pcm : pcm_axiom def_mx_valid def_mx_join nown def_mx_unitb.
Proof. 
by split=>[[||x][||y]|[||x][||y][||z]|[]|[]||[||x]] //; constructor.
Qed.
HB.instance Definition _ : isPCM (mutex T) := 
  isPCM.Build (mutex T) mutex_is_pcm.

(* cancellativity *)
Lemma mutex_is_cpcm : cpcm_axiom (mutex T).
Proof. by case=>[||m][||m1][||m2]; rewrite !pcmE. Qed.
HB.instance Definition _ : isCPCM (mutex T) := 
  isCPCM.Build (mutex T) mutex_is_cpcm.

(* topped structure *)
Definition def_mx_undefb (x : mutex T) : bool := 
  if x is mx_undef then true else false.

Lemma mutex_is_tpcm : tpcm_axiom mx_undef def_mx_undefb. 
Proof. by split=>//; case=>[||x]; constructor. Qed.
HB.instance Definition _ : isTPCM (mutex T) :=
  isTPCM.Build (mutex T) mutex_is_tpcm.

(* normality *)
Lemma mutex_is_normal : normal_tpcm_axiom (mutex T).
Proof. by case; [right|rewrite valid_unit; left|move=>t; left]. Qed.
HB.instance Definition _ : isNormal_TPCM (mutex T) :=
  isNormal_TPCM.Build (mutex T) mutex_is_normal.
End GeneralizedMutex.

(* if T is eqType, so is mutex T *)
Section Equality.
Variable T : eqType.

Definition mutex_eq (x y : mutex T) :=
  match x, y with
    mx_undef, mx_undef => true
  | nown, nown => true
  | mx x', mx y' => x' == y'
  | _, _ => false
  end.

Lemma mutex_eqP : Equality.axiom mutex_eq.
Proof.
case=>[||x]; case=>[||y] /=; try by constructor.
by case: eqP=>[->|H]; constructor=>//; case=>/H.
Qed.

HB.instance Definition _ := hasDecEq.Build (mutex T) mutex_eqP.
End Equality.

(* mutexes with distingusihed own element *)
Notation mtx T := (mutex (option T)).
Notation mtx2 := (mtx False).
Notation mtx3 := (mtx unit).
Notation own := (mx None).
Notation auth x := (mx (Some x)).
Notation auth1 := (mx (Some tt)).

(* some lemmas for generalized mutexes *)

Section MutexLemmas.
Variable T : Type.
Implicit Types (t : T) (x y : mutex T).

Variant mutex_spec x : mutex T -> Type :=
| mutex_undef of x = undef : mutex_spec x undef
| mutex_nown of x = Unit : mutex_spec x Unit
| mutex_mx t of x = mx t : mutex_spec x (mx t).

Lemma mxP x : mutex_spec x x.
Proof. by case: x=>[||t]; constructor. Qed.

Lemma mxE0 x y : x \+ y = Unit -> (x = Unit) * (y = Unit).
Proof. by case: x; case: y. Qed.

(* a form of cancelativity, more useful than the usual form *)
Lemma cancelMx t1 t2 x : (mx t1 \+ x = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by case: x=>[||x] //=; split=>//; case=>->. Qed.

Lemma cancelxM t1 t2 x : (x \+ mx t1 = mx t2) <-> (t1 = t2) * (x = Unit).
Proof. by rewrite joinC cancelMx. Qed.

(* DEVCOMMENT *)
(* the next batch of lemmas about validity should be automated *)
(* /DEVCOMMENT *)
Lemma mxMx t x : valid (mx t \+ x) -> x = Unit.
Proof. by case: x. Qed.

Lemma mxxM t x : valid (x \+ mx t) -> x = Unit.
Proof. by rewrite joinC=>/mxMx. Qed.

Lemma mxxyM t x y : valid (x \+ (y \+ mx t)) -> x \+ y = Unit.
Proof. by rewrite joinA=>/mxxM. Qed.

Lemma mxMxy t x y : valid (mx t \+ x \+ y) -> x \+ y = Unit.
Proof. by rewrite -joinA=>/mxMx. Qed.

Lemma mxxMy t x y : valid (x \+ (mx t \+ y)) -> x \+ y = Unit.
Proof. by rewrite joinCA=>/mxMx. Qed.

Lemma mxyMx t x y : valid (y \+ mx t \+ x) -> y \+ x = Unit.
Proof. by rewrite joinAC=>/mxMx. Qed.

(* inversion principle for join *)
(* own and mx are prime elements, and unit does not factor *)
Variant mxjoin_spec (x y : mutex T) : mutex T -> mutex T -> mutex T -> Type :=
| bothnown of x = Unit & y = Unit : mxjoin_spec x y Unit Unit Unit
| leftmx t of x = mx t & y = Unit : mxjoin_spec x y (mx t) (mx t) Unit
| rightmx t of x = Unit & y = mx t : mxjoin_spec x y (mx t) Unit (mx t)
| invalid of ~~ valid (x \+ y) : mxjoin_spec x y undef x y.

Lemma mxPJ x y : mxjoin_spec x y (x \+ y) x y.
Proof. by case: x y=>[||x][||y]; constructor. Qed.

End MutexLemmas.

Prenex Implicits mxMx mxxM mxxyM mxMxy mxxMy mxyMx.

(* DEVCOMMENT *)
(* and the same for own; do we need to repeat? *)
(* /DEVCOMMENT *)
Section OwnMutex.
Variables T : Type.
Implicit Types x y : mtx T.

Lemma mxOx x : valid (own \+ x) -> x = Unit.
Proof. by apply: mxMx. Qed.

Lemma mxxO x : valid (x \+ own) -> x = Unit.
Proof. by apply: mxxM. Qed.

Lemma mxxyO x y : valid (x \+ (y \+ own)) -> x \+ y = Unit.
Proof. by apply: mxxyM. Qed.

Lemma mxOxy x y : valid (own \+ x \+ y) -> x \+ y = Unit.
Proof. by apply: mxMxy. Qed.

Lemma mxxOy x y : valid (x \+ (own \+ y)) -> x \+ y = Unit.
Proof. by apply: mxxMy. Qed.

Lemma mxyOx x y : valid (y \+ own \+ x) -> y \+ x = Unit.
Proof. by apply: mxyMx. Qed.
End OwnMutex.

Prenex Implicits  mxOx mxxO mxxyO mxOxy mxxOy mxyOx.

(* specific lemmas for binary mutexes *)

(* DEVCOMMENT *)
(* these also are a bit of a featuritis *)
(* /DEVCOMMENT *)
Lemma mxON (x : mtx2) : valid x -> x != own -> x = Unit.
Proof. by case: x=>//; case. Qed.

Lemma mxNN (x : mtx2) : valid x -> x != Unit -> x = own.
Proof. by case: x=>//; case=>//; case. Qed.

(* the next batch of lemmas is for automatic simplification *)

Section MutexRewriting.
Variable T : eqType.
Implicit Types (t : T) (x : mutex T).

Lemma mxE1 :  (((undef == Unit :> mutex T) = false) *
               ((Unit == undef :> mutex T) = false)).
Proof. by []. Qed.

Lemma mxE2 t : (((mx t == Unit) = false) *
                ((Unit == mx t) = false)) *
               (((mx t == undef) = false) *
                ((undef == mx t) = false)).
Proof. by []. Qed.

Lemma mxE3 t x : ((((mx t \+ x == Unit) = false) *
                   ((x \+ mx t == Unit) = false)) *
                  (((Unit == mx t \+ x) = false) *
                   ((Unit == x \+ mx t) = false))).
Proof. by case: x. Qed.

Lemma mxE5 t1 t2 x :
       (((mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit)) *
        ((x \+ mx t1 == mx t2) = (t1 == t2) && (x == Unit))) *
       (((mx t1 == mx t2 \+ x) = (t1 == t2) && (x == Unit)) *
        ((mx t1 == x \+ mx t2) = (t1 == t2) && (x == Unit))).
Proof.
have L : forall t1 t2 x, (mx t1 \+ x == mx t2) = (t1 == t2) && (x == Unit).
- by move=>*; apply/eqP/andP=>[/cancelMx[]->->|[]/eqP->/eqP->].
by do !split=>//; rewrite ?L // eq_sym L eq_sym.
Qed.


Lemma mx_valid t : valid (mx t).
Proof. by []. Qed.

Lemma mx_injE t1 t2 : (mx t1 == mx t2) = (t1 == t2).
Proof. by []. Qed.

Definition mxE := ((((mxE1, mxE2), (mxE3)), ((mxE5, mx_injE),
                   (mx_valid))),
                   (* plus a bunch of safe simplifications *)
                   (((@unitL, @unitR), (@valid_unit, eq_refl)),
                   ((valid_undef, undef_join), join_undef))).

End MutexRewriting.

(* function mapping all mx's to own *)
Definition mxown {T} (x : mutex T) : mtx2 :=
  match x with
    mx_undef => undef
  | nown => Unit
  | _ => own
  end.

(* this is a morphism under full domain *)
Lemma mxown_is_pcm_morph {T} : pcm_morph_axiom relT (@mxown T).
Proof. by split=>[|x y] //; case: x; case: y. Qed.
HB.instance Definition _ T := 
  isPCM_morphism.Build (mutex T) mtx2 mxown mxown_is_pcm_morph.
HB.instance Definition _ T := 
  isFull_PCM_morphism.Build (mutex T) mtx2 (@mxown T) (fun _ _ => erefl _).
HB.instance Definition _ T := 
  isTPCM_morphism.Build (mutex T) mtx2 mxown (erefl undef).
Lemma mxown_is_binormal {T} : binorm_pcm_morph_axiom (@mxown T).
Proof. by case=>[||x][||y]. Qed.
HB.instance Definition _ T := 
  isBinorm_PCM_morphism.Build (mutex T) mtx2 mxown mxown_is_binormal.

(* the key inversion property is the following *)
(* we could use simple case analysis in practice *)
(* but this appears often, so we might just as well have a lemma for it *)
Lemma mxownP T (x : mutex T) : mxown x = Unit -> x = Unit.
Proof. by case: x. Qed.

Definition mxundef {T} (x : mtx T) : mtx2 :=
  match x with
  | nown => Unit
  | mx None => own
  | _ => undef
  end.

Definition sep_mxundef {T} (x y : mtx T) :=
  if x \+ y is (nown | mx None) then true else false.

Lemma sep_mxundef_is_seprel {T} : seprel_axiom (@sep_mxundef T).
Proof. by split=>//; case=>[||x] // [||y] // [||[]] //=; case: y. Qed.
HB.instance Definition _ T := 
  isSeprel.Build (mtx T) sep_mxundef sep_mxundef_is_seprel.

Lemma mxundef_is_pcm_morph {T} : pcm_morph_axiom (@sep_mxundef T) mxundef.
Proof. by split=>//; case=>[||x] // [||[]] //; case: x. Qed.
HB.instance Definition _ T := 
  isPCM_morphism.Build (mtx T) mtx2 mxundef mxundef_is_pcm_morph.
HB.instance Definition _ T := 
  isTPCM_morphism.Build (mtx T) mtx2 mxundef (erefl undef).
Lemma mxundef_is_binormal {T} : binorm_pcm_morph_axiom (@mxundef T).
Proof. by case=>[||[x|]][||[y|]]. Qed.
HB.instance Definition _ T := 
  isBinorm_PCM_morphism.Build (mtx T) mtx2 mxundef mxundef_is_binormal.

Prenex Implicits mxown mxundef.

(* inversion principle for mxundef *)
Variant mxundef_spec T (x : mtx T) : mtx2 -> mtx T -> Type :=
| mxundef_nown of x = nown : mxundef_spec x Unit Unit
| mxundef_own of x = own : mxundef_spec x own own
| mxundef_undef of x = undef : mxundef_spec x undef undef
| mxundef_mx t of x = auth t : mxundef_spec x undef (auth t).

Lemma mxundefP T (x : mtx T) : mxundef_spec x (mxundef x) x.
Proof. by case: x=>[||[t|]]; constructor. Qed.

(* nats into mtx *)
(* notice this is not a morphism *)
Definition nxown n : mtx2 := if n is 0 then Unit else own.

Variant nxown_spec n : mtx2 -> Type :=
| nxZ of n = 0 : nxown_spec n Unit
| nxS m of n = m.+1 : nxown_spec n own.

Lemma nxP n : nxown_spec n (nxown n).
Proof. by case: n=>[|n]; [apply: nxZ | apply: (@nxS _ n)]. Qed.

Variant nxownjoin_spec n1 n2 : mtx2 -> Type :=
| nxjZ of n1 = 0 & n2 = 0 : nxownjoin_spec n1 n2 Unit
| nxjS m of n1 + n2 = m.+1 : nxownjoin_spec n1 n2 own.

Lemma nxPJ n1 n2 : nxownjoin_spec n1 n2 (nxown (n1 \+ n2)).
Proof.
case: n1 n2=>[|n1][|n2] /=.
- by constructor.
- by apply: (@nxjS _ _ n2).
- by apply: (@nxjS _ _ n1); rewrite addn0 //.
apply: (@nxjS _ _ (n1 + n2).+1).
by rewrite addSn addnS.
Qed.

(**********************************)
(* Morphisms on locking histories *)
(**********************************)

(* Morphism on locking histories that provides mutual exclusion: *)
(* when one thread has locked, the other can't proceed. *)
(* Because the morphism just looks into the last history entry *)
(* we call it *omega*, or omg for short. *)

Section OmegaMorph.
Variable U : natmap (bool * bool).

Definition omg_sep := fun x y : U =>
  [&& last_atval false x ==> (last_key y < last_key x) &
      last_atval false y ==> (last_key x < last_key y)].

Lemma omg_is_seprel : seprel_axiom omg_sep.
Proof.
rewrite /omg_sep; split=>[|x y|x y|x y z] /=. 
- by rewrite lastatval0.
- by rewrite andbC.
- move=>V /andP [H _]; rewrite lastkey0 lastatval0 /=. 
  by case: (x in x ==> _) H=>// /(leq_trans _) ->.
move=>V /andP [X Y] /andP [].
rewrite !lastkeyUn !lastatvalUn !(validLE3 V).
rewrite {1 2}maxnC {1 2}/maxn gtn_max leq_max /=.
case: (ltngtP (last_key x) (last_key y)) X Y=>H X Y Kx Kz;
 rewrite ?H ?X ?(negbTE Y) fun_if if_arg ?implybT ?Kx Kz if_same //= ?andbT.
by case: (x in x ==> _) Kz=>// /(ltn_trans H) ->.
Qed.

HB.instance Definition _ := isSeprel.Build U omg_sep omg_is_seprel.

Definition omg (x : U) : mtx2 := 
  if undefb x then undef else
    if last_atval false x then own else nown.

(* DEVCOMMENT *)
(*   omg isn't tpcm morphism because it doesn't preserve undef *)
(*   this makes it less useful than it might be *)
(*   but we wait with fixing the definition until it becomes necessary *)
(*   (the definition should branch on x being undef *)
(* /DEVCOMMENT *)

Lemma omg_is_pcm_morph : pcm_morph_axiom omg_sep omg.
Proof.
rewrite /omg; split=>[|x y V /andP [X Y]] /=.
- by rewrite undefb0 lastatval0.
rewrite !undefNV !(validE2 V) /= lastatvalUn V; case: ltngtP X Y=>H X Y;
by rewrite ?(negbTE X) ?(negbTE Y) //; case: ifP.
Qed.
HB.instance Definition _ := isPCM_morphism.Build U mtx2 omg omg_is_pcm_morph.

Lemma omg_is_tpcm_morph : tpcm_morph_axiom omg.
Proof. by rewrite /tpcm_morph_axiom/omg undefb_undef. Qed.
HB.instance Definition _ := isTPCM_morphism.Build U mtx2 omg omg_is_tpcm_morph.

Lemma omg_is_norm : norm_pcm_morph_axiom omg.
Proof.
move=>/= x; rewrite /sepx/=/omg/omg_sep lastkey0 lastatval0.
case: (normalP x)=>// Vx; case: ifP=>H _ //=.
by case: lastkeyP (lastatval_indomb H).
Qed.
HB.instance Definition _ := isNorm_PCM_morphism.Build U mtx2 omg omg_is_norm.

(* transfer lemmas *)

(* omg isn't full, but admits valid h -> valid (omg h) *)
Lemma valid_omg h : valid (omg h) = valid h.
Proof.
apply/idP/idP=>[/fpV//|V].
rewrite pfV //= /sepx/= /omg_sep /= lastatval0 andbT lastkey0.
case N: (last_key h); last by apply/implyP. 
by rewrite /last_atval /atval /= cond_find // N.
Qed.

Lemma omgPos (V : pcm) (v : V) (ht : V -> U) :
        last_atval false (ht v) = (omg (ht v) == own).
Proof. 
rewrite /omg; case: normalP=>[->//|]; last by case: ifP.
by rewrite lastatval_undef.  
Qed.

Lemma omgPosMorph (V : pcm) (v1 v2 : V) (ht : pcm_morph V U):
        valid (v1 \+ v2) -> 
        preim ht omg_sep v1 v2 ->
        last_atval false (ht v1 \+ ht v2) = 
          (omg (ht v1) \+ omg (ht v2) == own).
Proof.
move=>W /andP [G] /andP []; rewrite /omg /= in G *.
rewrite !undefNV !(validE2 (pfV2 _ _ _ W G)) lastatvalUn pfV2 //=.
by case: ltngtP=>H H1 H2; rewrite ?(negbTE H1) ?(negbTE H2) //; case: ifP.
Qed.

Lemma omgNeg' (V : pcm) (v : V) (ht : V -> U) :
       ~~ last_atval false (ht v) = 
       (omg (ht v) == nown) || undefb (omg (ht v)).
Proof. by rewrite omgPos; case: (omg _)=>//; case. Qed.

Lemma omgNeg (V : pcm) (v : V) (ht : V -> U) :
       valid (ht v) ->
       ~~ last_atval false (ht v) = (omg (ht v) == nown).
Proof. by move=>W; rewrite omgNeg' undefNV valid_omg W; case: (omg _). Qed.

Lemma omgNegMorph (V : pcm) (v1 v2 : V) (ht : pcm_morph V U) :
         valid (v1 \+ v2) -> preim ht omg_sep v1 v2 ->
         ~~ last_atval false (ht v1 \+ ht v2) = 
         (omg (ht v1) \+ omg (ht v2) == nown).
Proof. 
move=>W /andP [H1 H2].
have W' : valid (ht (v1 \+ v2)) by rewrite pfV // (sepU0 W H1).
by rewrite -!pfjoin //= omgNeg.
Qed.

Lemma omgidPos (v : U) : last_atval false v = (omg v == own).
Proof. by rewrite (omgPos _ id). Qed.

Lemma omgidPosMorph (v1 v2 : U) :
        valid (v1 \+ v2) -> omg_sep v1 v2 ->
        last_atval false (v1 \+ v2) = (omg v1 \+ omg v2 == own).
Proof. by move=>W S; rewrite (omgPosMorph (ht:=idfun)). Qed.

Lemma omgidNeg (v : U) :
       valid v ->
        ~~ last_atval false v = (omg v == Unit).
Proof. exact: (@omgNeg _ _ id). Qed.

Lemma omgidNegMorph (v1 v2 : U) :
        valid (v1 \+ v2) -> omg_sep v1 v2 ->
         ~~ last_atval false (v1 \+ v2) = 
         (omg v1 \+ omg v2 == Unit).
Proof. by move=>W S; rewrite (omgNegMorph (ht:=idfun)). Qed.

Definition omgP := 
  (valid_omg,
   (omgidNegMorph, omgidPosMorph, omgPosMorph, omgNegMorph), 
   (omgidPos, omgidNeg, omgPos, omgNeg)).

Lemma omg_fresh_val (V : pcm) (v1 v2 : V) (ht : pcm_morph V U) :
      valid (v1 \+ v2) ->
      sep ht v1 v2 ->
      (omg (pts (fresh (ht v1 \+ ht v2)) (false, true) \+ ht v1) = own) *
      (omg (pts (fresh (ht v1 \+ ht v2)) (true, false) \+ ht v1) = nown) *
      (omg (pts (fresh (ht v1 \+ ht v2)) (false, true) \+ ht v2) = own) *
      (omg (pts (fresh (ht v1 \+ ht v2)) (true, false) \+ ht v2) = nown).
Proof.
move=>A O; have Vh : valid (ht v1 \+ ht v2) by rewrite pfV2.
rewrite /omg !undefNV !validPtUn /= !(validE2 Vh) !negbK /=.
by rewrite !lastatval_freshUn // !(negbTE (fresh_dom _)) ?(freshUnL,freshUnR).
Qed.

Lemma omg_fresh_sep (V : pcm) (v1 v2 : V) (ht : pcm_morph V U) op :
        valid (v1 \+ v2) ->
        sep ht v1 v2 ->
        (omg (ht v2) = Unit ->
          omg_sep (pts (fresh (ht v1 \+ ht v2)) op \+ ht v1) (ht v2)) *
        (omg (ht v1) = Unit ->
          omg_sep (ht v1) (pts (fresh (ht v1 \+ ht v2)) op \+ ht v2)).
Proof.
move=>A O; have Vh : valid (ht v1 \+ ht v2) by rewrite pfV2.
rewrite /omg_sep lastatval_freshUn //.
rewrite !lastkeyPtUn ?(validE2 Vh,freshUnL,freshUnR) //.
by split=>N; rewrite implybT omgP N.
Qed.

Definition omg_fresh := (omg_fresh_val, omg_fresh_sep).

(* DEVCOMMENT *)
(* some extra properties the need for which appeared later *)
(* TODO eventually organize into their proper places *)
(* /DEVCOMMENT *)
Lemma omg_eta (h : U):
        valid h -> omg h = own ->
        exists h' v, [/\ h' = free h (last_key h),
          h = pts (last_key h) (v, true) \+ h',
          last_key h != 0,
          last_key h \in dom h,
          last_key h \notin dom h' &
          last_key h' < last_key h].
Proof.
move=>V; rewrite /omg /=; rewrite undefNV V /=.
case: ifP=>// N _; set k := last_key h.
have D : k \in dom h.
- rewrite /last_atval /atval /oapp in N.
  by case: dom_find N.
have K : k != 0 by apply: dom_cond D.
case: (um_eta D); case=>v1 v2 [Ef Eh].
set h' := free h k in Eh *; set q := k \-> (v1 , true).
have Nd : k \notin dom h'.
- rewrite Eh in V; case: validUn V=>// _ _ X _; apply: X.
  by rewrite domPt inE /= K eq_refl.
exists h', v1; split=>//.
- by rewrite /last_atval /atval Ef /= in N; rewrite -N.
have: last_key h' <= k.
- by rewrite /k Eh lastkeyPtUnE -Eh V leq_maxr.
rewrite leq_eqVlt; case/orP=>// /eqP E.
by rewrite -E in Nd K; case: lastkeyP K Nd.
Qed.

(* specialize to alternating histories *)
Lemma omg_eta_all (h : U) :
        valid h -> omg h = own -> um_all (fun k v => v.2 = ~~ v.1) h ->
        exists h', [/\ h' = free h (last_key h),
          h = pts (last_key h) (false, true) \+ h',
          last_key h != 0,
          last_key h \in dom h,
          last_key h \notin dom h' &
          last_key h' < last_key h].
Proof.
move=>V H A; case: (omg_eta V H)=>h' [v][H1 H2 H3 H4 H5 H6].
exists h'; split=>//; rewrite H2 in V A; case: (umallPtUnE V A)=>/=.
by case: v {A} V H2.
Qed.

Lemma omg_lastkey x y :
        (omg x = own -> valid (x \+ y) -> omg_sep x y ->
           last_key (x \+ y) = last_key x) *
        (omg y = own -> valid (x \+ y) -> omg_sep x y ->
           last_key (x \+ y) = last_key y).
Proof.
rewrite /omg_sep /omg !undefNV. 
split=>L V S; rewrite (validE2 V) /= in L; case: ifP L=>L // _;
rewrite L /= in S; rewrite lastkeyUn V; case/andP: S=>S1 S2.
 by rewrite maxnC /maxn S1.
by rewrite /maxn S2.
Qed.

End OmegaMorph.

Arguments omg {U}.
Arguments omg_sep {U}.

