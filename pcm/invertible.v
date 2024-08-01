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
(* This file contains an implementation of invertible PCM morphisms and their *)
(* separating relations.                                                      *)
(******************************************************************************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype.
From pcm Require Import options axioms prelude.
From pcm Require Import pcm morphism.

(* in the POPL21 paper, we use the notation
   x D y D z =def= x D y /\ (x \+ y) D z
*)
Definition inv_rel (U : pcm) (D : rel U) :=
  forall a1 a2 a',
    valid (a1 \+ a2 \+ a') ->
    D a1 (a2 \+ a') -> D a2 (a1 \+ a') ->
    D a1 a2 && D (a1 \+ a2) a'.

Definition inv_morph_axiom (U V : pcm) (f : pcm_morph U V) :=
  forall (a : U) (b1 b2 : V),
    valid a -> sep f a Unit -> f a = b1 \+ b2 ->
    exists a1 a2, [/\ a = a1 \+ a2, valid (a1 \+ a2),
                      sep f a1 a2, f a1 = b1 & f a2 = b2 ].

Definition inv_morph (U V : pcm) (f : pcm_morph U V) := 
  inv_rel (sep f) /\ inv_morph_axiom f.


(* trivial seprel in invertible *)
Lemma inv_sepT (U : pcm) : inv_rel (@relT U). Proof. by []. Qed.

Lemma inv_idfun (U : pcm) : inv_morph (@idfun U). 
Proof. by split=>// a b1 b2 V _ E; exists b1, b2; rewrite -E. Qed.

(* composition of invertible morphisms is invertible *)

Lemma inv_comp (U V W : pcm) 
               (f : pcm_morph U V) (g : pcm_morph V W) :
        inv_morph f -> inv_morph g -> inv_morph (g \o f).
Proof.
case=>Sf Ff [Sg Fg]; split=>[a1 a2 a' V1|a b1 b2 V1] /andP [] /=.
- move/(Sf _ _ _ V1)=>H1 H2 /andP [/H1] /andP [D1 D2] /=.
  rewrite /sepx/= !pfjoin ?(validLE3 V1,sepAxx V1 D1 D2) //= in H2 *.
  by apply: Sg H2; apply: pfV3.
move=>D1; rewrite pfunit=>C1.
case/(Fg _ _ _ (pfV _ _ V1 D1) C1)=>c1 [c2][Ef Vc Xc <-<-].
case/(Ff _ _ _ V1 D1): Ef Xc=>a1 [a2][-> Va Xc <-<- Xd].
by exists a1, a2; rewrite /sepx/= Xc Xd. 
Qed.

(* morphism product of invertibles is invertible *)
Lemma inv_cprod (U1 U2 V1 V2 : pcm) 
                (f : pcm_morph U1 V1) (g : pcm_morph U2 V2) :
        inv_morph f -> inv_morph g -> inv_morph (f \* g).
Proof.
case=>Sf Ff [Sg Fg]; split=>[a1 a2 a'|] /=. 
- rewrite /rel_prod=>/andP [Va Vb] /andP [/(Sf _ _ _ Va) H1 /(Sg _ _ _ Vb) H2].
  by rewrite /sepx/=; case/andP=>/H1/andP [->->] /H2/andP [->->].
move=>/= a1 b1 b2 /andP [Va Vb] /andP [H1 H2][].
case/(Ff _ _ _ Va H1)=>c1 [c2][E1 Vc1 Y1 Fc1 Fc2].
case/(Fg _ _ _ Vb H2)=>d1 [d2][E2 Vd1 Y2 Fd1 Fd2].
exists (c1, d1), (c2, d2); rewrite /valid /= Vc1 Vd1.
rewrite /sepx/=/rel_prod/fprod /= Fc1 Fc2 Fd1 Fd2 Y1 Y2.
by rewrite pcmPE -E1 -E2 -!prod_eta.
Qed.

(* ker requires only that sep f is invertible (not that f itself is) *)
Lemma inv_ker (U V : pcm) (f : pcm_morph U V) :
        inv_rel (sep f) -> inv_rel (ker f).
Proof.
move=>Sf a1 a2 a' W /and3P [D1 /unitbP Eq1 _] /and3P [D2 /unitbP Eq2 /unitbP].
case/andP: (Sf _ _ _ W D1 D2)=>{}D1 {}D2.
rewrite /kerx !pfjoin ?(validLE3 W) //; last by rewrite (sepAxx W).
by rewrite /kerx Eq1 Eq2 D1 D2 !unitL=>->; rewrite /sepU pcmE.
Qed.

(* equalizer is invertible only for cancellative ranges *)
Lemma inv_eqlz (U : pcm) (V : eqcpcm) 
               (f : pcm_morph U V) (g : pcm_morph U V) :
        inv_rel (sep f) -> inv_rel (sep g) -> inv_rel (eqlz f g).
Proof.
move=>Sf Sg x y z W; rewrite /eqlzx. 
case/and4P=>X1 X2 Ex _ /and4P [Y1 Y2] Ey /eqP.
case/andP: (Sf _ _ _ W X1 Y1)=>E1 E1'.
case/andP: (Sg _ _ _ W X2 Y2)=>E2 E2'.
rewrite E1 E2 Ex Ey E1' E2' !pfjoin ?(validLE3 W) 2?(sepAxx W) //=.
rewrite -(eqP Ex) (eqP Ey) eq_refl => /joinxK ->; first by rewrite eqxx.
by rewrite pfV2 ?(validLE3 W) // (sepAxx W).
Qed.

(* this theorem generalizes the one from the POPL21 paper *)
(* to work with arbitrary sub-pcm over matching seprel *)
(* (the one in the paper worked with xsub explicitly) *)
(* can be further generalised to any D' that is compatible with D *)

Lemma inv_comp_sub (U V : pcm) (S : subpcm_struct U V) 
                   (W : pcm) (f : pcm_morph V W) :
        subsep S =2 sep f ->
        inv_morph f -> inv_morph (f \o pval S).
Proof.
move=>E [Sf Hf]; split=>[a1 a2 a' V1|a b1 b2 V1] /=; 
rewrite /sepx/= !pfT /=.
- by rewrite !pfjoin ?(validLE3 V1) //; apply: Sf; apply: pfV3.
rewrite pfunit /= => H1 /(Hf _ _ _ (pfVI V1) H1). 
case=>c1 [c2][Eq Vc H2 F1 F2]; exists (psub S c1), (psub S c2).
rewrite pfT /= -!pfjoin ?E //= -Eq psub_pval //=.
by rewrite !pval_psub ?(validL Vc,validR Vc) // E (sep0E Vc).
Qed.


