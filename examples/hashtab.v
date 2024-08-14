(*
Copyright 2010 IMDEA Software Institute
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
From mathcomp Require Import ssrnat eqtype seq fintype tuple finfun finset.
From pcm Require Import options axioms prelude pred ordtype finmap.
From pcm Require Import pcm unionmap heap autopcm.
From htt Require Import options model heapauto.
From htt Require Import array kvmaps.

Module HashTab.
Section HashTab.

(* hash table is array of buckets, i.e. KV maps *)
(* bucket indices are provided by the hash function *)
(* using dynaming kv-maps for buckets *)
(* DEVCOMMENT: *)
(*  it's possible to develop this with static buckers *)
(* /DEVCOMMENT *)

Variables (K : ordType) (V : Type) (buckets : DynKVmap.Sig K V)
          (n : nat) (hash : K -> 'I_n).
Definition hashtab := {array 'I_n -> DynKVmap.tp buckets}.
Notation KVshape := (@DynKVmap.shape _ _ buckets).
Notation table := (table KVshape).
Notation nil := (nil K V).

(* hash table is specified by a single finMap *)
(* which is the "flattening" of all buckets *)
Definition shape x (s : finMap K V) :=
  [Pred h | exists (tab : {ffun 'I_n -> DynKVmap.tp buckets})   (* array spec *)
                   (bucket : 'I_n -> finMap K V),            (* buckets spec *)
            [/\ forall k, fnd k s = fnd k (bucket (hash k)),
                forall i k, k \in supp (bucket i) -> hash k = i &
                h \In Array.shape x tab # sepit setT (table tab bucket)] ].

(* new hash map is an array of `n` empty buckets *)

(* bucket initialization loop invariant: *)
(* at iteration k, the heap holds the array and k empty buckets *)
Definition new_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists tab,
           h \In Array.shape x tab #
                   sepit [set x:'I_n | x < k] (table tab (fun=> nil)),
        [vfun y => shape y nil]).

Program Definition new : STsep (emp, [vfun y => shape y nil]) :=
  Do (t <-- Array.new 'I_n (DynKVmap.default buckets);
      let go := ffix (fun (loop : new_loopinv t) k =>
                  Do (if decP (b := k < n) idP is left pf then
                        b <-- DynKVmap.new buckets;
                        Array.write t (Ordinal pf) b;;
                        loop k.+1
                      else ret t))
      in go 0).
(* first the bucket initialization loop *)
Next Obligation.
(* pull out preconditions, branch on k comparison *)
move=>/= arr loop k [] _ /= [Eleq][tab][h1][h2][-> H1].
case: decP=>[{Eleq}pf H2|]; last first.
(* k = n, return the array pointer *)
- case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H; step=>_.
  (* pass through the constructed table, aggregated finmap is empty *)
  exists tab, (fun => nil); split=>//; exists h1, h2; split=>//{h1 H1}.
  (* h2 holds the table *)
  by apply/tableP2: H=>//= x; rewrite Ek !in_set ltn_ord.
(* k < n, allocate an empty bucket by framing on Unit *)
apply: [stepU]=>//= b m Hm.
(* write its id to the array under index k *)
apply: [stepX tab] @ h1=>{h1 H1}//= _ m2 E2.
(* invoke the loop *)
apply: [gE]=>//=; split=>//; rewrite joinCA.
(* extend the table by the new index/bucket pair, simplify *)
exists [ffun z => if z == Ordinal pf then b else tab z], m2, (m \+ h2).
split=>//{m2 E2}.
(* remove the new bucket from the heap *)
rewrite (sepitS (Ordinal pf)) in_set leqnn {1}/table ffunE eq_refl.
exists m, h2; do!split=>{m Hm}//; apply: tableP2 H2=>{h2}//.
- case=>x Hx; rewrite !in_set in_set1 -val_eqE /= ltnS (leq_eqVlt x).
  by case: ltngtP.
(* removing k from the domain of the new table gives the old table back *)
by move=>x _; rewrite in_set ffunE; case: eqP=>//->; rewrite ltnn.
Qed.
(* the outer function *)
Next Obligation.
(* simplify *)
move=>/= [] _ ->.
(* allocate the array *)
apply: [stepE]=>//= y m Hm.
(* invoke the loop with index 0 *)
apply: [gE]=>//=; split=>//.
(* the table is empty *)
exists [ffun => DynKVmap.default buckets], m, Unit; split=>//=.
- by rewrite unitR.
(* there are no buckets in the heap yet *)
by rewrite (eq_sepit (s2 := set0)) // sepit0.
Qed.

(* freeing hashtable = freeing the array + buckets *)

(* loop invariant: *)
(* at iteration k, the heap still holds the array and n-k buckets *)
Definition free_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists t b,
          h \In Array.shape x t #
                  sepit [set x:'I_n | x >= k] (table t b),
        [vfun _ : unit => emp]).

Program Definition free x : STsep {s} (shape x s,
                                      [vfun _ : unit => emp]) :=
  (* the extra Do here enables deriving precondition from the loop *)
  Do (ffix (fun (loop : free_loopinv x) k =>
        Do (if decP (b := k < n) idP is left pf then
              b <-- Array.read x (Ordinal pf);
              DynKVmap.free b;;
              loop k.+1
             else Array.free x)) 0).
(* first the loop *)
Next Obligation.
(* pull out the ghost + preconditions, branch on k comparison *)
move=>/= x loop k [] _ /= [Eleq][tf][bf][h1][h2][-> H1].
case: decP=>[pf H|]; last first.
(* k = n *)
- case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H.
  (* free the array *)
  apply: [gE]=>//=; exists tf.
  (* h2 is empty *)
  move: H; rewrite (eq_sepit (s2 := set0)).  
  - by rewrite sepit0=>->; rewrite unitR.
  by move=>y; rewrite Ek in_set in_set0 leqNgt ltn_ord.
(* k < n, read from array *)
apply: [stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the the k-th bucket *)
move: H; rewrite (sepitS (Ordinal pf)) in_set leqnn.
case=>h3[h4][{h2}-> H3 H4].
(* free it *)
apply: [stepX (bf (Ordinal pf))] @ h3=>{h3 H3}//= _ _ ->; rewrite unitL.
(* invoke loop, simplify *)
apply: [gE]=>//=; split=>//; exists tf, bf, h1, h4; split=>//.
(* drop the k-th entry from the table *)
apply/tableP2/H4=>//.
move=>z; rewrite !in_set in_set1; case: eqP=>/=.
- by move=>->/=; rewrite ltnn.
by move/eqP; rewrite -val_eqE /=; case: ltngtP.
Qed.
Next Obligation.
(* pull out ghost+preconditions *)
move=>/= x [fm][] h /= [tf][bf][_ _ H].
(* invoke the loop *)
by apply: [gE]=>//=; eauto.
Qed.

(* inserting into hashmap is inserting into *)
(* corresponding bucket + updating the array *)
(* returning the pointer is not needed *)
(* as the array is not moved *)
Program Definition insert x k v : 
  STsep {s} (shape x s, [vfun _ : unit => shape x (ins k v s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- DynKVmap.insert b k v;
      Array.write x hk b').
Next Obligation.
(* pull out ghost + deconstruct precondition *)
move=>/= x k v [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> /= H1 H2]]. 
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)) /table; case=>h3[h4][{h2}-> H3 H4].
(* insert into the bucket *)
apply/[stepX (bf (hash k))] @ h3=>{h3 H3}//= b' m2 H2.
(* write the bucket to the array, return the pointer *)
apply: [gX tf]@h1=>{h1 H1} //= _ m3 E3 _.
(* update the array and buckets' specs *)
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then ins k v (bf b) else bf b); split=>/=.
(* the new buckets spec is still a flattening *)
- move=>k0; rewrite fnd_ins; case: eqP=>[->|/eqP Ek].
  (* if the bucket was touched, we get the same value *)
  - by rewrite eq_refl fnd_ins eq_refl.
  (* if not, we get the old spec back *)
  by case: ifP=>_ //; rewrite fnd_ins (negbTE Ek).
(* the new buckets spec respects the hash *)
- move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_ins inE=>/orP; case; [move/eqP=>->|apply: Hh].
(* the shape is respected: first, the array fits *)
exists m3, (m2 \+ h4); split=>{Hf Hh m3 E3}//.
(* split out the modified bucket *)
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl.
exists m2, h4; split=>{m2 H2} //.
(* the table fits too *)
apply/tableP/H4=>/= x0;
by rewrite !in_set in_set1 andbT ?ffunE =>/negbTE->.
Qed.

(* removing from hashmap is removing from *)
(* corresponding bucket + updating the array *)
(* returning the pointer is again not needed *)
Program Definition remove x k :
  STsep {s} (shape x s,
             [vfun _ : unit => shape x (rem k s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- DynKVmap.remove b k;
      Array.write x hk b').
Next Obligation.
(* pull out ghost + destructure precondition *)
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> /= H1 H2]].
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)); case=>h3[h4][{h2}-> H3 H4].
(* insert into the bucket *)
apply/[stepX (bf (hash k))] @ h3=>{h3 H3}//= b' m2 H2.
(* write the bucket to the array, return the pointer *)
apply/[gX tf] @ h1=>{H1}//= _ m3 E3 _.
(* update the array and buckets' specs *)
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then rem k (bf b) else bf b); split=>/=.
(* the new buckets spec is still a flattening *)
- move=>k0; rewrite fnd_rem; case: eqP.
  (* if the bucket was touched, the value is gone *)
  - by move=>->; rewrite eq_refl fnd_rem eq_refl.
  (* if not, we get the old spec back *)
  by move/eqP=>Ek; case: ifP=>_ //; rewrite fnd_rem (negbTE Ek).
(* the new buckets spec respects the hash *)
- move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_rem !inE=>/andP [] _; apply: Hh.
(* the shape is respected: first, the array fits *)
exists m3, (m2\+ h4); split=>{m3 E3 Hf Hh}//.
(* split out the modified bucket *)
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl.
exists m2, h4; split=>{m2 H2} //.
(* the table fits too *)
apply/tableP/H4=>/= x0; 
by rewrite !in_set in_set1 andbT ?ffunE => /negbTE->.
Qed.

(* looking up in a hashmap is looking up in the corresponging bucket *)
Program Definition lookup x k :
  STsep {s} (shape x s,
             [vfun y m => m \In shape x s /\ y = fnd k s]) :=
  Do (b <-- Array.read x (hash k);
      DynKVmap.lookup b k).
Next Obligation.
(* pull out ghost + destructure precondition *)
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> H1 H2]].
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)); case=>h3[h4][{h2}-> H3 H4].
(* look up in the bucket, simplify *)
apply/[gX (bf (hash k))] @ h3=>{h3 H3}//= r m2 [H2 Hr] _.
split; last by rewrite Hf.
(* the shape is preserved, as nothing was modified *)
exists tf, bf; split=>//=; exists h1, (m2 \+ h4); split=>{h1 H1} //.
by rewrite (sepitT1 (hash k)); vauto.
Qed.

(* hash table is a *static* KV map *)
Definition HashTab := KVmap.make (Array null) new free insert remove lookup.

End HashTab.
End HashTab.

Definition HT K V := HashTab.HashTab (DynAssocList.AssocList K V).
