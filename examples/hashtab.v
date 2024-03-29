From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq fintype tuple finfun finset.
From pcm Require Import options axioms prelude pred ordtype finmap.
From pcm Require Import pcm unionmap heap autopcm.
From htt Require Import model heapauto.
From htt Require Import array kvmaps.

Module HashTab.
Section HashTab.

(* a hash table is an array of buckets, i.e. KV maps *)
(* bucket indices are provided by the hash function *)

Variables (K : ordType) (V : Type) (buckets : KVmap.Sig K V)
          (n : nat) (hash : K -> 'I_n).
Definition hashtab := {array 'I_n -> KVmap.tp buckets}.
Notation KVshape := (@KVmap.shape _ _ buckets).
Notation table := (table KVshape).
Notation nil := (nil K V).

Opaque Array.write Array.new Array.free Array.read.

(* hash table is specified by a single finMap *)
(* which is morally a "flattening" of all buckets *)
Definition shape x (s : finMap K V) :=
  [Pred h | exists (tab : {ffun 'I_n -> KVmap.tp buckets})   (* array spec *)
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
  Do (t <-- Array.new _ (KVmap.default buckets);
      let go := Fix (fun (loop : new_loopinv t) k =>
                  Do (if decP (b := k < n) idP is left pf then
                        b <-- KVmap.new buckets;
                        Array.write t (Ordinal pf) b;;
                        loop k.+1
                      else ret t))
      in go 0).
(* first the bucket initialization loop *)
Next Obligation.
(* pull out preconditions, branch on k comparison *)
move=>/= arr loop k [] _ /= [Eleq][tab][h1][h2][-> H1]; case: decP=>[{Eleq}pf H2|]; last first.
- (* k = n, return the array pointer *)
  case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H; step=>_.
  (* pass through the constructed table, aggregated finmap is empty *)
  exists tab, (fun => nil); split=>//; exists h1, h2; split=>//{h1 H1}.
  (* h2 holds the table *)
  by apply/tableP2: H=>//= x; rewrite Ek !in_set ltn_ord.
(* k < n, allocate an empty bucket by framing on Unit *)
apply: [stepU]=>//= b m Hm.
(* write its id to the array under index k *)
apply: [stepX tab] @ h1=>{h1 H1}//= _ m2 [E2 V2].
(* invoke the loop *)
apply: [gE]=>//=; split=>//; rewrite joinCA.
(* extend the table by the new index/bucket pair, simplify *)
exists [ffun z => if z == Ordinal pf then b else tab z], m2, (m \+ h2); split=>//{m2 E2 V2}.
(* remove the new bucket from the heap *)
rewrite (sepitS (Ordinal pf)) in_set leqnn {1}/table ffunE eq_refl; exists m, h2; do!split=>{m Hm}//.
apply: tableP2 H2=>{h2}//.
- by case=>x Hx; rewrite !in_set -val_eqE /= ltnS (leq_eqVlt x); case: ltngtP.
(* removing k from the domain of the new table gives the old table back *)
by move=>x _; rewrite in_set ffunE; case: eqP=>//->; rewrite ltnn.
Qed.
(* now the outer function *)
Next Obligation.
(* simplify *)
move=>/= [] _ ->.
(* allocate the array *)
apply: [stepE]=>//= y m [Hm Vm].
(* invoke the loop with index 0 *)
apply: [gE]=>//=; split=>//.
(* the table is empty *)
exists [ffun => KVmap.default buckets], m, Unit; split=>//=; first by rewrite unitR.
(* there are no buckets in the heap yet *)
by rewrite (eq_sepit (s2 := set0)) // sepit0.
Qed.

(* freeing a hashtable is freeing the array + buckets *)

(* loop invariant: *)
(* at iteration k, the heap still holds the array and n-k buckets *)
Definition free_loopinv x := forall k,
  STsep (fun h => k <= n /\ exists t b,
          h \In Array.shape x t #
                  sepit [set x:'I_n | x >= k] (table t b),
         [vfun _ : unit => emp]).

Program Definition free x : {s}, STsep (shape x s,
                                        [vfun _ : unit => emp]) :=
  (* we add an extra Do here so we can derive the precondition from the loop *)
  Do (Fix (fun (loop : free_loopinv x) k =>
        Do (if decP (b := k < n) idP is left pf then
              b <-- Array.read x (Ordinal pf);
              KVmap.free b;;
              loop k.+1
             else Array.free x)) 0).
(* first the loop *)
Next Obligation.
(* pull out the ghost + preconditions, branch on k comparison *)
move=>/= x loop k [] _ /= [Eleq][tf][bf][h1][h2][-> [H1 V1]]; case: decP=>[pf H|]; last first.
- (* k = n *)
  case: ltnP Eleq (eqn_leq k n)=>// _ -> /= /eqP Ek _ H.
  (* free the array *)
  apply: [gE]=>//=; exists tf.
  (* h2 is empty *)
  move: H; rewrite (eq_sepit (s2 := set0)); first by rewrite sepit0=>->; rewrite unitR.
  by move=>y; rewrite Ek in_set in_set0 leqNgt ltn_ord.
(* k < n, read from array *)
apply: [stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the the k-th bucket *)
move: H; rewrite (sepitS (Ordinal pf)) in_set leqnn; case=>h3[h4][{h2}-> H3 H4].
(* free it *)
apply: [stepX (bf (Ordinal pf))] @ h3=>{h3 H3}//= _ _ ->; rewrite unitL.
(* invoke loop, simplify *)
apply: [gE]=>//=; split=>//; exists tf, bf, h1, h4; split=>//.
(* drop the k-th entry from the table *)
apply/tableP2/H4=>//.
move=>z; rewrite !in_set; case: eqP=>/=.
- by move=>->/=; rewrite ltnn.
by move/eqP; rewrite -val_eqE /=; case: ltngtP.
Qed.
Next Obligation.
(* pull out ghost+preconditions *)
move=>/= x [fm][] h /= [tf][bf][_ _ H].
(* invoke the loop *)
by apply: [gE]=>//=; eauto.
Qed.

(* inserting into a hashmap is inserting into corresponding bucket + updating the array *)
(* returning the pointer is technically not needed, as the array is not moved *)
(* but we need to fit the KV map API *)

Program Definition insert x k v : {s}, STsep (shape x s,
                                              [vfun y => shape y (ins k v s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- KVmap.insert b k v;
      Array.write x hk b';;
      ret x).
Next Obligation.
(* pull out ghost + deconstruct precondition *)
move=>/= x k v [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> [/= H1 _] H2]].
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)) /table; case=>h3[h4][{h2}-> H3 H4].
(* insert into the bucket *)
apply/[stepX (bf (hash k))] @ h3=>{h3 H3}//= b' m2 H2.
(* write the bucket to the array, return the pointer *)
apply/[stepX tf] @ h1=>{h1 H1}//= _ m3 [E3 V3]; step=>_.
(* update the array and buckets' specs *)
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then ins k v (bf b) else bf b); split=>/=.
- (* the new buckets spec is still a flattening *)
  move=>k0; rewrite fnd_ins; case: eqP=>[->|/eqP Ek].
  - (* if the bucket was touched, we get the same value *)
    by rewrite eq_refl fnd_ins eq_refl.
  (* if not, we get the old spec back *)
  by case: ifP=>_ //; rewrite fnd_ins (negbTE Ek).
- (* the new buckets spec respects the hash *)
  move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_ins inE=>/orP; case; [move/eqP=>->|apply: Hh].
(* the shape is respected: first, the array fits *)
exists m3, (m2 \+ h4); split=>{Hf Hh m3 E3 V3}//.
(* split out the modified bucket *)
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl; exists m2, h4; split=>{m2 H2}//.
(* the table fits too *)
by apply/tableP/H4=>/= x0; rewrite !in_set andbT ?ffunE =>/negbTE->.
Qed.

(* removing from a hashmap is removing from corresponding bucket + updating the array *)
(* returning the pointer is again not needed except for the API fit *)

Program Definition remove x k :
  {s}, STsep (shape x s,
             [vfun y => shape y (rem k s)]) :=
  Do (let hk := hash k in
      b  <-- Array.read x hk;
      b' <-- KVmap.remove b k;
      Array.write x hk b';;
      ret x).
Next Obligation.
(* pull out ghost + destructure precondition *)
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> [/= H1 _] H2]].
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)); case=>h3[h4][{h2}-> H3 H4].
(* insert into the bucket *)
apply/[stepX (bf (hash k))] @ h3=>{h3 H3}//= b' m2 H2.
(* write the bucket to the array, return the pointer *)
apply/[stepX tf] @ h1=>{H1}//= _ m3 [E3 V3]; step=>_.
(* update the array and buckets' specs *)
exists [ffun z => if z == hash k then b' else tf z],
       (fun b => if b == hash k then rem k (bf b) else bf b); split=>/=.
- (* the new buckets spec is still a flattening *)
  move=>k0; rewrite fnd_rem; case: eqP.
  - (* if the bucket was touched, the value is gone *)
    by move=>->; rewrite eq_refl fnd_rem eq_refl.
  (* if not, we get the old spec back *)
  by move/eqP=>Ek; case: ifP=>_ //; rewrite fnd_rem (negbTE Ek).
- (* the new buckets spec respects the hash *)
  move=>i0 k0; case: eqP; last by move=>_; apply: Hh.
  by move=>->; rewrite supp_rem !inE=>/andP [] _; apply: Hh.
(* the shape is respected: first, the array fits *)
exists m3, (m2\+ h4); split=>{m3 E3 V3 Hf Hh}//.
(* split out the modified bucket *)
rewrite (sepitT1 (hash k)) /table /= ffunE eq_refl; exists m2, h4; split=>{m2 H2}//.
(* the table fits too *)
by apply/tableP/H4=>/= x0; rewrite !in_set andbT ?ffunE =>/negbTE->.
Qed.

(* looking up in a hashmap is looking up in the corresponging bucket *)

Program Definition lookup x k :
  {s}, STsep (shape x s,
             [vfun y m => m \In shape x s /\ y = fnd k s]) :=
  Do (b <-- Array.read x (hash k);
      KVmap.lookup b k).
Next Obligation.
(* pull out ghost + destructure precondition *)
move=>/= x k [fm][] _ /= [tf][bf][Hf Hh [h1][h2][-> H1 H2]].
(* read the bucket from array *)
apply/[stepX tf, h1] @ h1=>//= _ _ [->->].
(* split out the bucket in the heap *)
move: H2; rewrite (sepitT1 (hash k)); case=>h3[h4][{h2}-> H3 H4].
(* look up in the bucket, simplify *)
apply/[gX (bf (hash k))] @ h3=>{h3 H3}//= r m2 [H2 Hr] _; split; last by rewrite Hf.
(* the shape is preserved, as nothing was modified *)
exists tf, bf; split=>//=; exists h1, (m2 \+ h4); split=>{h1 H1}//.
by rewrite (sepitT1 (hash k)); vauto.
Qed.


(* hash table is a KV map *)

Definition HashTab := KVmap.make (Array null) new free insert remove lookup.

End HashTab.
End HashTab.

Definition HT K V := HashTab.HashTab (AssocList.AssocList K V).