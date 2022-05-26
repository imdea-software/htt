From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap automap.
From HTT Require Import model heapauto.
From HTT Require Import llist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Record buffer (T : Type) : Type :=
  Buf {active: ptr; inactive: ptr; len : ptr; capacity : nat}.

Definition BufferFull : exn := exn_from_nat 10.

Module Buffer.
Section Buffer.
Variable T : Type.
Notation buffer := (buffer T).

Definition is_buffer (a i : ptr) (m n : nat) (xs : seq T) :=
  [Pred h | exists (ys : seq T) ha hi,
            [/\ h = ha \+ hi,
                n = size xs + size ys,
                m = size xs,
                ha \In lseg a i xs &
                hi \In lseg i a ys]
  ].

Definition shape (b : buffer) (xs : seq T) :=
  [Pred h | exists a i m h',
            [/\ valid (active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h'))),
                h = active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h')) &
                h' \In is_buffer a i m (capacity b) xs]].

(* main methods *)

(* new buffer *)

(* TODO move to interlude *)
Lemma rcons_nseq {A : Type} n (x : A) :
  rcons (nseq n x) x = nseq n.+1 x.
Proof. by elim: n=>//=n ->. Qed.

Definition new_loopT (n : nat) (init : T) : Type :=
  forall (pk : ptr * nat),
  {q}, STsep (fun h => pk.2 < n /\ h \In lseg pk.1 q (nseq pk.2 init),
             [vfun p' => lseg p' q (nseq n.-1 init)]).

Program Definition new (n : nat) (init : T) :
          STsep (emp, [vfun v => shape v [::]]) :=
  Do (let run := Fix (fun (go : new_loopT n init) '(r,k) =>
                      Do (if k < n.-1 then
                            p' <-- allocb r 2;
                            p' ::= init;;
                            go (p', k.+1)
                          else ret r)) in
      if 0 < n then
        p <-- allocb null 2;
        p ::= init;;
        q <-- run (p, 0);
        p.+ 1 ::= q;;
        m <-- alloc 0;
        pi <-- alloc q;
        pa <-- alloc q;
        ret (Buf T pa pi m n)
      else m <-- alloc 0;
           pi <-- alloc null;
           pa <-- alloc null;
           ret (Buf T pa pi m 0)).
Next Obligation.
move=>n init go [r k] _ _[->->][q []] i /= [Hk H]; case: ltnP.
- move=>H0.
  step=>p'; step; rewrite unitR.
  apply: [gE q]=>//=; split; first by rewrite -ltn_predRL.
  by exists r, i; rewrite joinA.
move=>H2; move: Hk=>/[dup]/ltn_predK=>{1}<-; rewrite ltnS=>H1.
by step=>_; have/eqP <-: (k == n.-1) by rewrite eqn_leq H1 H2.
Qed.
Next Obligation.
move=>n init [] _ /= ->; case: ifP.
- move=>H0.
  step=>p; step; rewrite !unitR.
  rewrite -[_ \+ _]unitL; apply: [stepR p]@Unit=>//=q h H.
  step; step=>m; step=>pi; step=>pa; step=>V.
  exists q, q, 0, (h \+ (p :-> init \+ p.+ 1 :-> q)); split=>//.
  exists (nseq n init), Unit, (h \+ (p :-> init \+ p.+ 1 :-> q)); split=>//=.
  - by rewrite unitL.
  - by rewrite add0n size_nseq.
  by rewrite -(ltn_predK H0) -rcons_nseq; apply/lseg_rcons; exists p, h.
move=>_; step=>m; step=>pi; step=>pa; step=>V.
exists null, null, 0, Unit=>/=; split=>//.
by exists [::], Unit, Unit; split=>//; rewrite unitR.
Qed.

Program Definition write (x : T) (b : buffer) :
  {xs}, STsep (shape b xs,
               fun y h => match y with
                          | Val _ => h \In shape b (rcons xs x)
                          | Exn e => e = BufferFull /\ h \In shape b xs
               end) :=
  Do (m <-- !len b;
      if m < capacity b then
        i <-- !inactive b;
        i ::= x;;
        r <-- !i.+ 1;
        inactive b ::= (r : ptr);;
        len b ::= m.+1
      else throw BufferFull).
Next Obligation.
move=>x b [xs []] _ /= [a][i][m][h][_ -> [ys][ha][hi][E Ec -> Ha Hi]].
rewrite Ec; step; case: ltnP.
- rewrite -{1}(addn0 (size xs)) ltn_add2l => Hys.
  step; rewrite E.
  case/lseg_case: Hi.
  - by case=>_ Eys; rewrite Eys in Hys.
  case=>y[r][h'][Eys Ehi H']; rewrite Ehi.
  do 4![step]=>V.
  exists a, r, (size xs).+1, (ha \+ (i :-> x \+ (i.+ 1 :-> r \+ h'))); split=>//.
  exists (behead ys), (ha \+ (i :-> x \+ i.+ 1 :-> r)), h'; split=>//.
  - by rewrite !joinA.
  - by rewrite Ec size_rcons size_behead -subn1 addnABC // subn1.
  - by rewrite size_rcons.
  by apply/lseg_rcons; exists i, ha.
rewrite -{2}(addn0 (size xs)) leq_add2l leqn0 => /nilP Eys.
step=>V; split=>//.
exists a, i, (size xs), h; split=>//.
by exists [::], ha, hi; rewrite Eys in Ec Hi; split.
Qed.