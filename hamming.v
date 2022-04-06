(** * Hamming Code 4 bits to 7 bits
  #<script src='https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML'></script>#
*)

(** ** What is Hamming Code ?

    #\(HC(7, 4)\)# is a block code used to
    encode 4 bits of information over 7 bits
    (so we add 3 bits of redundancy).
    
    Hamming Codes are powerfull enough
    to detect and correct 1 bit error:
    
    - if we encode 4 bits using #\(HC(7, 4)\)#
      and one of the bits is flipped during transmission,
      the message is going to be correctly interpreted by the
      receiver.
    - if 2 bits or more are flipped,
      the error could remain undetected or could be
      detected but miss-corrected.
*)


Inductive data : Type :=
  Data (_ _ _ _ : bool).

Inductive block : Type :=
  Block (_ _ _ _ _ _ _ : bool).

(** Error detection and correction is based on so-called "Syndroms".
    Syndroms are values computed during the decoding phase and used
    to locate the error.
*)
Inductive syndrom : Type :=
  Syndrom (_ _ _ : bool).

Notation "x ^ y" := (xorb x y).

(** Encode data using #\(HC(7, 4)\)#. *)
Definition encode '(Data c3 c5 c6 c7) : block :=
  let c1 := c3 ^ c5 ^ c7 in
  let c2 := c3 ^ c6 ^ c7 in
  let c4 := c5 ^ c6 ^ c7 in
  Block c1 c2 c3 c4 c5 c6 c7.

(** Correct a block based on the computed syndrom. *)
Definition correct '(Syndrom s1 s2 s3) '(Block c1 c2 c3 c4 c5 c6 c7) : block :=
  match s1, s2, s3 with
  | false, false, false => Block c1 c2 c3 c4 c5 c6 c7
  | true, false, false  => Block (negb c1) c2 c3 c4 c5 c6 c7
  | false, true, false  => Block c2 (negb c2) c3 c4 c5 c6 c7
  | true, true, false   => Block c1 c2 (negb c3) c4 c5 c6 c7
  | false, false, true  => Block c1 c2 c3 (negb c4) c5 c6 c7
  | true, false, true   => Block c1 c2 c3 c4 (negb c5) c6 c7
  | false, true, true   => Block c1 c2 c3 c4 c5 (negb c6) c7
  | true, true, true    => Block c1 c2 c3 c4 c5 c6 (negb c7)
  end.

(** Decode without trying to correct *)
Definition decode_aux '(Block c1 c2 c3 c4 c5 c6 c7) : data :=
  Data c3 c5 c6 c7.

(** Decode and correct if needed *)
Definition decode '(Block c1 c2 c3 c4 c5 c6 c7) : data :=
  let s1 := c1 ^ c3 ^ c5 ^ c7 in
  let s2 := c2 ^ c3 ^ c6 ^ c7 in
  let s3 := c4 ^ c5 ^ c6 ^ c7 in
  let corrected := correct (Syndrom s1 s2 s3) (Block c1 c2 c3 c4 c5 c6 c7) in
  decode_aux corrected.

(** #\(HC(7, 4)\)# is a code:
  [decode] and [encode] define a bijection between
  [data] and [block]
*)
Lemma encode_decode :
  forall d, decode (encode d) = d.
Proof.
  now intros [[] [] [] []].
Qed.

(** ** Error Correction
    The key advantage of Hamming Code over an arbitrary code 
    is its ability to detect and correct errors.
    
    We start by modelling errors resulting of 1 single bit flip.
    The statement [error msg1 msg2] assert that [msg2] is the result of flipping 1 bit in [msg1].
*)

Inductive error : block -> block -> Prop :=
  | error_1 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block (negb c1) c2 c3 c4 c5 c6 c7)
  | error_2 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 (negb c2) c3 c4 c5 c6 c7)
  | error_3 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 c2 (negb c3) c4 c5 c6 c7)
  | error_4 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 c2 c3 (negb c4) c5 c6 c7)
  | error_5 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 c2 c3 c4 (negb c5) c6 c7)
  | error_6 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 c2 c3 c4 c5 (negb c6) c7)
  | error_7 c1 c2 c3 c4 c5 c6 c7 : error (Block c1 c2 c3 c4 c5 c6 c7) (Block c1 c2 c3 c4 c5 c6 (negb c7))
  .

(** Hamming Code can always correct 1 error:
    For any piece of [data], if exactly 1 bit is
    flipped during transmision, the error is corrected
    and [d] is correctly decoded.
*)
Lemma HC_correct_1_error :
  forall d c,
    error (encode d) c -> decode c = d.
Proof.
  intros [[] [] [] []].
  all: now inversion_clear 1.
Qed.

(** Hamming Code may fail to correct 2 errors or more:
    There exists a piece of [data] [d] and 2 errors [c1] [c2]
    such that if these [c1] and [c2] occurs during transmission,
    [d] is incorrectly decoded.
*)
Lemma HC_dont_correct_2_errors :
  exists d c1 c2,
    error (encode d) c1 /\
    error c1 c2 /\
    decode c2 <> d.
Proof.
  set (d := Data true true true true).
  exists d.
  exists (Block false true true true true true true).
  exists (Block false false true true true true true).
  now try repeat econstructor.
Qed.