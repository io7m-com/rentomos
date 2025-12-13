(*
 * Copyright © 2025 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Psatz.

Import ListNotations.

Local Open Scope string_scope.

Require Import com.io7m.entomos.Alignment.
Require Import com.io7m.entomos.Divisible.

(** The type of stream elements. *)
Inductive streamE : Set :=
  (** A 64-bit IEEE754 binary64 value. *)
  | Vf64 : R -> streamE
  (** A 64-bit unsigned integer. *)
  | Vu64 : nat -> streamE
  (** A 32-bit unsigned integer. *)
  | Vu32 : nat -> streamE
  (** An 8-bit unsigned integer. *)
  | Vu8  : nat -> streamE.

Definition u8byte (b : byte) : streamE :=
  Vu8 (Byte.to_nat b).

Definition streamEIsU8 (e : streamE) : Prop :=
  match e with
  | Vf64 _ => False
  | Vu64 _ => False
  | Vu32 _ => False
  | Vu8  _ => True
  end.

(** A proposition that describes a well-formed stream. *)
Inductive streamWellFormed : list streamE -> Prop :=
  (** An empty stream is well-formed. *)
  | BEPEmpty  : streamWellFormed []
  (** A stream consisting of a single 64-bit float is well-formed. *)
  | BEPVf64   : forall k, streamWellFormed [Vf64 k]
  (** A stream consisting of a single 64-bit integer is well-formed. *)
  | BEPVu64   : forall k, streamWellFormed [Vu64 k]
  (** A stream consisting of a single 32-bit integer is well-formed. *)
  | BEPVu32   : forall k, streamWellFormed [Vu32 k]
  (** A stream consisting of a number of 8-bit values of a length divisible by 4 is well-formed. *)
  | BEPVu8s   : forall es, Forall streamEIsU8 es -> length (es) mod 4 = 0 -> streamWellFormed es
  (** The concatenation of two well-formed streams is well-formed. *)
  | BEPAppend : forall xs ys, streamWellFormed xs -> streamWellFormed ys -> streamWellFormed (xs ++ ys).

(** The size in octets of a stream element. *)
Definition streamElementSize (s : streamE) : nat :=
  match s with
  | Vf64 _ => 8
  | Vu64 _ => 8
  | Vu32 _ => 4
  | Vu8  _ => 1
  end.

(** The size of a stream is the sum of the size of its elements. *)
Definition streamSize (s : list streamE) : nat :=
  fold_right plus 0 (map streamElementSize s).

Section binaryExpressions.
  Local Unset Elimination Schemes.

  (** The binary expression type. *)
  Inductive binaryExp : Set :=
    (** A 32-bit unsigned integer. *)
    | BiU32     : nat -> binaryExp
    (** A 64-bit unsigned integer. *)
    | BiU64     : nat -> binaryExp
    (** A 64-bit IEEE754 binary64 value. *)
    | BiF64     : R -> binaryExp
    (** A sequence of bytes. *)
    | BiBytes   : list byte -> binaryExp
    (** A sequence of bytes describing UTF-8 encoded text. *)
    | BiUTF8    : list byte -> binaryExp
    (** An array of binary expressions. *)
    | BiArray   : list binaryExp -> binaryExp
    (** A section of reserved space. *)
    | BiReserve : nat -> binaryExp
    (** A record with named binary expression members. *)
    | BiRecord  : list (string * binaryExp) -> binaryExp.

  Section binaryExp_rect.
    Variable P             : binaryExp -> Type.
    Variable P_list        : list binaryExp -> Type.
    Hypothesis P_nil       : P_list [].
    Hypothesis P_cons      : forall x xs, P x -> P_list xs -> P_list (x :: xs).
    Hypothesis P_BiU32     : forall x, P (BiU32 x).
    Hypothesis P_BiU64     : forall x, P (BiU64 x).
    Hypothesis P_BiF64     : forall x, P (BiF64 x).
    Hypothesis P_BiBytes   : forall bs, P (BiBytes bs).
    Hypothesis P_BiUTF8    : forall bs, P (BiUTF8 bs).
    Hypothesis P_BiArray   : forall bs, P_list bs -> P (BiArray bs).
    Hypothesis P_BiReserve : forall x, P (BiReserve x).
    Hypothesis P_BiRecord  : forall fs, P_list (map snd fs) -> P (BiRecord fs).

    Fixpoint binaryExp_rect (b : binaryExp) : P b :=
      let
        fix expForAll (xs : list binaryExp) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (binaryExp_rect y) (expForAll ys)
          end
      in let
        fix forAllSnd (fs : list (string * binaryExp)) : P_list (map snd fs) :=
          match fs as rf return P_list (map snd rf) with
          | []             => @P_nil
          | ((_, y) :: ys) => @P_cons y (map snd ys) (binaryExp_rect y) (forAllSnd ys)
          end
      in
        match b with
        | BiU32 c     => P_BiU32 c
        | BiU64 c     => P_BiU64 c
        | BiF64 c     => P_BiF64 c
        | BiBytes bs  => P_BiBytes bs
        | BiUTF8 bs   => P_BiUTF8 bs
        | BiArray es  => P_BiArray es (expForAll es)
        | BiReserve c => P_BiReserve c
        | BiRecord fs => P_BiRecord fs (forAllSnd fs)
        end.
  End binaryExp_rect.

  Section binaryExp_ind.
    Variable P             : binaryExp -> Prop.
    Hypothesis P_BiU32     : forall x, P (BiU32 x).
    Hypothesis P_BiU64     : forall x, P (BiU64 x).
    Hypothesis P_BiF64     : forall x, P (BiF64 x).
    Hypothesis P_BiBytes   : forall bs, P (BiBytes bs).
    Hypothesis P_BiUTF8    : forall bs, P (BiUTF8 bs).
    Hypothesis P_BiArray   : forall bs, Forall P bs -> P (BiArray bs).
    Hypothesis P_BiReserve : forall x, P (BiReserve x).
    Hypothesis P_BiRecord  : forall fs, Forall P (map snd fs) -> P (BiRecord fs).

    Definition binaryExp_ind (b : binaryExp) : P b :=
      binaryExp_rect
        P
        (Forall P)
        (Forall_nil P)
        (Forall_cons (P:=P)) 
        P_BiU32
        P_BiU64
        P_BiF64
        P_BiBytes
        P_BiUTF8
        P_BiArray
        P_BiReserve
        P_BiRecord
        b.
  End binaryExp_ind.
End binaryExpressions.

(** The size of a binary expression in octets. *)
Fixpoint binarySize (b : binaryExp) : nat :=
  match b with
  | BiU32 _     => 4
  | BiU64 _     => 8
  | BiF64 _     => 8
  | BiBytes s   => 4 + asMultipleOf4 (length s)
  | BiUTF8 s    => 4 + asMultipleOf4 (length s)
  | BiArray f   => 4 + fold_right plus 0 (map binarySize f)
  | BiReserve s => asMultipleOf4 s
  | BiRecord f  => fold_right plus 0 (map (compose binarySize snd) f)
  end.

Definition binaryEvalPaddedBytes
  (b     : list byte)
  (align : nat)
  (Hneq  : 0 <> align)
: list streamE :=
  let vremaining := length b mod align in
    match vremaining with
    | 0 => map u8byte b
    | _ => map u8byte (b ++ repeat x00 (align - vremaining))
    end.

(** The binary evaluation function; produces a stream from an expression. *)
Fixpoint binaryEval (b : binaryExp) : list streamE :=
  match b with
  | BiU32 k     => [Vu32 k]
  | BiU64 k     => [Vu64 k]
  | BiF64 k     => [Vf64 k]
  | BiBytes s   => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 Alignment.p0not4)
  | BiUTF8 s    => (Vu32 (length s)) :: (binaryEvalPaddedBytes s 4 Alignment.p0not4)
  | BiArray f   => (Vu32 (length f)) :: concat (map binaryEval f)
  | BiReserve s => repeat (Vu8 0) (asMultipleOf4 s)
  | BiRecord f  => concat (map (compose binaryEval snd) f)
  end.

(** The size of a binary expression padded to 16 octet alignment. *)
Definition binarySizePadded16 (b : binaryExp) : nat :=
  asMultipleOf16 (binarySize b).

(** Shorthand for UTF-8 strings. *)
Definition utf8 (s : string) : binaryExp :=
  BiUTF8 (list_byte_of_string s).

(** Shorthand for integer types. *)
Definition u32 := BiU32.
(** Shorthand for integer types. *)
Definition u64 := BiU64.
(** Shorthand for real types. *)
Definition f64 := BiF64.

#[local]
Lemma fold_right_add_cons : forall x xs,
  x + fold_right plus 0 xs = fold_right plus 0 (x :: xs).
Proof. reflexivity. Qed.

#[local]
Lemma forall_map_binarySize : forall es,
  Forall (fun b : binaryExp => binarySize b mod 4 = 0) es
    <-> Forall (fun n => n mod 4 = 0) (map binarySize es).
Proof.
  intros es.
  induction es.
  constructor.
  - rewrite Forall_map.
    intros H. trivial.
  - rewrite Forall_map.
    intros H. trivial.
  - rewrite Forall_map.
    constructor.
    intros H; trivial.
    intros H; trivial.
Qed.

(** The size of a binary expression is always divisible by 4. *)
Theorem binarySizeMultiple4 : forall b, binarySize (b) mod 4 = 0.
Proof.
  intros b.
  induction b as [Hbu32|Hbu64|Hbf64|Hbbyte|Hbutf|xs HFA|Hbuns|xs HFF] using binaryExp_ind.
  (* U32 values are of size 4 *)
  - reflexivity.
  (* U64 values are of size 8 *)
  - reflexivity.
  (* F64 values are of size 8 *)
  - reflexivity.

  (* Byte array values are rounded up to a multiple of 4 and prefixed with 4 *)
  - unfold binarySize.
    unfold asMultipleOf4.
    remember (asMultipleOf (Datatypes.length Hbbyte) 4 Alignment.p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.Div0.add_mod_idemp_l size 4 4).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (asMultipleOfMod (Datatypes.length Hbbyte) 4 (Alignment.p0not4)).
    }
    rewrite Hm0.
    reflexivity.

  (* UTF-8 values are rounded up to a multiple of 4 and prefixed with 4 *)
  - unfold binarySize.
    unfold asMultipleOf4.
    remember (asMultipleOf (Datatypes.length Hbutf) 4 Alignment.p0not4) as size eqn:Heqsize.
    rewrite Nat.add_comm.
    rewrite <- (Nat.Div0.add_mod_idemp_l size 4 4).
    assert (size mod 4 = 0) as Hm0. {
      rewrite Heqsize.
      apply (asMultipleOfMod (Datatypes.length Hbutf) 4 (Alignment.p0not4)).
    }
    rewrite Hm0.
    reflexivity.

  (* Each element of an array is a multiple of 4, so the entire array is too. *)
  - unfold binarySize.
    fold binarySize.
    induction xs as [|y ys HforAllInd].
    -- reflexivity.
    -- assert (fold_right Init.Nat.add 0 (map binarySize (y :: ys)) mod 4 = 0) as HfoldEq. {
         apply (@divisibilityNFoldPlus 4 (map binarySize (y :: ys))).
         discriminate.
         rewrite <- forall_map_binarySize.
         exact HFA.
       }
       rewrite map_cons.
       rewrite map_cons in HfoldEq.
       assert (4 mod 4 = 0) as H4mod40 by (reflexivity).
       assert (0 <> 4) as H0n4 by (discriminate).
       apply (divisiblityNAdd 4 (fold_right add 0 (binarySize y :: map binarySize ys)) 4 H0n4 H4mod40 HfoldEq).

  (* Unspecified values are rounded up. *)
  - unfold binarySize.
    unfold asMultipleOf4.
    rewrite asMultipleOfMod.
    reflexivity.

  (* Each element of an record is a multiple of 4, so the entire record is too. *)
  - unfold binarySize.
    fold binarySize.
    induction xs as [|y ys HforAllInd].
    -- reflexivity.
    -- rewrite map_cons.
       rewrite map_cons in HFF.
       rewrite <- fold_right_add_cons.
       apply divisiblityNAdd.
       discriminate.
       apply (Forall_inv HFF).
       apply HforAllInd.
       apply (Forall_inv_tail HFF).
Qed.

#[local]
Lemma sub_0_lt_ymx : forall x y,
  0 <= x -> x < y -> 0 < y - x.
Proof.
  intros x y Hle Hlt.
  destruct x as [|a].
  - rewrite Nat.sub_0_r.
    exact Hlt.
  - rewrite <- Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r.
    exact Hlt.
Qed.

#[local]
Lemma mod_sub : forall x m,
  0 < m -> 0 < m - (x mod m) <= m.
Proof.
  intros x m Hlt.
  constructor.
  - assert (0 <= x mod m < m) as HmRange. {
      apply Nat.mod_bound_pos.
      apply Nat.le_0_l.
      exact Hlt.
    }
    destruct HmRange as [HA HB].
    remember (x mod m) as y.
    apply (sub_0_lt_ymx y m HA HB).
  - assert (x mod m < m) as HmRange. {
      apply Nat.mod_upper_bound.
      apply Nat.neq_sym.
      apply Nat.lt_neq.
      exact Hlt.
    }
    apply Nat.le_sub_l.
Qed.

#[local]
Lemma mod_opposition : forall x a,
  0 <> a -> x mod a + (a - x mod a) = a.
Proof.
  intros x a Hnz.
  assert (x mod a < a) as Hxma. {
    apply (Nat.mod_upper_bound).
    apply Nat.neq_sym.
    exact Hnz.
  }
  remember (x mod a) as y eqn:Heqy.
  lia.
Qed.

(** The length of an evaluated binary expression padded to _a_ is always divisible by _a_. *)
Theorem binaryEvalPaddedBytesAligned : forall bs a (Hnz : 0 <> a),
  length (binaryEvalPaddedBytes bs a Hnz) mod a = 0.
Proof.
  intros bs a Hnz.
  unfold binaryEvalPaddedBytes.
  destruct (Datatypes.length bs mod a) eqn:Hlen.
  - rewrite length_map.
    exact Hlen.
  - rewrite length_map.
    rewrite length_app.
    rewrite repeat_length.
    rewrite <- Hlen.
    remember (Datatypes.length bs) as x.
    rewrite <- (Nat.Div0.add_mod_idemp_l x (a - x mod a) a).
    assert ((x mod a + (a - x mod a)) = a) as Heqa. {
      rewrite (mod_opposition x a Hnz).
      reflexivity.
    }
    rewrite Heqa.
    apply Nat.Div0.mod_same.
Qed.

#[local]
Lemma repeat_eq : forall (A : Type) (P : A -> Prop) (n : nat) (x : A),
  Forall (eq x) (repeat x n).
Proof.
  intros A P n x.
  induction n as [|m Hm].
  - constructor.
  - simpl.
    constructor.
    reflexivity.
    exact Hm.
Qed.

#[local]
Lemma Forall_implies : forall (A : Type) (P : A -> Prop) (Q : A -> Prop) (xs : list A) (H : forall x, P x -> Q x),
  Forall P xs -> Forall Q xs.
Proof.
  intros A P Q xs Ht HforAll.
  induction HforAll as [|y ys Hpy HfaP HfaQ].
  - constructor.
  - constructor.
    apply (Ht y Hpy).
    exact HfaQ.
Qed.

(** Evaluating a binary expression results in a series of u8 values. *)
Theorem binaryEvalPaddedBytesU8 : forall bs a (Hnz : 0 <> a),
  Forall streamEIsU8 (binaryEvalPaddedBytes bs a Hnz).
Proof.
  intros bs a Hnz.
  unfold binaryEvalPaddedBytes.
  destruct (Datatypes.length bs mod a) as [|HB].
  - rewrite Forall_map.
    induction bs as [|r rs Hrs].
    -- constructor.
    -- constructor.
       reflexivity.
       exact Hrs.
  - rewrite map_app.
    assert (Forall streamEIsU8 (map u8byte bs)) as Hmap. {
      rewrite Forall_map.
      induction bs as [|r rs Hrs].
      - constructor.
      - constructor.
        reflexivity.
        exact Hrs.
    }
    assert (Forall streamEIsU8 (map u8byte (repeat "000"%byte (a - S HB)))) as HmapR. {
      rewrite Forall_map.
      assert (Forall (eq "000"%byte) (repeat "000"%byte (a - S HB))) as Hfeq
        by (apply (repeat_eq byte (fun _ : byte => True) (a - S HB) "000"%byte)).
      simpl.
      apply (@Forall_implies byte (eq "000"%byte) (fun _ : byte => True) (repeat "000"%byte (a - S HB))). {
        intros. exact I.
      }
      exact Hfeq.
    }
    apply Forall_app.
    constructor.
    exact Hmap.
    exact HmapR.
Qed.

#[local]
Lemma app_cons : forall (A : Type) (x : A) (xs : list A),
  x :: xs = app (cons x nil) xs.
Proof.
  intros A x xs.
  reflexivity.
Qed.

(** Streams produced by the _binaryEval_ function are well-formed. *)
Theorem binaryEvalStreamsWellFormed : forall b,
  streamWellFormed (binaryEval b).
Proof.
  intros b.
  induction b as [a0|a1|a2|a3|a4|a5 Hfa|a6|a7 Hfa].
  (* U32 *)
  - apply BEPVu32.
  (* U64 *)
  - apply BEPVu64.
  (* F64 *)
  - apply BEPVf64.
  (* Bytes *)
  - unfold binaryEval.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    assert (length (binaryEvalPaddedBytes a3 4 Alignment.p0not4) mod 4 = 0) as Hlm
      by (apply (binaryEvalPaddedBytesAligned)).
    apply BEPVu8s.
    apply binaryEvalPaddedBytesU8.
    exact Hlm.
  (* UTF-8 *)
  - unfold binaryEval.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    assert (length (binaryEvalPaddedBytes a4 4 Alignment.p0not4) mod 4 = 0) as Hlm
      by (apply (binaryEvalPaddedBytesAligned)).
    assert (Forall streamEIsU8 (binaryEvalPaddedBytes a4 4 Alignment.p0not4)) as Hu8
      by (apply (binaryEvalPaddedBytesU8)).
    apply (BEPVu8s _ Hu8 Hlm).
  (* Array *)
  - simpl.
    rewrite app_cons.
    apply BEPAppend.
    apply BEPVu32.
    induction a5 as [|q qs IHqs].
    -- constructor.
    -- assert (streamWellFormed (concat (map binaryEval qs))) as HqsWF
         by (apply (IHqs (Forall_inv_tail Hfa))).
       assert (streamWellFormed (binaryEval q)) as HqWF
         by (apply (Forall_inv Hfa)).
       simpl.
       apply BEPAppend.
       exact HqWF.
       exact HqsWF.
  (* Reserve *)
  - simpl.
    unfold asMultipleOf4.
    remember (asMultipleOf a6 4 Alignment.p0not4) as size eqn:Heqsize.
    assert (size mod 4 = 0) as Heqm. {
      rewrite Heqsize.
      apply (asMultipleOfMod).
    }
    assert ((compose Vu8 Byte.to_nat) "000"%byte = (Vu8 0)) as HbyteEq by reflexivity.
    apply BEPVu8s.
    assert (Forall (eq (Vu8 0)) (repeat (Vu8 0) size)) as Hfeq
      by (apply (@repeat_eq streamE streamEIsU8 size (Vu8 0))).
    apply (@Forall_implies streamE (eq (Vu8 0)) streamEIsU8 (repeat (Vu8 0) size)). {
      intros x Hxeq.
      unfold streamEIsU8.
      rewrite <- Hxeq.
      exact I.
    }
    exact Hfeq.
    rewrite repeat_length.
    exact Heqm.
  (* Record *)
  - simpl.
    induction a7 as [|q qs IHqs].
    -- constructor.
    -- assert (Forall (fun b : binaryExp => streamWellFormed (binaryEval b)) (map snd qs)) as Hfqs. {
         apply (@Forall_inv_tail binaryExp (fun b : binaryExp => streamWellFormed (binaryEval b)) (snd q) (map snd qs)). {
           assert ((map snd (q :: qs)) = (snd q :: map snd qs)) as Hmc by reflexivity.
           rewrite <- Hmc.
           exact Hfa.
         }
       }
       assert (streamWellFormed (concat (map (compose binaryEval snd) qs))) as Hconqs by (apply (IHqs Hfqs)).
       rewrite map_cons.
       rewrite concat_cons.
       apply BEPAppend.
       rewrite map_cons in Hfa.
       apply (Forall_inv Hfa).
       exact Hconqs.
Qed.

#[local]
Lemma fold_right_1_length : forall xs,
  Forall (eq 1) xs -> fold_right add 0 xs = length xs.
Proof.
  intros xs Hfa.
  induction xs as [|y ys IHxs].
  - reflexivity.
  - rewrite <- fold_right_add_cons.
    assert (length (y :: ys) = 1 + length (ys)) as HlenYs by reflexivity.
    rewrite HlenYs.
    assert (1 = y) as Hy1 by (apply (Forall_inv Hfa)).
    rewrite <- Hy1.
    f_equal.
    apply IHxs.
    apply (Forall_inv_tail Hfa).
Qed.

#[local]
Theorem fold_right_add_app : forall xs ys,
  fold_right add 0 xs + fold_right add 0 ys = fold_right add 0 (xs ++ ys).
Proof.
  intros xs ys.
  rewrite fold_right_app.
  generalize dependent ys.
  induction xs as [|q qs IHqs].
  - reflexivity.
  - intros ys.
    simpl.
    rewrite <- (IHqs ys).
    rewrite Nat.add_assoc.
    reflexivity.
Qed.

Theorem streamSizeApp : forall xs ys,
  streamSize xs + streamSize ys = streamSize (xs ++ ys).
Proof.
  intros xs ys.
  unfold streamSize.
  rewrite map_app.
  rewrite fold_right_add_app.
  reflexivity.
Qed.

(** All well-formed streams have a size divisible by 4. *)
Theorem streamsWellFormedDivisible4 : forall es,
  streamWellFormed es -> streamSize es mod 4 = 0.
Proof.
  intros es Hwf.
  induction Hwf as [|H1|H2|H3|es Hfa Hsize|xs ys Hxswf Hxsize Hyswf Hysize].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold streamSize.
    assert (Forall (fun e => 1 = streamElementSize e) es) as HFaSize. {
      apply (@Forall_implies streamE streamEIsU8 (fun e : streamE => 1 = streamElementSize e) es). {
        intros x His.
        destruct x as [f64|u64|u32|u8].
        - contradiction.
        - contradiction.
        - contradiction.
        - reflexivity.
      }
      exact Hfa.
    }
    assert (Forall (eq 1) (map streamElementSize es)) as Hall1. {
      apply (@Forall_map _ _ _ _ es).
      exact HFaSize.
    }
    assert (fold_right add 0 (map streamElementSize es) = length es) as HlenEq. {
      assert (length es = length (map streamElementSize es)) as HmapLen. {
        rewrite length_map.
        reflexivity.
      }
      rewrite HmapLen.
      apply (fold_right_1_length (map streamElementSize es) Hall1).
    }
    rewrite HlenEq.
    exact Hsize.
  - rewrite <- streamSizeApp.
    apply divisiblityNAdd.
    discriminate.
    exact Hxsize.
    exact Hysize.
Qed.
