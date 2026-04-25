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

Require Import Stdlib.Arith.PeanoNat.

(** * Alignment *)

(** Return _size_ scaled such that it is a multiple of _q_. *)
Definition asMultipleOf (size q : nat) (Hnz : 0 <> q) : nat :=
  let r := size / q in
    match Nat.ltb_spec0 r q with
    | ReflectT _ _ => (r + 1) * q
    | ReflectF _ _ => r * q
    end.

#[local]
Lemma p0not4 : 0 <> 4.
Proof. discriminate. Qed.

#[local]
Lemma p0not16 : 0 <> 16.
Proof. discriminate. Qed.

(** Return _size_ scaled such that it is a multiple of 4. *)
Definition asMultipleOf4 (size : nat) : nat :=
  asMultipleOf size 4 p0not4.

(** Return _size_ scaled such that it is a multiple of 6. *)
Definition asMultipleOf16 (size : nat) : nat :=
  asMultipleOf size 16 p0not16.

(** If _n_ is a multiple of _m_, then _n mod m = 0_. *)
Lemma asMultipleOfMod : forall s q (Hneq : 0 <> q), (asMultipleOf s q Hneq) mod q = 0.
Proof.
  intros s q Hneq.
  unfold asMultipleOf.
  destruct (Nat.ltb_spec0 (s / q) q) as [Hlt|H1].
  - apply (Nat.Div0.mod_mul (s / q + 1) q).
  - apply (Nat.Div0.mod_mul (s / q) q).
Qed.
