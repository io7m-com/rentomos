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

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.

(** If _x_ and _y_ are divisible by _z_, then _x + y_ is also divisible by _z_. *)
Theorem divisiblityNAdd : forall (x y z : nat),
  0 <> z -> x mod z = 0 -> y mod z = 0 -> (x + y) mod z = 0.
Proof.
  intros x y z Hz Hx Hy.
  destruct y as [|y].
    (* If y = 0, then this matches one of our assumptions already. *)
    rewrite Nat.add_0_r; exact Hx.
    (* Otherwise, the following property always holds given that the divisor is ≠ 0. *)
    assert ((x mod z + S y) mod z = (x + S y) mod z) as Heq.
      apply (Nat.Div0.add_mod_idemp_l x (S y) z).
    (* x mod z = 0 *)
    rewrite Hx in Heq.
    (* 0 + S y = S y *)
    rewrite Nat.add_0_l in Heq.
    rewrite <- Heq.
    exact Hy.
Qed.

(** Divisibility is preserved over addition. *)
Theorem divisibilityNFoldPlus : forall z xs,
  0 <> z ->
    Forall (fun n => n mod z = 0) xs ->
      (fold_right plus 0 xs) mod z = 0.
Proof.
  intros z xs Hnz HforAll.
  induction xs as [|y ys].
  - apply (Nat.Div0.mod_0_l z).
  - assert (fold_right add 0 (y :: ys) = y + fold_right add 0 ys) as Hfoldeq by reflexivity.
    rewrite Hfoldeq.
    assert (fold_right add 0 ys mod z = 0) as Hfoldeq2. {
      apply IHys.
      apply (@Forall_inv_tail nat (fun n : nat => n mod z = 0) y ys HforAll).
    }
    rewrite divisiblityNAdd.
    reflexivity.
    exact Hnz.
    apply (@Forall_inv nat (fun n : nat => n mod z = 0) y ys HforAll).
    exact Hfoldeq2.
Qed.
