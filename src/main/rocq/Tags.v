(*
 * Copyright © 2026 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Strings.Byte.

(** A 64-bit section identifier. *)
Inductive TagT : Set := Tag {
  tag_byte0 : byte;
  tag_byte1 : byte;
  tag_byte2 : byte;
  tag_byte3 : byte;
  tag_byte4 : byte;
  tag_byte5 : byte;
  tag_byte6 : byte;
  tag_byte7 : byte
}.

(** The example PNG file format identifier. *)
Example tagPNG :=
  Tag x89 x50 x4e x47 x0d x0a x1a x0a.

