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

From Stdlib Require Import Lists.List.

Require Import com.io7m.entomos.Tags.

Import ListNotations.

(** The ordering constraints on a file section. *)
Inductive FileSectionOrderingT :=
    (** The section must be the first in the file. *)
    FSO_MustBeFirst
  | (** The section must be the last in the file. *)
    FSO_MustBeLast
  | (** The section can appear anywhere in the file. *)
    FSO_AnyOrder
  .

(** The cardinality of a file section. *)
Inductive FileSectionCardinalityT :=
    (** The section must appear exactly once. *)
    FSC_One
  | (** The section can appear at most once. *)
    FSC_ZeroToOne
  | (** The section can appear any number of times, including not at all. *)
    FSC_ZeroToN
  | (** The section must appear at least once. *)
    FSC_OneToN
  .

(** The constraints on unknown sections. *)
Inductive FileSectionsUnknownT :=
  | (** Unknown sections are permitted. *)
    UnknownSectionsPermitted
  | (** Unknown sections are not permitted. *)
    UnknownSectionsNotPermitted
  .

(** A description of a file section. *)
Inductive FileSectionDescriptionT := FileSectionDescription {
  (** The file section tag. *)
  fileSectionTag         : TagT;
  (** The file section ordering constraint. *)
  fileSectionOrdering    : FileSectionOrderingT;
  (** The file section cardinality constraint. *)
  fileSectionCardinality : FileSectionCardinalityT
}.

(** The description of a file format version. *)
Inductive FileDescriptionT := FileDescription {
  (** The file tag. *)
  fileTag             : TagT;
  (** The major file format version. *)
  fileVersionMajor    : nat;
  (** The minor file format version. *)
  fileVersionMinor    : nat;
  (** The file sections. *)
  fileSections        : list FileSectionDescriptionT;
  (** The file end tag. *)
  fileEndTag          : TagT;
  (** The constraints on unknown file sections. *)
  fileSectionsUnknown : FileSectionsUnknownT
}.

(** The number of sections with _FSO_MustBeFirst_. *)
Fixpoint fileSectionOrderingCountFirst
  (xs : list FileSectionDescriptionT)
  (n  : nat)
: nat :=
  match xs with
  | nil       => 0
  | cons y ys =>
    match (fileSectionOrdering y) with
    | FSO_MustBeFirst => fileSectionOrderingCountFirst ys (S n)
    | _               => fileSectionOrderingCountFirst ys n
    end
  end.

(** The number of sections with _FSO_MustBeLast_. *)
Fixpoint fileSectionOrderingCountLast
  (xs : list FileSectionDescriptionT)
  (n  : nat)
: nat :=
  match xs with
  | nil       => 0
  | cons y ys =>
    match (fileSectionOrdering y) with
    | FSO_MustBeLast => fileSectionOrderingCountLast ys (S n)
    | _              => fileSectionOrderingCountLast ys n
    end
  end.

(** At most one section can be _FSO_MustBeFirst_. *)
Definition fileSectionAtMostOneFirst (xs : list FileSectionDescriptionT) : Prop :=
  fileSectionOrderingCountFirst xs 0 <= 1.

(** At most one section can be _FSO_MustBeLast_. *)
Definition fileSectionAtMostOneLast (xs : list FileSectionDescriptionT) : Prop :=
  fileSectionOrderingCountLast xs 0 <= 1.

(** The file sections must have unique tags. *)
Definition fileSectionTagsUnique (xs : list FileSectionDescriptionT) : Prop :=
  NoDup (map (fun s => fileSectionTag s) xs).

(** The file sections cannot contain the file tag. *)
Definition fileSectionFileNotSection (f : FileDescriptionT) : Prop :=
  ~In (fileTag f) (map (fun s => fileSectionTag s) (fileSections f)).

(** The file sections cannot contain the end tag. *)
Definition endSectionFileNotSection (f : FileDescriptionT) : Prop :=
  ~In (fileEndTag f) (map (fun s => fileSectionTag s) (fileSections f)).

(** The file format description invariants. *)
Definition fileDescriptionInvariants (f : FileDescriptionT) : Prop :=
     fileSectionAtMostOneFirst (fileSections f)
  /\ fileSectionAtMostOneLast (fileSections f)
  /\ fileSectionTagsUnique (fileSections f)
  /\ fileSectionFileNotSection f
  /\ endSectionFileNotSection  f.

