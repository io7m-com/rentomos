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

From Stdlib Require Import Strings.Byte.
From Stdlib Require Import Lists.List.

Require Import com.io7m.entomos.Tags.
Require Import com.io7m.entomos.FileFormat.

Import ListNotations.

Example fileIdentifier : TagT :=
  Tag x89 x4d x54 x50 x0d x0a x1a x0a.

Example sectionEndIdentifier : TagT :=
  Tag x4d x54 x50 x5f x45 x4e x44 x21.

Example sectionManifestIdentifier : TagT :=
  Tag x4d x54 x50 x5f x4d x41 x4e x49.

Example sectionFileIdentifier : TagT :=
  Tag x4d x54 x50 x5f x46 x49 x4c x45.

Example sectionManifest : FileSectionDescriptionT :=
  FileSectionDescription sectionManifestIdentifier FSO_MustBeFirst FSC_One.

Example sectionFile : FileSectionDescriptionT :=
  FileSectionDescription sectionFileIdentifier FSO_AnyOrder FSC_ZeroToN.

Example fileDescriptionExample : FileDescriptionT :=
  FileDescription 
  fileIdentifier
  1 
  0 
  [sectionManifest; sectionFile] 
  sectionEndIdentifier
  UnknownSectionsPermitted
  .

Lemma fileSectionAtMostOneFirstExample : fileSectionAtMostOneFirst (fileSections fileDescriptionExample).
Proof.
  unfold fileSectionAtMostOneFirst.
  simpl; auto.
Qed.

Lemma fileSectionAtMostOneLastExample : fileSectionAtMostOneLast (fileSections fileDescriptionExample).
Proof.
  unfold fileSectionAtMostOneLast.
  simpl; auto.
Qed.

Lemma fileSectionTagsUniqueExample : fileSectionTagsUnique (fileSections fileDescriptionExample).
Proof.
  unfold fileSectionTagsUnique.
  simpl; auto.
  constructor.
  - unfold not.
    intro H.
    inversion H.
    contradict H0.
    discriminate.
    inversion H0.
  - constructor.
    unfold not.
    intro H.
    inversion H.
    constructor.
Qed.

Lemma fileSectionFileNotSectionExample : fileSectionFileNotSection fileDescriptionExample.
Proof.
  unfold fileSectionFileNotSection.
  simpl.
  unfold not.
  intro H.
  destruct H.
  - contradict H.
    discriminate.
  - destruct H.
    contradict H.
    discriminate.
    auto.
Qed.

Lemma endSectionFileNotSectionExample : endSectionFileNotSection fileDescriptionExample.
Proof.
  unfold endSectionFileNotSection.
  simpl.
  unfold not.
  intro H.
  destruct H.
  - contradict H.
    discriminate.
  - destruct H.
    contradict H.
    discriminate.
    auto.
Qed.

Theorem fileDescriptionInvariantsExample : fileDescriptionInvariants fileDescriptionExample.
Proof.
  constructor.
  apply fileSectionAtMostOneFirstExample.
  constructor.
  apply fileSectionAtMostOneLastExample.
  constructor.
  apply fileSectionTagsUniqueExample.
  constructor.
  apply fileSectionFileNotSectionExample.
  apply endSectionFileNotSectionExample.
Qed.
