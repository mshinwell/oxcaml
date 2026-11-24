(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Format_doc], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

Module Doc.
  (* format_doc.mli:68  type t *)
  Parameter t : Type.
  Extract Inlined Constant t => "Format_doc.Doc.t".
End Doc.
(* format_doc.mli:161  type doc = Doc.t *)
Definition doc : Type := Format_doc.Doc.t.
Extract Inlined Constant doc => "Format_doc.doc".
(* format_doc.mli:162  type t = doc *)
Definition t : Type := doc.
Extract Inlined Constant t => "Format_doc.t".
