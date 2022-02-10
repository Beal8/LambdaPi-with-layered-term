(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)

include Signatures.OPTIONS with type command_spec = Command.spec

(* This option is not in Signatures.OPTIONS yet because adding tags to
   the compilation of the plugin is a recent feature that may still be
   subject to change, so the interface may not be stable; besides,
   there is obviously little to gain from tweaking that option from
   inside the plugin itself... *)
val plugin_tags : string list ref

(* Returns 'true' if we heuristically infer that we are run from an
   ocamlbuild projet (either _tags or myocamlbuild.ml are present).

   This information is used to decide whether to enable recursive
   traversal of subdirectories by default.
*)
val ocamlbuild_project_heuristic : unit -> bool

val spec : unit -> (Arg.key * Arg.spec * Arg.doc) list

val entry : bool Slurp.entry option ref
val init : unit -> unit
