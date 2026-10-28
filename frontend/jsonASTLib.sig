(* Public JSON decoders for importing compiler artifacts into jsonAST. *)

signature jsonASTLib = sig
  include Abbrev

  (* Per-node legacy claims for the source/annotated zipper. Callers must
     remove folded metadata before using these on the ordinary source path. *)
  val json_expr : term JSONDecode.decoder
  val json_type : term JSONDecode.decoder
  val annotated_ast : term JSONDecode.decoder
  val wrapped_annotated_ast : term JSONDecode.decoder
  val storage_layout : term JSONDecode.decoder
end
