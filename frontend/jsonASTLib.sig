(* Public JSON decoders for importing compiler artifacts into jsonAST. *)

signature jsonASTLib = sig
  include Abbrev

  val annotated_ast : term JSONDecode.decoder
  val wrapped_annotated_ast : term JSONDecode.decoder
  val storage_layout : term JSONDecode.decoder
end
