signature jsonConstASTLib = sig
  include Abbrev

  (* Strict integer-constant frontend: source annotations and expressions only.
     Unsupported syntax raises JSONDecode.JSONError. *)
  val annotated_ast : term JSONDecode.decoder
end
