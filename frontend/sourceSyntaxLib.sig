signature sourceSyntaxLib = sig
  include Abbrev

  (* Opt-in, source-only. No call to jsonASTLib or any translator/evaluator.
     Unsupported/malformed present syntax raises JSONDecode.JSONError.
     Decoding success is NOT source typing, constant evaluation or acceptance.
     Full qualifier retention requires pre-vy_ast.get_node syntax: ordinary
     Vyper JSON has already erased qualifier Calls. We never reconstruct them
     from compiler is_constant/is_immutable flags. See sourceSyntax.md. *)
  val expression : term JSONDecode.decoder
  val statement : term JSONDecode.decoder
  val declaration : term JSONDecode.decoder
  val source_module : term JSONDecode.decoder
  val annotated_ast : term JSONDecode.decoder
  val wrapped_annotated_ast : term JSONDecode.decoder

  (* Unvalidated diagnostic/resolution claims, keyed by JSON structural path.
     Never used to construct semantic source terms. In particular source_id
     and paths are NOT canonical declaration identities. Fold/type metadata
     is neither read nor retained as semantic input. *)
  type origin =
    {json_path : string list, source_id : IntInf.int option,
     node_id : IntInf.int option, src : string option,
     lineno : IntInf.int option, col_offset : IntInf.int option,
     end_lineno : IntInf.int option, end_col_offset : IntInf.int option,
     path : string option, resolved_path : string option,
     source_sha256sum : string option}
  type import_claim =
    {json_path : string list, alias : string, source_id : IntInf.int,
     qualified_module_name : string, resolved_path : string, path : string option}
  type decoded =
    {syntax : term, provenance : origin list, import_claims : import_claim list}
  val annotated_ast_with_provenance : decoded JSONDecode.decoder
end
