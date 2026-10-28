signature sourceOrdinaryClaimsLib = sig
  include Abbrev
  (* No fallback decoder: malformed/mismatched syntax raises JSONError.
     Folds are deleted recursively BEFORE either annotated decoder is called. *)
  val without_folds : JSON.value -> JSON.value
  type expression_pair =
    {claims:term, projection:thm, shape:thm, source_match:thm}
  val pair_expression : JSON.value -> JSON.value -> expression_pair

  type paired =
    {original:sourceModuleLoaderLib.loaded, annotated:JSON.value, claims:term, retained:term,
     projection:thm, shape:thm, source_match:thm,
     origins:sourceSyntaxLib.origin list,
     import_claims:sourceSyntaxLib.import_claim list}
  (* original_json and annotated are UNWRAPPED {ast,imports} objects.
     original_json must decode to #program original. The loader's policies,
     canonical keys and provenance are retained unchanged and revalidated.
     annotated retains the fold-free compiler tree for explicitly inherited
     declaration/signature claims; it is NOT replacement source syntax.
     Only original VariableDecl annotation qualifiers may be erased by the
     compiler. Source projection keeps those ORIGINAL wrappers, never flags.
     Program root paths use source-field ordinal/array-index steps; nested
     expression paths use source_claims_at, hence equal syntax at different
     occurrences may carry different legacy types/dispatch claims. *)
  val pair_program : sourceModuleLoaderLib.loaded -> JSON.value -> JSON.value -> paired
end
