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
     occurrences may carry different legacy types/dispatch claims.
     Program claims resolve inferred struct/flag types against all paired
     top-level declarations, including imports, using jsonNominalSources.
     With no imported nominal declarations, import identity validation is
     skipped; main-only nominal declarations still repair main claims.
     Otherwise, import source IDs shared across distinct known resolved_paths
     use the inherited HOL build_module_identity_map/lookup_module_identity policy.
     Every import participates, including those with no nominal declarations.
     In this collision mode ALL imports must have source_id and resolved_path,
     and every resolved_path must be unique; repeated paths raise JSONError
     even for identical aliases. This is fail-closed: the inherited frontend
     deduplicates full legacy bodies before allocating IDs, which this source
     route deliberately does not decode or approximate. With no cross-path
     collision the existing raw-ID policy is unchanged, including repeated
     aliases and synthetic imports lacking resolved_path.
     Ambiguous names and explicit type origins are retained unchanged;
     pair_expression alone has no program declaration context. *)
  val pair_program : sourceModuleLoaderLib.loaded -> JSON.value -> JSON.value -> paired
end
