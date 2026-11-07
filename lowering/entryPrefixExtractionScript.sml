(* Entry packaging needs only the first internal delimiter. *)
Theory entryPrefixExtraction
Ancestors
  vyperCompiler loweringShapeDefs compileEnv context venomInst list

Theorem package_internal_blocks_first_delimiter:
  ~MEM name (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = name /\
  package_internal_blocks ((name,h,r)::ds) (prefix ++ bb::suffix) =
    SOME (entry,fs) ==>
  entry = prefix
Proof
  strip_tac >>
  `split_blocks_at name (prefix ++ bb::suffix) = SOME (prefix,bb::suffix)` by
    (irule split_blocks_at_append_delimiter >> simp[]) >>
  gvs[package_internal_blocks_def, AllCaseEqs()]
QED

Theorem extracted_entry_packaged_blocks:
  package_internal_blocks (internal_fn_descriptors internal_fns)
    (all_blocks st) = SOME (prefix,fs) /\
  extract_context_with_internals "__entry" internal_fns st = SOME (ctx,data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn ==>
  efn.fn_blocks = prefix
Proof
  strip_tac >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  simp_tac bool_ss [extract_context_with_internals_def, LET_THM] >>
  rewrite_tac[GSYM all_blocks_def] >> asm_rewrite_tac[] >>
  simp[mk_venom_context_def, lookup_function_def, FIND_thm,
       mk_raw_function_def] >> strip_tac >>
  gvs[lookup_function_def, FIND_thm, mk_raw_function_def]
QED

Theorem extracted_entry_first_delimiter_blocks:
  internal_fn_descriptors internal_fns = (name,h,r)::ds /\
  all_blocks st = prefix ++ bb::suffix /\
  ~MEM name (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = name /\
  extract_context_with_internals "__entry" internal_fns st = SOME (ctx,data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn ==>
  efn.fn_blocks = prefix
Proof
  strip_tac >>
  `?entry fs. package_internal_blocks (internal_fn_descriptors internal_fns)
      (all_blocks st) = SOME (entry,fs)` by
    (qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
     simp_tac bool_ss [extract_context_with_internals_def, LET_THM] >>
     rewrite_tac[GSYM all_blocks_def] >>
     Cases_on `package_internal_blocks (internal_fn_descriptors internal_fns)
                   (all_blocks st)` >> simp[] >> PairCases_on `x` >> simp[]) >>
  `entry = prefix` by (irule package_internal_blocks_first_delimiter >>
    metis_tac[]) >>
  irule extracted_entry_packaged_blocks >> metis_tac[]
QED

Theorem extracted_entry_no_internal_blocks:
  internal_fn_descriptors internal_fns = [] /\
  extract_context_with_internals "__entry" internal_fns st = SOME (ctx,data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn ==>
  efn.fn_blocks = all_blocks st
Proof
  strip_tac >> irule extracted_entry_packaged_blocks >>
  qexistsl [`ctx`, `data`, `[]`, `internal_fns`, `st`] >>
  simp[package_internal_blocks_def]
QED
