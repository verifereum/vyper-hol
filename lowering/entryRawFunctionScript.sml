Theory entryRawFunction
Ancestors
  vyperCompiler loweringShapeDefs venomExecSemantics venomInst list

Theorem extracted_entry_raw_function:
  extract_context_with_internals entry internal_fns sf = SOME (ctx,data) /\
  package_internal_blocks (internal_fn_descriptors internal_fns) (all_blocks sf) =
    SOME (eb,fs) /\
  lookup_function entry ctx.ctx_functions = SOME efn ==>
  efn = mk_raw_function entry eb
Proof
  simp[extract_context_with_internals_def, GSYM all_blocks_def] >>
  strip_tac >> gvs[mk_venom_context_def, lookup_function_def,
                  mk_raw_function_def, FIND_thm]
QED

Theorem extracted_entry_blocks:
  extract_context_with_internals entry internal_fns sf = SOME (ctx,data) /\
  package_internal_blocks (internal_fn_descriptors internal_fns) (all_blocks sf) =
    SOME (eb,fs) /\
  lookup_function entry ctx.ctx_functions = SOME efn ==>
  efn.fn_blocks = eb
Proof
  strip_tac >> drule_all extracted_entry_raw_function >>
  simp[mk_raw_function_def]
QED
