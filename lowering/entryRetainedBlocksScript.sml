(* Literal pre-internal prefixes survive successful entry extraction. *)
Theory entryRetainedBlocks
Ancestors
  entryInternalAppend entryPrefixRetention entryRawFunction moduleLowering
  compileEnv list

Theorem internal_compilation_all_blocks_prefix:
  compile_internal_fn_bodies ints se = (r,sz) ==>
  ?tail. all_blocks sz = all_blocks se ++ tail
Proof
  Cases_on `ints = []`
  >- simp[compile_internal_fn_bodies_def, comp_return_def] >>
  Cases_on `r` >> metis_tac[internal_fn_bodies_retains_prefix]
QED

Theorem extracted_entry_retains_prefix:
  all_blocks sf = pre ++ tail /\
  (!d. MEM d (internal_fn_descriptors ints) ==>
    ~MEM (FST d) (MAP (\bb. bb.bb_label) pre)) /\
  package_internal_blocks (internal_fn_descriptors ints) (all_blocks sf) =
    SOME (eb,fs) /\
  extract_context_with_internals entry ints sf = SOME (ctx,data) /\
  lookup_function entry ctx.ctx_functions = SOME efn ==>
  !bb. MEM bb pre ==> MEM bb efn.fn_blocks
Proof
  strip_tac >> drule_all extracted_entry_blocks >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  irule package_internal_blocks_prefix_mem >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
