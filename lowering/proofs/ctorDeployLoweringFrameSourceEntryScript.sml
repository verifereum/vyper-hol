(* Structural source-entry facts; opcode production remains a separate obligation. *)
Theory ctorDeployLoweringFrameSourceEntry
Ancestors
  deployUnitProducers vyperCompiler venomInst list

Theorem deploy_lowering_entry_and_names:
  lower_vyper_deploy_unit tops rp bytes = SOME u ==>
  u.cu_context.ctx_entry = SOME "__deploy" /\
  ALL_DISTINCT (MAP (\f. f.fn_name) u.cu_context.ctx_functions) /\
  ?fn. lookup_function "__deploy" u.cu_context.ctx_functions = SOME fn
Proof
  strip_tac >> drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def, ctx_fn_names_def]
QED

Theorem package_internal_blocks_entry_prefix:
  !name has_ret_buf ret_count rest prefix bb suffix entry_blocks functions.
  ~MEM name (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = name /\
  package_internal_blocks ((name, has_ret_buf, ret_count)::rest)
    (prefix ++ bb::suffix) = SOME (entry_blocks, functions) ==>
  entry_blocks = prefix
Proof
  rpt strip_tac >> drule_all split_blocks_at_append_delimiter >> strip_tac >>
  gvs[Once package_internal_blocks_def, AllCaseEqs()]
QED

Theorem extract_context_entry_prefix:
  internal_fn_descriptors internal_fns = (name, has_ret_buf, ret_count)::rest /\
  REVERSE st.cs_blocks ++
    [<| bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts |>] =
      prefix ++ bb::suffix /\
  ~MEM name (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = name /\
  extract_context_with_internals entry_label internal_fns st = SOME (ctx,data) ==>
  ?f fs. ctx.ctx_functions = f::fs /\ f.fn_name = entry_label /\ f.fn_blocks = prefix
Proof
  rpt strip_tac >> gvs[extract_context_with_internals_def, AllCaseEqs()] >>
  `entry_blocks = prefix` by
    (irule package_internal_blocks_entry_prefix >>
     qexists `bb` >> simp[] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  gvs[mk_venom_context_def, mk_raw_function_def]
QED

Theorem extract_context_no_internal_entry_blocks:
  internal_fn_descriptors internal_fns = [] /\
  extract_context_with_internals entry_label internal_fns st = SOME (ctx,data) ==>
  ?f fs. ctx.ctx_functions = f::fs /\ f.fn_name = entry_label /\
    f.fn_blocks = REVERSE st.cs_blocks ++
      [<| bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts |>]
Proof
  rpt strip_tac >>
  gvs[extract_context_with_internals_def, package_internal_blocks_def,
      mk_venom_context_def, mk_raw_function_def]
QED
