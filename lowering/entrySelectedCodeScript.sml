(* Compile-only witnesses for a selected external body in __entry. *)
Theory entrySelectedCode
Ancestors
  entryCodeContainment entryRuntimePrefix allocaFrontierBound
  loweringShapeDefs loweringShapeProps vyperCompiler compileEnv venomInst
  list moduleLowering venomWf removeUnusedSsaProofs

Theorem entry_prefix_label_shape[local]:
  shape_extends F jump_label_ok (initial_compile_state "__entry") st ==>
  all_blocks st <> [] /\ (HD (all_blocks st)).bb_label = "__entry" /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks st)))
Proof
  simp[shape_extends_def] >> strip_tac >>
  `MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
     ["__entry"]` by simp[initial_compile_state_def, all_blocks_def] >>
  drule block_labels_cs_extends >> asm_rewrite_tac[] >> strip_tac >>
  Cases_on `all_blocks st` >> gvs[]
QED

Theorem run_lowering_selected_body_code:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  MEM (lbl, ce, args, cds, pay, nr, key, trans, view, fbody, rt) external_fns /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn ==>
  ?sd selected_ce sa se.
    compile_register_positional_args ce args 4 sd = (selected_ce, sa) /\
    compile_guarded_body selected_ce nr key trans view fbody rt sa = ((), se) /\
    fn_has_code sa se efn /\ fn_inst_ids_distinct efn
Proof
  strip_tac >>
  drule run_lowering_static_integrity >> strip_tac >>
  `fn_inst_ids_distinct efn` by
    (drule lookup_function_MEM >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
          MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, AllCaseEqs()] >> pairarg_tac >>
  rename1 `_ = (result, st1)` >> Cases_on `result` >>
  simp[] >> strip_tac >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `?data. extract_context_with_internals "__entry" internal_fns st1 =
      SOME (unit.cu_context, data) /\ lowering_context_ok unit.cu_context` by
    (Cases_on `extract_context_with_internals "__entry" internal_fns st1` >>
     gvs[AllCaseEqs()]) >>
  mp_tac (Q.SPEC `"__entry"` shape_state_initial_compile_state) >> strip_tac >>
  drule_all runtime_selected_body_states >> strip_tac >>
  drule entry_prefix_label_shape >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) efn.fn_blocks)` by
    (qpat_x_assum `lowering_context_ok unit.cu_context` mp_tac >>
     simp[lowering_context_ok_def, EVERY_MEM] >> strip_tac >>
     drule lookup_function_MEM >> strip_tac >>
     qpat_x_assum `!fn. MEM fn unit.cu_context.ctx_functions ==> _` drule >>
     simp[fn_labels_def]) >>
  drule_all extracted_entry_body_has_code >> strip_tac >>
  metis_tac[]
QED
