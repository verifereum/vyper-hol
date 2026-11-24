Theory entryCreateConvertBytes
Ancestors
  bodyFullConvertBytesJoint bodyFullConvertCastOrigin exprSimConvertBytes
  entryCreateAdminSequence entryCreateScopedBind entryCreateScopedForce
  entryCreateNativeFirstExit entryCreateRegionLift entryCreatePendingScope
  entryCreateIntervalLayout entryCreatePathScope entryCreateCompletedCut
  entryCreateFocusSpec entryCreateCompositeFocus createSizeCutCode createSizeCutRegion
  fragGasOriginPtr fragGasOrigin fragGasSeqAbort fragExec instIdxIndep
  exprLoweringProps abiBufferAllocationCode gasEvents venomInstProps venomInst
  createSizePrefixReplay createMarkedPath
  venomExecSemantics venomState list rich_list arithmetic
  exprLowering compileEnv abiEncoderProps context emitHelper
  bodyPtrTypeBuiltinsMemoryInterface bodyPtrTypeBuiltinsMemoryBounds

Theorem convert_straight_origin_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
  gas_origin_edge T E C fn s marks r ==>
  marks = [] /\ (~s.vs_halted) /\
  ((?u. step_inst_base i s = OK u /\ ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
        r = OK (u with vs_inst_idx := SUC s.vs_inst_idx)) \/
   (exit_result (step_inst_base i s) /\ r = step_inst_base i s))
Proof
  simp[gas_origin_edge_def] >> strip_tac >>
  gvs[step_inst_non_invoke, gas_events_step_def] >>
  metis_tac[step_preserves_control_flow, step_inst_non_invoke]
QED

(* Consume only the installed code preceding the abort. The path gives the
   memory-checked final edge; the sequence run rules out an earlier exit PC. *)
Theorem convert_abort_scope_from_code[local]:
  !code s bb raw u marks.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort Revert_abort raw /\
    gas_origin_path T E C fn s marks (Abort Revert_abort u) ==>
    create_operand_full_scope a b E C fn s marks (Abort Revert_abort u)
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by (fs[] >> decide_tac) >>
  qpat_x_assum `gas_origin_path T _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_origin_path_cases]) >> gvs[]
  >- suspend "step" >> suspend "terminal"
QED

Resume convert_abort_scope_from_code[step]:
  drule_all convert_straight_origin_edge >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
       gvs[exit_result_def]) >>
  rename1 `step_inst_base h s = OK z` >>
  qabbrev_tac `t = z with vs_inst_idx := SUC s.vs_inst_idx` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `run_inst_seq code t = Abort Revert_abort (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    fs[Abbr `t`, run_inst_seq_def, run_inst_seq_inst_idx, exec_result_map_def] >>
  `create_operand_full_scope a b E C fn t right (Abort Revert_abort u)` by
    (qpat_x_assum `!s bb raw u marks. _` irule >>
     simp[Abbr `t`, ADD_CLAUSES] >> metis_tac[]) >>
  `gas_origin_edge F E C fn s [] (OK t)` by
    (qpat_assum `gas_origin_edge T E C fn s [] (OK t)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [gas_origin_edge_def] >> metis_tac[]) >>
  `create_expr_prefix a b E C fn s [] t` by
    (simp[create_expr_prefix_marked] >> irule relationTheory.RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  qpat_x_assum `create_operand_full_scope a b E C fn t _ _` mp_tac >>
  simp[create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

Resume convert_abort_scope_from_code[terminal]:
  simp[create_operand_full_scope_def] >>
  qexistsl_tac [`[]`,`s`,`marks`] >> simp[create_expr_prefix_marked]
QED

Finalise convert_abort_scope_from_code

Definition convert_admin_slice_def:
  convert_admin_slice a b <=>
    b.cs_current_bb = a.cs_current_bb /\ b.cs_blocks = a.cs_blocks /\
    a.cs_next_id <= b.cs_next_id /\
    b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (emitted_insts a b)
End

Theorem convert_bytes_cast_slice[local]:
  compile_type_convert x (ConvBytestringCast n i) a = (out,b) ==>
  convert_admin_slice a b
Proof
  Cases_on `n < i` >>
  simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[convert_admin_slice_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem convert_bytes_widen_slice[local]:
  compile_bytestring_widen_copy d x k a = (out,b) ==>
  convert_admin_slice a b
Proof
  Cases_on `k` >>
  simp[compile_bytestring_widen_copy_def, contextTheory.compile_copy_memory_def,
       contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[convert_admin_slice_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem convert_bytes_slice[local]:
  is_bytestring_type ann /\ is_bytestring_type (expr_type e) /\
  valid_conversion (expr_type e) ann /\
  (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce ann then
     compile_bytestring_widen_copy (type_memory_bytes ce ann) x
       (type_memory_bytes ce (lowered_value_type ce e)) a
   else compile_type_convert x (mk_convert_op (expr_type e) ann) a) = (out,b) ==>
  convert_admin_slice a b
Proof
  strip_tac >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce ann`
  >- (fs[] >> metis_tac[convert_bytes_widen_slice]) >>
  gvs[] >>
  mp_tac (Q.SPECL [`expr_type e`,`ann`] memory_convert_shapes) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `i` (qx_choose_then `n` assume_tac)) >>
  metis_tac[convert_bytes_cast_slice]
QED

Theorem convert_slice_cut_code[local]:
  cs_extends a b /\ convert_admin_slice a b ==> create_cut_code {} a b
Proof
  simp[convert_admin_slice_def, create_cut_code_def,
       exprSimAbiGasBridgeTheory.frag_code_same_blocks, emitted_insts_def,
       EVERY_MEM] >>
  rpt strip_tac >> res_tac >>
  Cases_on `i.inst_opcode` >> gvs[create_cut_targets_def, is_terminator_def]
QED

Theorem convert_slice_abort_scope[local]:
  convert_admin_slice a b /\ fn_has_code a b f /\ create_operand_at a t /\
  run_inst_seq (emitted_insts a b) t = Abort Revert_abort raw /\
  gas_origin_path T E ctx f t [] (Abort Revert_abort u) ==>
  create_operand_full_scope a b E ctx f t [] (Abort Revert_abort u)
Proof
  strip_tac >> fs[convert_admin_slice_def, create_operand_at_def] >>
  qpat_x_assum `fn_has_code a b f` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  irule convert_abort_scope_from_code >> simp[] >>
  qexistsl_tac [`bb`,`emitted_insts a b`,`raw`] >> gvs[] >>
  conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then drule >> simp[]) >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_APPEND]
QED

Theorem convert_vv_post_scope[local]:
  is_bytestring_type ann /\
  convert_bytes_vv_post (DF,lo,d,ctx,f) ce cx ann e
    (es,a,b,s,out,G,tn) H res ee G1 tn1 t ==>
  create_operand_vv_post (DF,lo,d,ctx,f) ce cx (TypeBuiltin ann Convert ann [e])
    (es,a,b,s,LocatedValue ann (mk_ptr out LocMemory),G,tn) H res ee G1 tn1 t /\
  create_operand_at b t
Proof
  simp[convert_bytes_vv_post_def, create_operand_vv_post_def,
       bodyFullEmptyLeafDataTheory.expr_vv_sim_full_post_def,
       exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def,
       create_operand_at_def, loweringPostsTheory.post_value_type_def,
       vyperASTTheory.expr_type_def, mk_ptr_def, vv_location_def] >>
  rpt strip_tac >> simp[] >> first_assum (irule_at Any) >> simp[]
QED

Theorem convert_suffix_scoped[local]:
  is_bytestring_type ann /\ convert_admin_slice m b /\ fn_has_code m b f /\
  create_operand_at m t /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  convert_bytes_vv_suffix (DF,lo,d,ctx,f,E,PG) ce cx ann e st0
    (es,a,m,b,s,out,G,tn) (v,mid,t,G1,tn1) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 m b
    (\ee. (sum_CASE (convert_result cx (expr_type e) ann v) (\w. INL (Value w)) INR, ee))
    (mid,t,G1,tn1)
    (\H res ee G' tn' u. create_operand_vv_post (DF,lo,d,ctx,f) ce cx
      (TypeBuiltin ann Convert ann [e]) (es,a,b,s,LocatedValue ann (mk_ptr out LocMemory),G,tn)
      H res ee G' tn' u /\ create_operand_at b u)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  qpat_x_assum `convert_bytes_vv_suffix _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [convert_bytes_vv_suffix_def]) >> gvs[]
  >- suspend "normal" >> suspend "abort"
QED

Resume convert_suffix_scoped[normal]:
  `create_operand_full_scope m b E ctx f t []
     (OK (raw with vs_inst_idx := LENGTH b.cs_current_insts))` by
    (irule create_admin_sequence_scope >> fs[convert_admin_slice_def, EVERY_MEM]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  qexistsl_tac [`sum_CASE (convert_result cx (expr_type e) ann v) (\w. INL (Value w)) INR`,
                `mid`,`G2`,`tn2`] >>
  simp[gasSummaryTheory.gas_explicit_def] >> rpt strip_tac >> res_tac >>
  `mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[exit_result_def] >> drule_all convert_vv_post_scope >> simp[]
QED

Resume convert_suffix_scoped[abort]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `gas_origin_path T E ctx f t [] (Abort Revert_abort u)` by
    metis_tac[gas_origin_ptr_path_projections] >>
  drule_all convert_slice_abort_scope >> strip_tac >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`mid`,`G2`,`tn2`] >>
  simp[gasSummaryTheory.gas_explicit_def, create_operand_exit_post_def, exit_result_def,
       exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]
QED

Finalise convert_suffix_scoped
