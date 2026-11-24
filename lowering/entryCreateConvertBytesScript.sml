Theory entryCreateConvertBytes
Ancestors
  bodyFullConvertBytesJoint bodyFullConvertCastOrigin exprSimConvertBytes
  entryCreateAdminSequence entryCreateScopedBind entryCreateScopedForce entryCreateBodyCut
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

Theorem convert_bytes_site_split[local]:
  is_bytestring_type ann /\ is_bytestring_type (expr_type e) /\ ~is_word_type ann /\
  compile_expr ce ty (TypeBuiltin ann Convert ann [e]) a = (vv,b) ==>
  ?x m out. lower_value compile_expr ce (expr_type e) e a = (x,m) /\
    (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce ann
       then compile_bytestring_widen_copy (type_memory_bytes ce ann) x
         (type_memory_bytes ce (lowered_value_type ce e)) m
       else compile_type_convert x (mk_convert_op (expr_type e) ann) m) = (out,b) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\ cs_extends m b
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr ce (expr_type e) e a` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, vyperASTTheory.expr_type_def] >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce ann` >>
  strip_tac >> gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  rename1 `lower_value _ _ _ _ _ = (x,m)`
  >- (qspecl_then [`type_memory_bytes ce ann`,`x`,
                     `type_memory_bytes ce (lowered_value_type ce e)`,`m`]
        mp_tac externalEntryShapeTheory.compile_bytestring_widen_copy_labels >> simp[]) >>
  qspecl_then [`x`,`mk_convert_op (expr_type e) ann`,`m`,`\_. T`]
    mp_tac externalEntryShapeTheory.compile_type_convert_labels >> simp[]
QED

Theorem convert_bytes_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  cs_extends m b /\ convert_admin_slice m b /\ fn_has_code m b f /\
  create_operand_cut a m E ctx f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
  create_operand_cut a b E ctx f tops cx st0
    (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s)
Proof
  strip_tac >> drule_all convert_slice_cut_code >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (simp[eval_expr_convert_vv_action] >> irule create_cut_bind_left >>
      fs[create_operand_cut_def, vyperStorageTraceTheory.storage_trace_frame_def] >> metis_tac[]) >>
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut m b E ctx f tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >>
     fs[convert_admin_slice_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `create_operand_cut m b _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED

Theorem convert_bytes_scope_geometry[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  cs_extends a m /\ cs_extends m b /\ create_layout a b /\ create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
     create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
     create_operand_full_scope a b E ctx f s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx f s left (OK t) /\
     create_operand_focus_scope m b E ctx f t right ==>
     create_operand_focus_scope a b E ctx f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx f s left (OK t) /\
     create_operand_full_scope m b E ctx f t right r ==>
     create_operand_full_scope a b E ctx f s (left ++ right) r)
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  `a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  `!left t. create_expr_prefix a m E ctx f s left t ==>
            create_expr_prefix a b E ctx f s left t` by
    (rpt strip_tac >> irule create_left_prefix_lift_at >> metis_tac[]) >>
  `!p marks q. create_prefix_step m b E ctx f p marks q ==>
               create_prefix_step a b E ctx f p marks q` by
    (simp[create_prefix_step_def, frag_ids_def] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- (rpt strip_tac >> irule create_left_focus_lift_at >> metis_tac[])
  >- (rpt strip_tac >> irule create_left_terminal_lift_at >> metis_tac[])
  >- (simp[create_operand_full_scope_def] >> rpt strip_tac >>
      irule create_operand_focus_scope_prepend >> qexists_tac `t` >> simp[] >>
      irule create_operand_focus_scope_lift >>
      `create_cut_region m b t` by metis_tac[cj 1 create_cut_region_rules] >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  Cases_on `r` >> simp[create_operand_full_scope_def] >> rpt strip_tac >>
  metis_tac[create_expr_prefix_mono, create_expr_prefix_append, APPEND_ASSOC]
QED

Theorem convert_bytes_child_post[local]:
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P
    (create_operand_exit_post ctx cx) /\
  (!H res ee G1 tn1 t. P H res ee G1 tn1 t ==> ?v. res = INL v) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?v. res = INL v /\ P H (INL v) ee G1 tn1 t /\
                              ee.gas_obs = [] /\ ~t.vs_halted /\ create_operand_at m t)
    (\H res ee gt r. ?ex. res = INR ex /\
      create_operand_exit_post ctx cx H (INR ex : eval_result + vyperState$exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[]
      >- (`~t.vs_halted` by metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase,
                                    fragGasPathTheory.gas_path_normal] >>
          fs[create_operand_full_scope_def, create_operand_at_def] >> metis_tac[]) >>
      Cases_on `res` >>
      fs[create_operand_exit_post_def, exprSimDefsTheory.expr_exit_def,
         exprSimDefsTheory.halt_exit_def, stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem convert_bytes_scoped_bind[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  cs_extends a m /\ cs_extends m b /\ create_layout a b /\ create_operand_at a s /\
  is_bytestring_type ann /\ convert_admin_slice m b /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (create_force_read_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,x,G,tn))
    (create_operand_exit_post ctx cx) /\
  (!left v mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       create_force_read_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,x,G,tn)
         H (INL v : value + vyperState$exception) mid G1 tn1 t) ==>
    convert_bytes_vv_suffix (DF,lo,d,ctx,f,E,PG) ce cx ann e st0
      (es,a,m,b,s,out,G,tn) (v,mid,t,G1,tn1)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s,G,tn)
    (\H res ee G' tn' u. create_operand_vv_post (DF,lo,d,ctx,f) ce cx
      (TypeBuiltin ann Convert ann [e]) (es,a,b,s,LocatedValue ann (mk_ptr out LocMemory),G,tn)
      H res ee G' tn' u /\ create_operand_at b u)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> drule_all convert_bytes_scope_geometry >>
  disch_then (qspec_then `E` strip_assume_tac) >>
  pure_rewrite_tac[eval_expr_convert_vv_action] >>
  irule scoped_operand_bind >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_def] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
      once_rewrite_tac[vyperStateTheory.bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[GSYM vyperStateTheory.ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
      once_rewrite_tac[vyperStateTheory.bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      simp[GSYM vyperStateTheory.ignore_bind_def]) >>
  qexistsl_tac [`\H v ee G1 tn1 t.
    create_force_read_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,x,G,tn)
      H (INL v : value + vyperState$exception) ee G1 tn1 t /\
      ee.gas_obs = [] /\ ~t.vs_halted /\ create_operand_at m t`, `m`] >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "suffix" >> suspend "child"
QED

Resume convert_bytes_scoped_bind[child]:
  drule convert_bytes_child_post >>
  (impl_tac >- (simp[create_force_read_post_def,
                    exprSimFullBundlePropsTheory.expr_sim_full_post_def] >> metis_tac[])) >>
  simp[]
QED

Resume convert_bytes_scoped_bind[suffix]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  irule convert_suffix_scoped >> simp[] >> conj_tac
  >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (qexists_tac `left` >> simp[]) >>
  metis_tac[]
QED

Finalise convert_bytes_scoped_bind

(* Split the actual and shadow compilation at the same operand. *)
Theorem convert_bytes_child_site[local]:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert ann [e]) es (st0,a,b,sha,shb,vv,s,G,tn) /\
  expr_body_pre ce cx env e es /\
  is_bytestring_type ann /\ is_bytestring_type (expr_type e) /\ ~is_word_type ann ==>
  ?m shm x out.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,x,s,G,tn) /\
    (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce ann
       then compile_bytestring_widen_copy (type_memory_bytes ce ann) x
         (type_memory_bytes ce (lowered_value_type ce e)) m
       else compile_type_convert x (mk_convert_op (expr_type e) ann) m) = (out,b) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    cs_extends a m /\ cs_extends m b /\ fn_has_code m b f
Proof
  simp[s1PrefixDefsTheory.expr_vv_sim_full_pre_def] >> strip_tac >>
  drule_all convert_bytes_site_split >> strip_tac >>
  qpat_x_assum `compile_expr ce _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr (gas_shadow_env _ _) _ _ _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) convert_bytes_site_split >>
  simp[] >> strip_tac >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
  pop_assum (qspecl_then [`a`,`sha`] mp_tac o
    REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows) >>
  imp_res_tac fragExecTheory.fn_has_code_split >>
  simp[s1PrefixDefsTheory.expr_sim_full_pre_def] >>
  rpt (first_assum (irule_at Any)) >>
  metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible]
QED

Theorem create_convert_bytes_vv_case:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type dst /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert dst [e]) es (st0,a,b,sha,shb,vv,s,G,tn) /\
  create_layout a b /\
  (!m shm x.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,x,s,G,tn) /\ create_layout a m ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (create_force_read_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,x,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 a b (eval_expr cx (TypeBuiltin ann Convert dst [e])) (es,s,G,tn)
    (\H res ee G1 tn1 t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx
      (TypeBuiltin ann Convert dst [e]) (es,a,b,s,vv,G,tn) H res ee G1 tn1 t /\
      create_operand_at b t)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (TypeBuiltin ann Convert dst [e])) (es,s)
Proof
  strip_tac >> drule exprSimConvertTheory.expr_body_pre_convert >> strip_tac >> gvs[] >>
  `is_bytestring_type (expr_type e)` by metis_tac[valid_conversion_to_bytestring] >>
  `~is_word_type ann /\ (!n. ann <> FlagT n)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type,compileEnvTheory.is_word_type_def] >>
  drule_all convert_bytes_child_site >> strip_tac >>
  `create_layout a m` by metis_tac[create_layout_subinterval, compileEnvTheory.cs_extends_refl] >>
  qpat_assum `!m shm x. _ ==> _` (drule_all_then strip_assume_tac) >>
  drule_all convert_bytes_slice >> strip_tac >>
  `create_cut_code {} m b` by metis_tac[convert_slice_cut_code] >>
  `lower_value compile_expr ce (expr_type e) e a = (x,m) /\
   MEM f ctx.ctx_functions /\ fn_has_code a m f /\ create_operand_at a s` by
     fs[s1PrefixDefsTheory.expr_sim_full_pre_def,create_operand_at_def] >>
  `create_cut_code {} a m` by metis_tac[cj 2 createSizeOperandCodeTheory.create_operand_cut_code,pairTheory.SND] >>
  gvs[] >> reverse conj_tac
  >- (irule convert_bytes_cut >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  `cx_tops cx = tops` by fs[bodySimTheory.body_inv_def,gasContextTheory.cx_tops_def] >>
  gvs[] >> irule convert_bytes_scoped_bind >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule convert_bytes_selected_suffix >>
  fs[s1PrefixDefsTheory.expr_sim_full_pre_def,s1PrefixDefsTheory.expr_vv_sim_full_pre_def,
     create_force_read_post_def,loweringPostsTheory.post_value_type_def] >>
  conj_tac >- (qexists_tac `left` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  conj_tac
  >- (drule_all_then mp_tac exprSimHypsTheory.expr_body_pre_type_evaluates >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
      `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
      drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
      strip_tac >> gvs[]) >>
  rpt conj_tac >> TRY (goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  simp[exprSimFullBundlePropsTheory.expr_sim_full_post_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[exprSimFullBundlePropsTheory.expr_sim_full_post_def,
       valueCopyBytesTheory.is_bytestring_word_type]
QED
