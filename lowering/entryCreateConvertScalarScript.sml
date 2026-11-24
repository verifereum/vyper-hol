(* Scalar Convert owns one checked straight-line suffix, entered only after
   the selected forced child completes. *)
Theory entryCreateConvertScalar
Ancestors
  entryCreateAdminSequence entryCreateScopedBind
  entryCreatePendingScope entryCreateOperandReplay entryCreateBodyCut
  entryCreateFocusSpec s1PrefixDefs
  bodyFullConvertScalarJoint bodyFullConvertScalarRun
  bodyPtrTypeBuiltinsScalarRawOutcome freshWrites
  gasShadowCompileStmtHelpers vyperStorageTrace createSizeTypeBuiltinCode
  exprSimConvert exprLowering exprLoweringProps compileEnv vyperContext
  vyperInterpreter vyperState vyperAST venomInst venomInstProps list
  venomExecSemantics venomState emitHelperProps fragExec fragGasOrigin
  entryCreateCompletedCut createSizePrefixReplay createMarkedPath
  entryCreatePathScope entryCreateIntervalLayout entryCreateRegionLift
  entryCreateNativeFirstExit exprSimAbiGasBridge relation arithmetic

Definition scalar_convert_cont_def:
  scalar_convert_cont cx src dst v ee =
    (sum_CASE (convert_result cx src dst v) (\w. INL (Value w)) INR, ee)
End

Theorem scalar_convert_source[local]:
  eval_expr cx (TypeBuiltin ann Convert ann [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (scalar_convert_cont cx (expr_type e) ann)
Proof
  simp[FUN_EQ_THM, scalar_convert_cont_def] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,ee)` >>
  Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
  Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val ann` >>
  simp[scalar_convert_cont_def, convert_result_def, return_def, raise_def]
QED

Theorem scalar_convert_cont_frame[local,simp]:
  storage_trace_frame (scalar_convert_cont cx src dst v)
Proof
  simp[scalar_convert_cont_def, storage_trace_frame_def]
QED

Theorem scalar_convert_compile_split[local]:
  ~is_bytestring_type (expr_type e) /\
  compile_expr ce ty (TypeBuiltin ann Convert ann [e]) a = (vv,b) ==>
  ?x m out.
    lower_value compile_expr ce (expr_type e) e a = (x,m) /\
    compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) m = (out,b) /\
    vv = StackValue ann out
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr ce (expr_type e) e a` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  Cases_on `ann` >> gvs[exprBopLoweringTheory.as_stack_val_pair] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem scalar_convert_layout[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) m = (out,b) ==>
  b.cs_blocks = m.cs_blocks /\
  b.cs_current_bb = m.cs_current_bb /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
    ~is_terminator i.inst_opcode) (emitted_insts m b)
Proof
  strip_tac >> drule_all scalar_dispatch_straight_fresh >>
  disch_then (drule_at (Pat `compile_type_convert _ _ _ = _`) o
    REWRITE_RULE [straight_fresh_def]) >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  qpat_assum `writes_fresh _ _` (drule_at (Pat `MEM _ _`) o
    REWRITE_RULE [writes_fresh_def, EVERY_MEM]) >>
  Cases_on `i.inst_opcode` >> gvs[fresh_write_op_def, is_terminator_def]
QED

Theorem scalar_convert_pre_split[local]:
  ~is_bytestring_type (expr_type e) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert ann [e]) es (st0,a,b,sha,shb,vv,s0,G0,tn0) ==>
  ?x m shm out.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,x,s0,G0,tn0) /\
    compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) m = (out,b) /\
    vv = StackValue ann out /\
    cs_extends a m /\ cs_extends m b /\ fn_has_code m b f
Proof
  rw[expr_vv_sim_full_pre_def] >> drule_all scalar_convert_compile_split >> strip_tac >>
  `?shm. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha = (x,shm) /\ gas_shadow_state m shm` by
    (`gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
       (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
         (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`a`,`sha`] mp_tac o
       REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e) sha` >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `cs_extends a m /\ cs_extends sha shm` by metis_tac[compile_expr_grows] >>
  `cs_extends m b /\ cs_extends shm shb` by
    (Cases_on `ann` >> gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels, pairTheory.SND]) >>
  `fn_has_code a m f /\ fn_has_code m b f /\ fn_has_code sha shm shf` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  qexistsl_tac [`x`,`m`,`shm`] >> simp[expr_sim_full_pre_def] >>
  metis_tac[convert_operand_admissible, exprSimStackTheory.eval_expr_force_admissible,
    eval_expr_type_builtin_value]
QED

Theorem scalar_convert_cut_code[local]:
  compile_type_convert x op m = (out,b) ==> create_cut_code {} m b
Proof
  strip_tac >> `create_cut_code {} m (SND (compile_type_convert x op m))` by
    irule compile_type_convert_cut_code >>
  pop_assum mp_tac >> asm_simp_tac bool_ss [pairTheory.SND]
QED

Theorem scalar_convert_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\ fn_has_code m b f /\
  valid_conversion (expr_type e) ann /\ ~is_bytestring_type (expr_type e) /\
  compile_type_convert x (case ann of FlagT name =>
    ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op (expr_type e) ann) m = (out,b) /\
  create_operand_cut a m E ctx f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) /\
  (!p d k before hit after.
    create_interior_visit a b E ctx f (p,d,k) s (before,hit,after) ==>
    create_interior_visit a m E ctx f (p,d,k) s (before,hit,after) \/
    ?t d1 k1 front back. before = front ++ back /\ create_operand_at m t /\
      create_interior_visit m b E ctx f (p,d1,k1) t (back,hit,after)) ==>
  create_operand_cut a b E ctx f tops cx st0 (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s)
Proof
  strip_tac >> drule_then assume_tac scalar_convert_cut_code >>
  drule_all scalar_convert_layout >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  qpat_assum `!p d k before hit after. _ ==> _ \/ _` (drule_then strip_assume_tac)
  >- (once_rewrite_tac[scalar_convert_source] >>
      irule create_cut_bind_left >> simp[] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut m b E ctx f tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >> fs[EVERY_MEM]) >>
  qpat_x_assum `create_operand_cut m b _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED

(* A raw abort itinerary and a marked path from the same installed slice
   have the same first fetch. Successful steps reindex the raw tail; the
   abort is taken at the current slot, strictly before the slice exit. *)
Theorem scalar_convert_run_edge[local]:
  gas_origin_edge T E ctx f s marks r /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
  r = (case step_inst_base i s of
          OK u => OK (u with vs_inst_idx := SUC s.vs_inst_idx)
        | q => q)
Proof
  simp[fragGasOriginTheory.gas_origin_edge_def] >>
  strip_tac >> gvs[step_inst_non_invoke, exit_result_def] >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem scalar_convert_abort_slice[local]:
  !code s u err t bb.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    (!j. j < LENGTH code ==> get_instruction bb (s.vs_inst_idx + j) = SOME (EL j code)) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort err u /\
    gas_origin_path T E ctx f s [] (Abort err t) ==>
    create_operand_full_scope a b E ctx f s [] (Abort err t)
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. _ ==> get_instruction _ _ = _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once fragGasOriginTheory.gas_origin_path_cases])
  >- (drule_all_then assume_tac scalar_convert_run_edge >>
      Cases_on `step_inst_base h s` >> gvs[exit_result_def] >>
      rename1 `step_inst_base h s = OK raw` >>
      qabbrev_tac `v = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
      `raw.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_inst_non_invoke, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      `run_inst_seq code v = Abort err (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[Abbr `v`, run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
      first_x_assum (qspecl_then [`v`,`u with vs_inst_idx := SUC s.vs_inst_idx`,`err`,`t`,`bb`] mp_tac) >>
      impl_tac
      >- (simp[Abbr `v`, ADD_CLAUSES] >> rpt strip_tac >>
          qpat_assum `!j. _ ==> get_instruction bb _ = _`
            (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >>
          simp[ADD_CLAUSES]) >>
      simp[create_operand_full_scope_def] >> strip_tac >>
      rename1 `create_expr_prefix a b E ctx f v [] stop` >>
      `create_prefix_step a b E ctx f s [] v` by
        (simp[create_prefix_step_def] >>
         qpat_assum `gas_origin_edge T E ctx f s [] (OK v)` mp_tac >>
         simp[gas_origin_edge_def, NoAsms] >> metis_tac[]) >>
      qexists_tac `stop` >> simp[] >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
        create_expr_prefix_append)) >> qexists_tac `v` >> simp[] >>
      simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
      simp[create_marked_edge_def]) >>
  rw[create_operand_full_scope_def] >> qexists_tac `s` >> simp[]
QED

Theorem scalar_convert_terminal_scope[local]:
  fn_has_code m b f /\ create_cut_code {} m b /\
  b.cs_blocks = m.cs_blocks /\ b.cs_current_bb = m.cs_current_bb /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
    ~is_terminator i.inst_opcode) (emitted_insts m b) /\
  create_operand_at m t /\ ~t.vs_halted /\
  gas_origin_path T E ctx f t [] r /\
  ((?u. run_inst_seq (emitted_insts m b) t = OK u /\
         r = OK (u with vs_inst_idx := LENGTH b.cs_current_insts)) \/
   (?err u t'. run_inst_seq (emitted_insts m b) t = Abort err u /\ r = Abort err t')) ==>
  create_operand_full_scope m b E ctx f t [] r
Proof
  strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids m b /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts m b)` by
    fs[EVERY_MEM,createSizeCutCodeTheory.create_cut_code_def,frag_code_def,emitted_blocks_def] >>
  gvs[] >- (drule_all create_admin_sequence_scope >> simp[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule scalar_convert_abort_slice >> simp[] >> qexistsl_tac [`bb`,`emitted_insts m b`,`u`] >>
  fs[create_operand_at_def,EVERY_MEM]
QED

Theorem scalar_convert_terminal_scoped[local]:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre ce cx env e es /\ valid_conversion (expr_type e) ann /\
  ~is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  lower_value compile_expr ce (expr_type e) e a = (x,m) /\
  compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) m = (out,b) /\
  fn_has_code m b f /\ fn_inst_ids_distinct f /\ local_ptrs_reserved ce a /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
  create_operand_at m t /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s0,x,G0,tn0)
       H (INL v : value + exception) mid G1 tn1 t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 m b
    (scalar_convert_cont cx (expr_type e) ann v) (mid,t,G1,tn1)
    (\H res ee G tn z.
       create_operand_vv_post (DF,lo,d,ctx,f) ce cx (TypeBuiltin ann Convert ann [e])
         (es,a,b,s0,StackValue ann out,G0,tn0) H res ee G tn z /\
       z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> drule_all scalar_convert_layout >> strip_tac >>
  drule_then assume_tac scalar_convert_cut_code >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all scalar_convert_selected_terminal >>
  disch_then (qspecl_then [`E`,`PG`] strip_assume_tac) >> gvs[]
  >- (simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL (Value vout)`,`mid`,`OK (u with vs_inst_idx := LENGTH b.cs_current_insts)`,`Gf`,`tnf`] >>
      simp[scalar_convert_cont_def,gasSummaryTheory.gas_explicit_def] >> conj_tac
      >- (`EVERY (\i. i.inst_id IN frag_ids m b /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts m b)` by
            fs[EVERY_MEM,createSizeCutCodeTheory.create_cut_code_def,frag_code_def,emitted_blocks_def] >>
          drule_all create_admin_sequence_scope >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!H. _ ==> expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
          [bodyFullEmptyLeafDataTheory.expr_vv_sim_full_post_def,
           exprSimFullBundlePropsTheory.expr_sim_full_endpoint_def])) >>
      qpat_x_assum `_ + _ = LENGTH b.cs_current_insts` kall_tac >>
      simp[create_operand_vv_post_def,contextTheory.vv_location_def,exit_result_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `gas_origin_path T E ctx f t [] (Abort err t')` by
    (first_x_assum (drule_then (strip_assume_tac o MATCH_MP
       fragGasOriginPtrTheory.gas_origin_ptr_path_projections))) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`mid`,`Abort err t'`,`Gf`,`tnf`] >>
  simp[scalar_convert_cont_def,gasSummaryTheory.gas_explicit_def,create_operand_exit_post_def,
       exit_result_def,exprSimDefsTheory.expr_exit_def,haltExitProjTheory.halt_exit_not_halt] >>
  irule scalar_convert_terminal_scope >> simp[] >> qexists_tac `u` >> simp[]
QED

Theorem scalar_convert_prefix_widen[local]:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E ctx f p ms q ==>
  create_prefix_step a b E ctx f p ms q
Proof
  simp[create_prefix_step_def,abiEncoderPropsTheory.frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem scalar_convert_full_join[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E ctx f s left t /\
  create_operand_full_scope m b E ctx f t right r ==>
  create_operand_full_scope a b E ctx f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono,scalar_convert_prefix_widen,
            create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem scalar_convert_focus_join[local]:
  a.cs_next_id <= m.cs_next_id /\ body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_operand_at m t /\
  create_expr_prefix a b E ctx f s left t /\ create_operand_focus_scope m b E ctx f t right ==>
  create_operand_focus_scope a b E ctx f s (left ++ right)
Proof
  strip_tac >> irule create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule create_operand_focus_scope_lift >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >> simp[] >>
  `create_cut_region m b t` by
    (drule_all createSizeCutRegionTheory.create_cut_region_rules >> fs[create_operand_at_def]) >>
  metis_tac[scalar_convert_prefix_widen]
QED

Theorem scalar_convert_scoped_bind[local]:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Convert ann [e]) es /\
  expr_body_pre ce cx env e es /\ valid_conversion (expr_type e) ann /\
  ~is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
    (st0,a,m,sha,shm,x,s0,G0,tn0) /\
  compile_type_convert x (case ann of FlagT name =>
      ConvToFlag (ce.ce_flag_n_members (nsid_to_string name))
      | _ => mk_convert_op (expr_type e) ann) m = (out,b) /\
  fn_has_code m b f /\ a.cs_next_id <= m.cs_next_id /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s0,x,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  (!marks t. create_expr_prefix a m E ctx f s0 marks t ==>
             create_expr_prefix a b E ctx f s0 marks t) /\
  (!marks. create_operand_focus_scope a m E ctx f s0 marks ==>
           create_operand_focus_scope a b E ctx f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s0 marks r ==>
             create_operand_full_scope a b E ctx f s0 marks r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s0,G0,tn0)
    (\H res ee G tn z.
       create_operand_vv_post (DF,lo,d,ctx,f) ce cx (TypeBuiltin ann Convert ann [e])
         (es,a,b,s0,StackValue ann out,G0,tn0) H res ee G tn z /\
       z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> drule_then assume_tac scalar_convert_cut_code >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  once_rewrite_tac[scalar_convert_source] >> irule scoped_operand_bind_all_mixed >>
  simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
      irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexistsl_tac [`\H res mid G1 tn1 t.
    expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s0,x,G0,tn0)
      H res mid G1 tn1 t /\ mid.gas_obs = []`,`m`] >> simp[] >>
  rpt conj_tac
  >~ [`create_operand_focus_scope a b _ _ _ _ (_ ++ _)`]
  >- (rpt strip_tac >> fs[create_operand_full_scope_def, create_operand_at_def] >>
      irule scalar_convert_focus_join >> simp[create_operand_at_def] >> metis_tac[])
  >~ [`create_operand_full_scope a b _ _ _ _ (_ ++ _) _`]
  >- (rpt strip_tac >> irule scalar_convert_full_join >>
      qexistsl_tac [`m`,`t`] >> fs[create_operand_full_scope_def])
  >- suspend "selected_continuation" >>
  suspend "child"
QED

Resume scalar_convert_scoped_bind[child]:
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks` >> simp[]
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> Cases_on `r` >>
      gvs[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def,
          exprSimDefsTheory.halt_exit_def,AllCaseEqs()] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Resume scalar_convert_scoped_bind[selected_continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?v. res = INL v` by
    (first_x_assum drule >> simp[exprSimFullBundlePropsTheory.expr_sim_full_post_def] >> metis_tac[]) >>
  gvs[] >>
  `~t.vs_halted` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
              fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  irule scalar_convert_terminal_scoped >> simp[] >>
  conj_tac >- (qexists_tac `marks` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `env` >> simp[]
QED
Finalise scalar_convert_scoped_bind

Theorem create_convert_scalar_vv_case:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann Convert ann [e]) es /\
  ~is_bytestring_type (expr_type e) /\ ~is_bytestring_type ann /\
  create_layout a b /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (TypeBuiltin ann Convert ann [e]) es (st0,a,b,sha,shb,vv,s0,G0,tn0) /\
  (!m shm x. create_layout a m /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
      (st0,a,m,sha,shm,x,s0,G0,tn0) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s0,x,G0,tn0))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 a b (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx
      (TypeBuiltin ann Convert ann [e]) (es,a,b,s0,vv,G0,tn0) H res ee G tn t /\
      create_operand_at b t)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
    (eval_expr cx (TypeBuiltin ann Convert ann [e])) (es,s0)
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  drule_all scalar_convert_pre_split >> strip_tac >> gvs[] >>
  `create_layout a m` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  qpat_assum `!m shm x. _ ==> _` (drule_all_then strip_assume_tac) >>
  drule_then assume_tac operand_value_cut_code >>
  drule_then assume_tac scalar_convert_cut_code >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  `create_cut_region a m s0` by
    (irule (cj 1 createSizeCutRegionTheory.create_cut_region_rules) >> simp[] >>
     qexists_tac `f` >> simp[]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  `a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[createSizeCutCodeTheory.create_cut_code_def] >>
  reverse conj_tac
  >- (irule scalar_convert_cut >> simp[] >> qexistsl_tac [`ce`,`m`,`out`,`x`] >> simp[] >>
      rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[]) >>
  simp[create_operand_at_def] >> irule scalar_convert_scoped_bind >>
  qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  qexists_tac `env` >> simp[] >>
  conj_tac >- (rpt strip_tac >> drule_all create_left_terminal_lift_at >> simp[]) >>
  conj_tac >- (rpt strip_tac >> drule_all create_left_prefix_lift_at >> simp[]) >>
  rpt strip_tac >> drule_all create_left_focus_lift_at >> simp[]
QED
