(* The request's optional generated GAS, before any calldata packing. *)
Theory entryCreateExtRequestGas
Ancestors
  bodyFullRawCallGas generatedGasOrigin msgGasSim
  entryCreateAdminSequence entryCreateNativeFirstExit
  createSizeCutCode createMarkedPath createSizePrefixReplay
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  createExprSizeExitDefs bodySim gasSummaryCompose fragGasMode fragGasPath
  emitHelper compileEnv emitHelperProps exprLoweringProps gasSummary fragGasOriginPtr
  fragGasOrigin fragExec gasOracleReplay gasEvents gasExplicitSites gasShadowState
  gasShadowUnit venomWf venomInst venomState venomExecSemantics abiEncoderProps
  bodyPtrDefs ptrDiscipline loweringStateRelDefs allocaHistory vyperValue
  vyperTypeSystem finite_map rich_list option arithmetic
  vyperStorageFootprint vyperInterpreter vyperState list relation pred_set

Theorem extcall_emitted_gas_layout[local]:
  emit_op GAS [] a = (gas,b) ==>
  create_cut_code {} a b /\ ci_mono a b /\
  b.cs_next_id = SUC a.cs_next_id /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b
Proof
  strip_tac >>
  `create_cut_code {} a (SND (emit_op GAS [] a))` by
    simp[create_cut_code_emit_op, create_cut_targets_def] >>
  `ci_mono a (SND (emit_op GAS [] a))` by simp[ci_mono_emit_op] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, emitted_insts_def, DROP_APPEND]
QED

(* The endpoint is the one given by the optional-GAS semantic producer.
   Its exact update, installed fetch and shadow classification determine the
   only edge of the compiler interval. *)
Theorem extcall_emitted_gas_scope[local]:
  emit_op GAS [] a = (gas,b) /\
  emit_op GAS [] sha = (shgas,shb) /\
  gas_shadow_state a sha /\
  gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code sha shb shfunc /\
  create_operand_at a s /\ ~s.vs_halted /\
  gas_prefix 1 s.vs_gas_readings = [gw] ==>
  create_operand_full_scope a b (gas_explicit_sites ctx shctx) ctx func s [F]
    (OK (update_var (FST (fresh_var a)) gw
      (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                 vs_inst_idx := LENGTH b.cs_current_insts|>)))
Proof
  strip_tac >> fs[create_operand_at_def] >>
  drule_all compile_generated_gas_origin_path >>
  disch_then (qspec_then `F` strip_assume_tac) >>
  qpat_assum `emit_op GAS [] a = (gas,b)`
    (mp_then Any mp_tac emit_gas_placement_id) >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `emit_op GAS [] a = (gas,b)`
    (mp_then Any strip_assume_tac extcall_emitted_gas_layout) >>
  qabbrev_tac `i = mk_inst a.cs_next_id GAS [] [FST (fresh_var a)]` >>
  qabbrev_tac `t = update_var (FST (fresh_var a)) gw
    (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
               vs_inst_idx := LENGTH b.cs_current_insts|>)` >>
  `get_instruction bb s.vs_inst_idx =
       SOME (mk_inst a.cs_next_id GAS [] [FST (fresh_var a)])` by simp[] >>
  `?v. gas_prefix 1 s.vs_gas_readings = [v] /\
       gas_path_mem_edge ctx func s 1
         (OK (update_var (FST (fresh_var a)) v
           (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                      vs_inst_idx := SUC s.vs_inst_idx|>)))` by
    (irule msg_gas_mem_edge >> metis_tac[]) >>
  `gas_path_mem_edge ctx func s 1 (OK t)` by gvs[Abbr `t`] >>
  `gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s
    [(func.fn_name,a.cs_next_id) IN gas_explicit_sites ctx shctx] (OK t)` by
    (irule gas_mem_edge_origin >> metis_tac[]) >>
  `create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx func s [F] t` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def, create_prefix_step_def] >>
     fs[Abbr `i`, mk_inst_def, frag_ids_def] >>
     qpat_assum `(func.fn_name,a.cs_next_id) NOTIN gas_explicit_sites ctx shctx`
       (fn th => qpat_assum `gas_origin_edge F _ _ _ _ _ (OK t)`
           (ACCEPT_TAC o SIMP_RULE bool_ss [th]))) >>
  qpat_x_assum `b.cs_current_insts = _ ++ _` kall_tac >>
  fs[create_operand_full_scope_def, Abbr `t`, update_var_def] >>
  metis_tac[]
QED

(* Input is the normal keyword post's gas projection, together with its
   cursor and state/ghost invariants. In particular a source keyword is
   never evaluated again and the implicit read consumes no source GAS. *)
Theorem extcall_request_gas_scoped_cut:
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  (case shgo of SOME g => (g,sh3) | NONE => emit_op GAS [] sh3) = (shgas,sh5) /\
  (IS_NONE go <=> IS_NONE shgo) /\ gas_shadow_state s3 sh3 /\
  gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code s3 s5 func /\ fn_has_code sh3 sh5 shfunc /\
  local_ptrs_reserved cenv s3 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x) /\
  storage_trace_domain cx st0 ke.storage_trace /\
  (!H. valid_horizon cx st0 H ke.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ke G3 tn3 z /\
    stmt_state_rel H ctx func cenv cx ke z /\
    storage_well_formed_on cx ke (FST H)) /\
  alloca_history func z /\ ~z.vs_halted /\ create_operand_at s3 z /\
  (case source_gas of NONE => go = NONE | SOME gv =>
     ?op w. go = SOME op /\ eval_operand op z = SOME w /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tn3 op = {}) ==>
  ?zg Gg tng gw.
    let marks = case go of SOME _ => [] | NONE => [F] in
    create_cut_code {} s3 s5 /\ ci_mono s3 s5 /\
    create_operand_full_scope s3 s5 (gas_explicit_sites ctx shctx) ctx func z marks (OK zg) /\
    (!source. create_operand_cut s3 s5 (gas_explicit_sites ctx shctx)
          ctx func tops cx st0 source (ke,z)) /\
    (!right. gas_explicit (marks ++ right) z.vs_gas_readings =
             gas_explicit right zg.vs_gas_readings) /\
    eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
    (!n. OPTION_BIND source_gas dest_NumV = SOME n ==> n = w2n gw) /\
    ~zg.vs_halted /\ create_operand_at s5 zg /\ alloca_history func zg /\
    zg.vs_labels = z.vs_labels /\ zg.vs_memory = z.vs_memory /\
    zg.vs_allocas = z.vs_allocas /\ zg.vs_alloca_next = z.vs_alloca_next /\
    zg.vs_fmp = z.vs_fmp /\ tng.t_mem = tn3.t_mem /\
    tng.t_stor = tn3.t_stor /\ tng.t_trans = tn3.t_trans /\ tng.t_imm = tn3.t_imm /\
    (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
        FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
    (!H. valid_horizon cx st0 H ke.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (z,G3,tn3) marks (OK zg,Gg,tng) /\
      ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg /\
      stmt_state_rel H ctx func cenv cx ke zg /\
      storage_well_formed_on cx ke (FST H) /\
      ghost_kept_at lo cenv ke s3 G3 tn3 z Gg tng)
Proof
  Cases_on `source_gas` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qpat_assum `emit_op GAS [] s3 = (gas,s5)`
        (mp_then Any strip_assume_tac extcall_emitted_gas_layout) >>
      `!source. create_operand_cut s3 s5 (gas_explicit_sites ctx shctx)
          ctx func tops cx st0 source (ke,z)` by
        (gen_tac >> irule create_admin_sequence_cut >>
         qpat_assum `emit_op GAS [] s3 = (gas,s5)`
           (mp_then Any mp_tac emitted_insts_emit_op) >>
         simp[mk_inst_def, is_terminator_def]) >>
      `z.vs_current_bb = s3.cs_current_bb /\ z.vs_inst_idx = LENGTH s3.cs_current_insts`
        by fs[create_operand_at_def] >>
      drule_all (PURE_REWRITE_RULE
        [option_case_def, IS_NONE_DEF, NOT_NONE_SOME, DROP_0,
         AND_CLAUSES, IMP_CLAUSES, REFL_CLAUSE, COND_CLAUSES, FORALL_SIMP]
        (Q.INST [`go` |-> `NONE`, `shadow_go` |-> `NONE`] raw_call_optional_gas_joint)) >>
      disch_then (qspec_then `PG`
        (qx_choosel_then [`t`,`G6`,`tn6`,`gw`]
          (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
      qexistsl_tac [`t`,`G6`,`tn6`,`gw`] >>
      `create_operand_full_scope s3 s5 (gas_explicit_sites ctx shctx) ctx func z [F] (OK t)` by
        (qpat_assum `t = update_var _ _ _` SUBST1_TAC >>
         irule extcall_emitted_gas_scope >> simp[] >> metis_tac[]) >>
      `!right. gas_explicit (F::right) z.vs_gas_readings =
               gas_explicit right t.vs_gas_readings` by
        (qpat_assum `t.vs_gas_readings = _` (SUBST1_TAC) >>
         Cases_on `z.vs_gas_readings` >> simp[gas_explicit_cons]) >>
      `t.vs_labels = z.vs_labels` by
        (qpat_assum `t = update_var _ _ _` SUBST1_TAC >> simp[update_var_def]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[create_operand_at_def] >>
      rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`z`,`G3`,`tn3`] >>
  simp[ci_mono_refl, ghost_kept_at_def, gas_origin_ptr_path_rules] >>
  metis_tac[create_operand_empty_scope, create_operand_cut_def]
QED

(* Use the administrative gas selection as a normal unit-valued left
   operand of the common scoped bind. It does not run any source action. *)
Theorem extcall_gas_prefix_outcome:
  storage_trace_domain cx st0 ke.storage_trace /\
  gas_explicit marks z.vs_gas_readings = [] /\
  create_operand_full_scope a b E ctx func z marks (OK zg) /\
  (!H. valid_horizon cx st0 H ke.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (z,G,tn) marks (OK zg,Gg,tng) /\
    Q H (ke with gas_obs := []) Gg tng zg) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (return ()) (ke,z,G,tn)
    (\H res ee G' tn' t. res = INL () /\ (t,G',tn') = (zg,Gg,tng) /\ Q H ee G' tn' t)
    (\H res ee gt r. F)
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL ()`,`ke`,`OK zg`,`Gg`,`tng`] >>
  simp[return_def] >> metis_tac[]
QED

(* The completed native prefix fixes the same caller endpoint. Comparing
   against the unit-valued outcome reuses the existing replay theorem. *)
Theorem extcall_gas_prefix_landing[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  valid_horizon cx st0 H ke.storage_trace /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (return ()) (ke,z,G,tn)
    (\H res ee G' tn' t. res = INL () /\ (t,G',tn') = (zg,Gg,tng) /\ Q H ee G' tn' t)
    (\H res ee gt r. F) /\
  create_expr_prefix a b E ctx func z native t /\ create_operand_at b t ==>
  t = zg /\ !rest. gas_explicit (native ++ rest) z.vs_gas_readings =
                    gas_explicit rest zg.vs_gas_readings
Proof
  strip_tac >> drule_all scoped_outcome_completed_operand >>
  simp[gas_completed_operand_def, return_def] >> strip_tac >>
  qpat_assum `!K marks u. _` (qspecl_then [`H`,`native`,`t`] mp_tac) >>
  fs[create_operand_at_def] >> strip_tac >>
  qpat_assum `!K. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `gas_path ctx func z (LENGTH native) (OK t)` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> strip_tac >>
     metis_tac[gas_marked_path_exec]) >>
  simp[] >> rpt strip_tac >> drule gas_explicit_append_path >> simp[]
QED

Theorem extcall_gas_prefix_cut_lift:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b func /\
  create_cut_code {} b c /\ fn_has_code b c func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  valid_horizon cx st0 H ke.storage_trace /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (return ()) (ke,z,G,tn)
    (\H res ee G' tn' t. res = INL () /\ (t,G',tn') = (zg,Gg,tng) /\ Q H ee G' tn' t)
    (\H res ee gt r. F) /\
  create_operand_cut a b E ctx func tops cx st0 source (ke,z) /\
  create_operand_cut b c E ctx func tops cx st0 source (ke,zg) ==>
  create_operand_cut a c E ctx func tops cx st0 source (ke,z)
Proof
  rewrite_tac[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- metis_tac[] >>
  drule_all extcall_gas_prefix_landing >> strip_tac >> gvs[] >>
  qpat_assum `!p d k before hit after. create_interior_visit b c _ _ _ _ _ _ ==> _`
    (drule_then mp_tac) >>
  simp[create_body_cut_def]
QED
