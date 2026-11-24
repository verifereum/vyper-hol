(* Finite-horizon composition for a framed fixed memory array. *)
Theory bodyFullSubscriptArrayMemory
Ancestors exprBopSimProps[qualified,ignore_grammar] integer[qualified,ignore_grammar] arithmetic[qualified,ignore_grammar] bodyPtrBopHashFootprint[qualified,ignore_grammar] exprSimBopRestWordLoads[qualified,ignore_grammar] exprSimHypsDefs[qualified,ignore_grammar] vyperTypeInvariants[qualified,ignore_grammar] exprSimIfExpCompat[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyFullFramedMemorySelectionSpec
  bodyFullTargetArraySuffix bodyPtrSignedConvertSourceFrame emitHelperProps
  bodyFullEmptyLeafData exprSimFullBundleProps
  bodyFullSubscriptArrayMemoryFrame bodyFullSubscriptArrayCodeBounds
  bodyFullSubscriptArrayCodeOps bodyFullIfExpReach bodyFullHashKeccakFixed stateRelProj
  exprSimVVFrame exprSimIfExpWidenedAdapter assignBasePtrBoundary
  gasShadowCompileStmtHelpers compilerInstructionSuffix fragGasOriginPtrLoop
  exprSimArrayIndex ptrDiscipline venomState
  fragGasOriginPtr words finite_map list
  bodyFullOfVV bodyFullPreds bodySimFull gasOutcomeFullCompose
  bodyFullGhostFrame bodyFullPathHistory
  exprSimSubscriptArrayCompose exprSimSubscriptArraySource
  exprSimSubscriptArrayFramed exprSimSubscriptArrayOrigin exprSimSubscriptArraySuffix
  exprSimSubscriptArrayEndpoint exprSimHyps exprSimSource
  exprOperandVar exprLoweringProps exprSimUnwrap fragExec
  gasShadowCompile gasShadowState gasShadow gasExemptCert
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom
  bodyPtrDefs loweringPosts compileEnv vyperInterpreter vyperState vyperAST

(* The selector's two paths use the same installed bounds and address cuts.
   Only the normal path executes the address calculation. *)
Theorem fixed_memory_selector_layout:
  compile_array_subscript bop idx F n ws elem_size sgn loader sa = (dst,sb) ==>
  ?sc sm offset out.
    array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) /\
    emit_op MUL [idx; Lit (n2w elem_size)] sc = (Var offset,sm) /\
    emit_op ADD [bop; Var offset] sm = (Var out,sb) /\ dst = Var out /\
    array_elem_ptr bop idx F ws elem_size sc = (dst,sb)
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> gvs[oneTheory.one] >> strip_tac >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def, comp_bind_def, comp_return_def,
       loweringShapeRulesTheory.emit_op_eq] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fixed_memory_bounds_mono[local]:
  array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) ==> ci_mono sa sc
Proof
  simp[array_bounds_check_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `array_bounds_valid _ _ _ sa = (valid,sv)` >>
  `ci_mono sa sv` by
    (qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     Cases_on `sgn` >> simp[array_bounds_valid_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     metis_tac[ci_mono_emit_op, pairTheory.SND, ci_mono_trans]) >>
  metis_tac[ci_mono_emit_void, pairTheory.SND, ci_mono_trans]
QED

(* One uniform endpoint for fixed-literal bounds checking followed by address
   arithmetic. The final ADD retains the captured base's provenance. *)
Theorem fixed_memory_selector_joint_ok:
  array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) /\
  emit_op MUL [idx;Lit (n2w elem_size)] sc = (Var offset,sm) /\
  emit_op ADD [base_op;Var offset] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. base_op = Var q ==> not_fresh_at sa q) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s = SOME a /\ op_taint tn base_op = {} /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  idx_in_range sgn (n2w i:bytes32) (n2w n) ==>
  ?Gf tnf sf.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sf,Gf,tnf)) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (i * elem_size)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov G base_op /\
    sf.vs_immutables = s.vs_immutables /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_data_section = s.vs_data_section /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!H cenv cx es. stmt_state_rel H ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel H ctx func cenv cx es sf) /\
    (?scheck Gcheck tncheck.
       scheck.vs_current_bb = sc.cs_current_bb /\
       scheck.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~scheck.vs_halted /\
       (!D lo explicit. allocas_from lo s ==>
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
            (OK scheck,Gcheck,tncheck) /\
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (scheck,Gcheck,tncheck) []
            (OK sf,Gf,tnf)))
Proof
  strip_tac >>
  drule_then assume_tac fixed_memory_bounds_mono >>
  `ci_mono sc sm /\ ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    metis_tac[fn_has_code_split, ci_mono_def, cs_extends_trans] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\ op_prov G (Lit (n2w n)) = NONE /\
   (!q. idx = Var q \/ Lit (n2w n) = Var q ==> not_fresh_at sa q) /\
   (!l. idx <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all array_bounds_check_read_only_joint_ok_frame >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G1`,`tn1`,`s1`] strip_assume_tac) >>
  `eval_operand base_op s1 = SOME a /\ op_taint tn1 base_op = {} /\
   op_prov G1 base_op = op_prov G base_op` by
    (Cases_on `base_op` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `eval_operand idx s1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def, op_prov_def]) >>
  `!q. base_op = Var q ==> not_fresh_at sc q` by
    metis_tac[ci_mono_def, loweringShapeDefsTheory.not_fresh_at_mono] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (`allocas_below_fmp s1 <=> allocas_below_fmp s` by simp[allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  drule_all scalar_mul_add_joint_frame >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`G2`,`tn2`,`s2`] strip_assume_tac) >>
  qexistsl [`G2`,`tn2`,`s2`] >> simp[arithmeticTheory.MULT_COMM] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      irule gas_origin_ptr_path_trans >> qexistsl [`G1`,`s1`,`tn1`] >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc q` by metis_tac[ci_mono_def, loweringShapeDefsTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `local_ptrs_reserved cenv sc` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
      metis_tac[]) >>
  qexistsl_tac [`s1`,`G1`,`tn1`] >> simp[] >>
  rpt strip_tac >> gvs[allocas_from_def] >> first_assum irule >> first_assum ACCEPT_TAC
QED

(* Keep the installed base, index and fixed selector cuts in one view. *)
Theorem framed_memory_subscript_compile_cuts:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = ValPT (ArrayT et (Fixed n)) /\
  ~copies_subscript_base cenv obj idx /\
  (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory) /\
  fn_has_code sa sb func ==>
  ?bvv sm iop st2 dst.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,st2) /\
    vv_location bvv = SOME LocMemory /\
    compile_array_subscript (vv_operand bvv) iop F n (word_scale LocMemory)
      (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory) /\
    cs_extends sa sm /\ cs_extends sm st2 /\ cs_extends st2 sb /\
    fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func
Proof
  strip_tac >> drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `vv_location bvv = SOME LocMemory` by metis_tac[pairTheory.FST] >> gvs[] >>
  drule_then assume_tac compile_expr_extends >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[]
QED

Theorem subscript_array_framed_memory_full_from_selection:
  framed_memory_selection_rule (\a b c s r. T) ==>
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et n.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 /\ body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et (Fixed n) /\
    place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r,t') ==>
      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
      eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e1 es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base,
              exprSimTopLevelPropsTheory.array_slot_base_compile_location] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e1 es` by
    (fs[body_expr_full_ok_def] >> metis_tac[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all framed_memory_subscript_compile_cuts >>
  disch_then (qx_choosel_then [`bvv`,`sm`,`iop`,`st2`,`dst`] strip_assume_tac) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  qpat_assum `compile_expr cenv ty e1 sa = _`
    (mp_then Any strip_assume_tac compile_expr_extends) >>
  qpat_assum `lower_value compile_expr _ _ e2 sm = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >> gvs[] >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e1)
         (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (reverse conj_tac
     >- (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
         simp[gas_shadow_expr_def] >> strip_tac >>
         qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr e1) _) _ = _`
           (mp_then Any mp_tac compile_expr_array_subscript) >>
         fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
         rename1 `lower_value _ _ _ (gas_shadow_expr e2) shadow_sm = (_,shadow_st2)` >>
         qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) _ = _`
           (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
         `cs_extends shadow_st2 shadow_sb` by
           (`ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
            qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
              (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
            irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
         irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
     drule compile_expr_extends >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx e1) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> (gvs[]))) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule gas_outcome_full_bind_all_path >>
  `!res : eval_result + exception. !r.
    (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >> simp[] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_select] >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_base" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >> metis_tac[]
QED

Resume subscript_array_framed_memory_full_from_selection[after_base]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ mid.gas_obs = []`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (fn th => mk_asm "base_path" th >>
      qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac) th) >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (mk_asm "base_eval") >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `body_expr_full_ok cx e2` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (fs[body_expr_full_ok_def] >> metis_tac[]) >>
  `?shadow_st2. lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2)
      shadow_sm = (iop,shadow_st2) /\ gas_shadow_state st2 shadow_st2` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e2)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sm`, `shadow_sm`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2) shadow_sm` >>
     simp[]) >>
  `cs_extends shadow_sm shadow_st2 /\ cs_extends shadow_st2 shadow_sb` by
    (`cs_extends shadow_sm shadow_st2` by
       (qpat_assum `lower_value _ _ _ _ shadow_sm = _`
          (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     drule compile_expr_array_subscript >>
     fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
     `ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `fn_has_code sm st2 func /\ fn_has_code shadow_sm shadow_st2 shadow_func` by
    metis_tac[fn_has_code_split] >>
  `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
      es sa sm s0 mid tv bvv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> fs[vv_post_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `st2`, `shadow_sm`, `shadow_st2`,
                          `iop`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt conj_tac
     >- metis_tac[local_ptrs_reserved_next_var]
     >- metis_tac[expr_body_pre_gas_admissible]
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
           metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G1,tn1)` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
           qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
             (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
              CONJ path o CONJ no_phi))))
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
         strip_tac >> fs[vv_post_def]))) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ indexQ indexR` >>
  irule gas_outcome_full_bind_all_path >> simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "selection" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >>
  conj_tac >- simp[Abbr `indexR`, Abbr `baseR`] >>
  simp[Abbr `indexQ`, Abbr `indexR`, Abbr `baseR`] >>
  qx_genl_tac [`H`, `res`, `ee`, `r`] >>
  Cases_on `res` >> simp[] >> strip_tac >> conj_tac
  >- (qpat_x_assum `expr_exit (INR _ : value + exception) _` mp_tac >>
      rename1 `expr_exit (INR exc : eval_result + exception) r` >>
      Cases_on `r` >> Cases_on `exc` >>
      simp[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  fs[exprSimDefsTheory.halt_exit_def]
QED

Resume subscript_array_framed_memory_full_from_selection[selection]:
  qx_genl_tac [`imarks`, `ires`, `fin`, `Gi`, `tni`, `it`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `indexQ (storage_trace_horizon fin.storage_trace) ires fin Gi tni it /\
   ~it.vs_halted /\ fin.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `indexQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `indexQ`, NoAsms] >> strip_tac >> gvs[] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (select_result cx (expr_type e1) tv (ValueSubscript v))
     (fin,it,Gi,tni)
     (expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript ann e1 e2)
       (es,sa,sb,s0,LocatedValue ann (mk_ptr dst LocMemory),G0,tn0)) baseR`
    suffices_by
      simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def, post_value_type_def,
           AC CONJ_ASSOC CONJ_COMM] >>
  asm "base_eval" assume_tac >> asm "base_path" assume_tac >>
  `framed_memory_selection_hypotheses
     (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     (tops,cenv,cx,env,ty,ann,e1,e2,et,n)
     (st0,es,sa,sb,shadow_sa,shadow_sb,LocatedValue ann (mk_ptr dst LocMemory),s0,G0,tn0)
     (sm,bvv,marks,tv,mid,s,G1,tn1) (st2,iop,imarks,v,fin,it,Gi,tni) dst` by
    (simp[framed_memory_selection_hypotheses_def, expr_vv_sim_full_hypotheses_def,
          expr_sim_full_code_def, expr_vv_sim_full_post_def, expr_sim_full_post_def,
          expr_sim_full_endpoint_def] >> rpt strip_tac >>
     (qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _`
        (drule_then ACCEPT_TAC) ORELSE
      (first_assum (drule_then strip_assume_tac) >> simp[]))) >>
  drule_all framed_memory_selection_rule_full >> simp[Abbr `baseR`]
QED

Finalise subscript_array_framed_memory_full_from_selection[local]

(* We ask for an observation only on the selected scalar run.  The fixed
   selector has no header load and reads its bound from a literal. *)
Definition fixed_memory_scalar_observer_def:
  fixed_memory_scalar_observer Obs <=>
  !idx n sgn sa sc bop ws esz p sb s b iw tn G lo ctx explicit func PG.
    array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) /\
    array_elem_ptr bop idx F ws esz sc = (p,sb) /\
    eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    op_taint tn bop = {} /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    same_blocks sa sc /\ same_blocks sc sb /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    fn_has_code sa sc func /\ fn_has_code sc sb func /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sa sc) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t H tm.
      Obs sa sc sb s (if idx_in_range sgn iw (n2w n) then OK t else Abort Revert_abort t) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (if idx_in_range sgn iw (n2w n) then OK t else Abort Revert_abort t,H,tm)) /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
        FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
        (if idx_in_range sgn iw (n2w n) then s else revert_state (set_returndata [] s)) /\
      (idx_in_range sgn iw (n2w n) ==>
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        eval_operand p t = SOME (b + iw * n2w esz) /\
        op_prov H p = op_prov G bop /\ op_taint tm p = {})
End

Theorem fixed_memory_scalar_unobserved[local]:
  fixed_memory_scalar_observer (\a b c s r. T)
Proof
  simp[fixed_memory_scalar_observer_def] >> rpt gen_tac >> strip_tac >>
  rename1 `array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc)` >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\ op_prov G (Lit (n2w n)) = NONE /\
   (!x. Lit (n2w n) = Var x ==> not_fresh_at sa x)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]
QED

Theorem fixed_memory_scalar_code[local]:
  array_bounds_check idx len sgn sa = ((),sc) /\
  array_elem_ptr bop idx F ws esz sc = (dst,sb) /\ fn_has_code sa sb func ==>
  same_blocks sa sc /\ same_blocks sc sb /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
  fn_has_code sa sc func /\ fn_has_code sc sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sc) /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sc sb)
Proof
  strip_tac >>
  `same_blocks sa sc /\ sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sa sc)` by
    (qpat_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     Cases_on `sgn` >> simp[array_bounds_valid_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
          venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `same_blocks sc sb /\ sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sc sb)` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
          venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  simp[] >> irule fn_has_code_split >>
  simp[cs_extends_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  conj_tac >- (qexists `[]` >> fs[same_blocks_def]) >>
  qexists `[]` >> fs[same_blocks_def]
QED

Theorem framed_memory_selection_observed:
  fixed_memory_scalar_observer Obs ==> framed_memory_selection_rule Obs
Proof
  simp[framed_memory_selection_rule_def] >> disch_tac >> rpt gen_tac >>
  simp[framed_memory_selection_hypotheses_def, expr_vv_sim_full_hypotheses_def,
       expr_sim_full_code_def, expr_vv_sim_full_post_def, expr_sim_full_post_def,
       expr_sim_full_endpoint_def] >>
  strip_tac >> suspend "selection"
QED

Resume framed_memory_selection_observed[selection]:
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ (_ with gas_obs := _ ++ tail) =
        (INL _,_ with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => pure_rewrite_tac[APPEND_NIL,th]) >>
     disch_then ACCEPT_TAC) >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) = (INL v,fin)` by
    (qpat_assum `!tail. bind _ _ (_ with gas_obs := _ ++ tail) =
        (INL _,_ with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => pure_rewrite_tac[APPEND_NIL,th]) >>
     disch_then ACCEPT_TAC) >>
  `?ir. eval_expr cx e2 (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) =
      (INL ir,fin) /\ read_result cx ir fin = (INL v,fin)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >> metis_tac[]) >>
  `fin.scopes = mid.scopes /\ fin.immutables = mid.immutables` by
    (qpat_x_assum `!t r t'. eval_expr cx e2 t = _ ==> _` drule >> simp[]) >>
  `?p. bvv = LocatedValue (ArrayT et (Fixed n)) p /\ p.ptr_location = LocMemory` by
    (`vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
       es sa sm s0 mid tv bvv s` by metis_tac[] >>
     Cases_on `bvv` >> gvs[contextTheory.vv_location_def] >>
     metis_tac[vv_post_def, vv_holds_def, is_bytestring_type_def]) >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `local_ptrs_reserved cenv sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `local_ptrs_reserved cenv st2` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `!l. p.ptr_operand <> Label l` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac compile_array_pointer_not_label) >>
     disch_then irule >> simp[] >>
     qexists_tac `env` >>
     qpat_assum `expr_body_pre cenv cx env e1 es`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
     qpat_assum `expr_sim_inv cenv cx env mid`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     simp[]) >>
  `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` by metis_tac[] >>
  `expr_body_pre cenv cx env e2
     (mid with gas_obs := gas_explicit imarks s.vs_gas_readings)` by simp[] >>
  `?itv. evaluate_type (get_tenv cx) (expr_type e2) = SOME itv /\
     value_has_type itv v` by
    (drule_all expr_body_pre_runtime_typed >> strip_tac >> metis_tac[]) >>
  `expr_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx e2
     mid sm st2 s fin v iop it` by metis_tac[] >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type e2)` by
    (qpat_x_assum `value_has_type itv v` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     qpat_x_assum `v = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type e2` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
       vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  gvs[] >>
  `!l. iop <> Label l` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac exprReasonOperandTheory.lower_compile_expr_not_label) >>
     disch_then (qspec_then `env` mp_tac) >>
     qpat_assum `expr_body_pre cenv cx env e2 mid`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
     qpat_assum `expr_sim_inv cenv cx env mid`
       (strip_assume_tac o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     simp[]) >>
  suspend "base_view"
QED

Resume framed_memory_selection_observed[base_view]:
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (_ /\ _) /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (strip_assume_tac o CONJUNCT1))) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> (_ /\ _) /\ gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon fin.storage_trace`
      (drule_then (strip_assume_tac o CONJUNCT1))) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     vv_post H ctx func cenv cx (Subscript (ArrayT ann (Fixed n)) e1 e2)
       es sa st2 s0 fin tv (LocatedValue (ArrayT ann (Fixed n)) p) it` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _` drule >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     `stmt_state_rel H ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx fin it` by metis_tac[expr_post_def] >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
     irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `env` >> simp[]) >>
  `vv_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx
     (Subscript (ArrayT ann (Fixed n)) e1 e2)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) sa st2 s0 fin tv
     (LocatedValue (ArrayT ann (Fixed n)) p) it` by
    (simp[exprSimPropsTheory.vv_post_initial_gas] >> metis_tac[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`)
    framed_array_post_view >>
  disch_then (qspecl_then [`mid`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `vv_holds cenv cx (ArrayT ann (Fixed n)) tv
      (LocatedValue (ArrayT ann (Fixed n)) p) fin it /\
   vv_at cenv cx (ArrayT ann (Fixed n)) sa st2 fin tv
      (LocatedValue (ArrayT ann (Fixed n)) p) it /\
   ptr_vv_ok cx (ArrayT ann (Fixed n)) tv
      (LocatedValue (ArrayT ann (Fixed n)) p) fin Gi tni it /\
   ptr_buf_ok cenv e1 p.ptr_operand Gi it` by
    (`valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) mid.storage_trace` by
       (qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon fin.storage_trace` (strip_assume_tac o UNDISCH)) >>
     `expr_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx e2
        mid sm st2 s fin
        (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)) iop it` by metis_tac[] >>
     `dynarray_free etv` by metis_tac[] >>
     qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac
         (INST_TYPE [alpha |-> ``:256``] captured_memory_base_transport)) >>
     simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> simp[]) >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
     `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
        es sa sm s0 mid tv (LocatedValue (ArrayT ann (Fixed n)) p) s` by metis_tac[] >>
     `wb_frame cenv es mid sa s0 s` by
       (qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, vv_post_def, wb_frame_def] >> metis_tac[]) >>
     drule_all wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]) >>
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  `valid_index (ArrayTV etv (Fixed n)) av
      (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) <=>
   idx_in_range (is_signed_type (expr_type e2)) iw (n2w n)` by
    (metis_tac[array_index_word_bounds]) >>
  suspend "scalar"
QED

Resume framed_memory_selection_observed[scalar]:
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
    (mp_then Any mp_tac fixed_memory_selector_layout) >>
  disch_then (qx_choosel_then [`sc`,`s_mul`,`off`,`out`] strip_assume_tac) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  drule_all fixed_memory_scalar_code >> strip_tac >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (`ci_mono st2 sc` by (drule fixed_memory_bounds_mono >> simp[]) >>
     `ci_mono sc s_mul /\ ci_mono s_mul sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
     fs[ci_mono_def] >> decide_tac) >>
  `!q. p.ptr_operand = Var q ==> not_fresh_at st2 q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `op_taint tni p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
  qpat_x_assum `fixed_memory_scalar_observer Obs`
    (drule_all o REWRITE_RULE [fixed_memory_scalar_observer_def]) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
  disch_then (qx_choosel_then [`sf`,`Gf`,`tnf`] strip_assume_tac) >>
  Cases_on `valid_index (ArrayTV etv (Fixed n)) av
    (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)`
  >- (`idx_in_range (is_signed_type (expr_type e2)) iw (n2w n)` by
        (qpat_assum `valid_index _ _ _ <=> idx_in_range _ _ _` (irule o iffLR) >>
         first_assum ACCEPT_TAC) >>
      qpat_assum `idx_in_range _ _ _` (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th])) >>
      suspend "valid_selection") >>
  `~idx_in_range (is_signed_type (expr_type e2)) iw (n2w n)` by metis_tac[] >>
  qpat_assum `~idx_in_range _ _ _` (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th])) >>
  suspend "rejected_selection"
QED

Resume framed_memory_selection_observed[valid_selection]:
  drule vyperArrayTheory.array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  `?child. select_result cx (ArrayT ann (Fixed n)) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))) fin =
        (INL child,fin) /\ read_result cx child fin = (INL x,fin)` by
    (irule framed_array_select_read >> simp[] >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `e1`, `mid`] >> simp[]) >>
  `!tail. select_result cx (ArrayT ann (Fixed n)) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)))
      (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)` by
    simp[select_result_nonstorage_gas_obs] >>
  `well_formed_type_value etv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type etv x` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
  `val_wf etv x` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV
       (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))] /\
       tv = PlaceR (MemoryPlace id path)` by
    (qpat_assum `select_result _ _ _ _ fin = (INL child,fin)`
       (mp_tac o MATCH_MP exprSimPropsTheory.select_result_memory_place) >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`, `mid`] >> simp[]) >>
  `Num (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) = w2n iw` by
    (Cases_on `is_signed_type (expr_type e2)` >> fs[] >>
     Cases_on `w2n iw < INT_MIN (:256)` >>
     fs[integer_wordTheory.w2i_eq_w2n] >>
     `w2n iw < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
     intLib.COOPER_TAC) >>
  suspend "selector"
QED

Resume framed_memory_selection_observed[selector]:
  qpat_x_assum `~sf.vs_halted /\ _` strip_assume_tac >>
  `sf = it with <|vs_vars := sf.vs_vars; vs_inst_idx := sf.vs_inst_idx|>` by
    (qpat_assum `sf with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
     simp[NoAsms, venom_state_component_equality]) >>
  `sf.vs_immutables = it.vs_immutables /\ sf.vs_memory = it.vs_memory /\
   sf.vs_allocas = it.vs_allocas /\ sf.vs_alloca_next = it.vs_alloca_next /\
   sf.vs_data_section = it.vs_data_section /\ sf.vs_fmp = it.vs_fmp /\
   sf.vs_accounts = it.vs_accounts /\ sf.vs_transient = it.vs_transient /\
   sf.vs_call_ctx = it.vs_call_ctx /\ sf.vs_requests = it.vs_requests` by
    (qpat_assum `sf = it with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `lookup_var out sf = SOME (w + n2w (w2n iw * elem_size_in_location cenv LocMemory ann))` by
    (fs[eval_operand_def] >> metis_tac[wordsTheory.n2w_w2n, wordsTheory.word_mul_n2w]) >>
  `w2n w + val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) < dimword (:256)` by
    (qpat_assum `vv_post _ _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac vv_post_memory_footprint_bound) >>
     simp[vyperASTTheory.expr_type_def, post_value_type_def]) >>
  qabbrev_tac `j = Num (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)` >>
  `j = w2n iw` by simp[Abbr `j`] >>
  `w2n ((w:bytes32) + n2w (j * type_memory_size etv)) = w2n w + j * type_memory_size etv` by
    (drule_all fixed_array_element_nonwrapping >> simp[Abbr `j`]) >>
  `0 <= (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) /\
   (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) < &n` by
    (qpat_assum `array_length (ArrayTV _ _) _ = n` (fn len =>
       qpat_assum `valid_index _ _ _`
         (ACCEPT_TAC o REWRITE_RULE [vyperArrayTheory.valid_index_def,len]))) >>
  `j < n` by
    (`&j = (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)` by
       simp[Abbr `j`, integerTheory.INT_OF_NUM] >>
     qpat_assum `(if _ then _ else _) < &n` mp_tac >>
     qpat_assum `&j = (if _ then _ else _)` (SUBST1_TAC o SYM) >> simp[]) >>
  `j * type_memory_size etv + type_memory_size etv <=
    type_memory_size (ArrayTV etv (Fixed n))` by
    (pure_rewrite_tac[valueEncodingTheory.type_memory_size_def,
       GSYM (cj 5 arithmeticTheory.MULT_CLAUSES)] >>
     irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `lowered_value_type cenv e1 = expr_type e1` by
    (qpat_assum `expr_body_pre cenv cx env e1 es`
       (mp_then Any assume_tac expr_body_pre_var_types_well_formed) >>
     qpat_assum `expr_body_pre cenv cx env e1 es` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >> strip_tac >>
     drule exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
     disch_then (qspec_then `cenv` mp_tac) >>
     simp[is_bytestring_type_def] >>
     (impl_tac >-
        (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC)) >>
     disch_then (DISJ_CASES_THEN2 ACCEPT_TAC STRIP_ASSUME_TAC) >>
     qpat_x_assum `e1 = Call _ _ _ _` SUBST_ALL_TAC >>
     qpat_assum `expr_type (Call _ _ _ _) = _`
       (mp_tac o REWRITE_RULE [vyperASTTheory.expr_type_def]) >>
     disch_then SUBST_ALL_TAC >>
     qpat_assum `post_value_type cenv (Call _ _ _ _) = _`
       (ACCEPT_TAC o SRULE [cj 1 post_value_type_def,
          is_word_type_def, is_bytestring_type_def])) >>
  `type_memory_bytes cenv (lowered_value_type cenv e1) =
     type_memory_size (ArrayTV etv (Fixed n))` by
    (simp[] >> irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`mid`] >> simp[]) >>
  `0 < type_memory_size etv ==> ptr_covers Gf tnf out sf (type_memory_size etv)` by
    (strip_tac >>
     `0 < type_memory_size (ArrayTV etv (Fixed n))` by decide_tac >>
     `?parent_reg. p.ptr_operand = Var parent_reg /\
        ptr_covers Gi tni parent_reg it (type_memory_size (ArrayTV etv (Fixed n)))` by
       (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >> simp[] >>
        qexistsl_tac [`cenv`,`e1`] >> simp[]) >>
     `lookup_var parent_reg it = SOME w` by
       (qpat_x_assum `eval_operand p.ptr_operand it = SOME w` mp_tac >>
        simp[venomStateTheory.eval_operand_def]) >>
     qpat_x_assum `ptr_covers Gi tni parent_reg it _` mp_tac >>
     simp[ptr_covers_def] >> strip_tac >>
     rename1 `FLOOKUP Gi parent_reg = SOME (region_base, region_size)` >>
     `FLOOKUP Gf out = SOME (region_base, region_size)` by
       (qpat_x_assum `op_prov Gf (Var out) = op_prov Gi p.ptr_operand` mp_tac >>
        simp[ptrDisciplineTheory.op_prov_def]) >>
     simp[ptr_covers_def] >>
     gvs[elem_size_in_location_def, is_slot_addressed_def] >> decide_tac) >>
  suspend "child_endpoint"
QED

Resume framed_memory_selection_observed[child_endpoint]:
  `!q. not_fresh_at st2 q ==> lookup_var q sf = lookup_var q it` by
    (simp[lookup_var_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at st2 x ==> FLOOKUP Gf x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!name b sz. local_region cenv fin.scopes it name b sz <=>
               local_region cenv fin.scopes sf name b sz` by
    (rpt gen_tac >> sym_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `st2` >> simp[]) >>
  `eval_operand p.ptr_operand sf = SOME w` by
    (irule exprBopSimPropsTheory.eval_operand_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `cs_extends st2 sb` mp_tac >> simp[cs_extends_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     vv_post H ctx func cenv cx (Subscript (ArrayT ann (Fixed n)) e1 e2)
       es sa sb s0 fin tv (LocatedValue (ArrayT ann (Fixed n)) p) sf` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx fin it` by
       (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> (expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _) /\ _`
          (qspec_then `H` (drule_then (irule o MATCH_MP exprSimWordArgsTheory.expr_post_state o CONJUNCT1 o CONJUNCT1)))) >>
     `stmt_state_rel H ctx func cenv cx fin sf` by
       (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`it`,`st2`] >> simp[]) >>
     irule memory_vv_post_readonly_tail >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     qexistsl_tac [`it`,`st2`] >> simp[] >>
     fs[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
     metis_tac[]) >>
  `eval_operand (Var out) sf = SOME (w + n2w (j * type_memory_size etv))` by
    (simp[venomStateTheory.eval_operand_def, elem_size_in_location_def,
          is_slot_addressed_def] >>
     pure_rewrite_tac[GSYM wordsTheory.word_mul_n2w, wordsTheory.n2w_w2n] >>
     simp[wordsTheory.WORD_MULT_COMM]) >>
  `vv_place_ptr cenv cx fin sf tv (LocatedValue (ArrayT ann (Fixed n)) p)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ sb _ _ _ _ sf`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> simp[NoAsms, vv_post_def]) >>
  `vv_place_ptr cenv cx fin sf child (LocatedValue ann (mk_ptr (Var out) LocMemory))` by
    (`vv_place_ptr cenv cx fin sf child (LocatedValue ann (mk_ptr (Var out) p.ptr_location))`
       suffices_by simp[] >>
     irule array_element_place_ptr >>
     goal_assum (drule_at (Pat `vv_place_ptr _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >>
     qexists_tac `env` >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 fin child
       (LocatedValue ann (mk_ptr (Var out) LocMemory)) sf` by
    ((rpt strip_tac >>
     `vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 fin child
       (LocatedValue ann (mk_ptr (Var out) p.ptr_location)) sf` suffices_by simp[] >>
     irule vv_post_array_element >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ sb _ _ _ _ sf`
       (qspec_then `H` (strip_assume_tac o UNDISCH)) >>
     simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >> simp[] >> (gvs[vv_post_array_element]))) >>
  suspend "selected_ptr"
QED

Resume framed_memory_selection_observed[selected_ptr]:
  `ptr_vv_ok cx ann child (LocatedValue ann (mk_ptr (Var out) LocMemory)) fin Gf tnf sf /\
   ptr_buf_ok cenv (Subscript ann e1 e2) (Var out) Gf sf` by
    (conj_tac
     >- (simp[ptr_vv_ok_def, contextTheory.mk_ptr_def] >>
         `ptr_mem_ok cx (ArrayT ann (Fixed n)) (ArrayV av) p.ptr_operand Gi tni it` by
           ((qpat_assum `ptr_vv_ok _ _ tv _ fin Gi tni it` mp_tac >> simp[ptr_vv_ok_def] >> (gvs[ptr_vv_ok_def]))) >>
         simp[ptr_mem_ok_def] >> conj_tac
         >- ((rpt strip_tac >>
             `val_in_memory (ArrayTV etv (Fixed n)) (ArrayV av) (w2n w) mem` by
               (irule bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust >>
                goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >> simp[]) >>
             `&j = (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)` by
               simp[Abbr `j`, integerTheory.INT_OF_NUM] >>
             `array_index (ArrayTV etv (Fixed n)) av (&j) = SOME x` by simp[] >>
             drule_all exprSimBopRestWordLoadsTheory.rest_word_array_memory_index >>
             simp[arithmeticTheory.MULT_COMM] >> (metis_tac[Abbr `j`, integerTheory.INT_OF_NUM, arithmeticTheory.MULT_COMM, bodyPtrBopHashFootprintTheory.ptr_mem_ok_robust, exprSimBopRestWordLoadsTheory.rest_word_array_memory_index]))) >>
         strip_tac >>
         `val_footprint etv x <= val_store_size etv x /\
          val_store_size etv x <= type_memory_size etv` by
           simp[exprSimPropsTheory.val_footprint_le_store_size, exprSimPropsTheory.val_store_size_le] >>
         `0 < type_memory_size etv` by decide_tac >>
         `ptr_covers Gf tnf out sf (type_memory_size etv)` by simp[] >>
         qpat_x_assum `ptr_covers Gf tnf out sf _`
           (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
         goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >>
         gvs[elem_size_in_location_def, is_slot_addressed_def,
             arithmeticTheory.MULT_COMM] >> decide_tac) >>
     simp[ptr_buf_ok_def, exprLoweringTheory.lowered_value_type_def,
          vyperASTTheory.expr_type_def] >> strip_tac >>
     `ptr_covers Gf tnf out sf (type_memory_size etv)` by simp[] >>
     qpat_x_assum `ptr_covers Gf tnf out sf _`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >>
     gvs[elem_size_in_location_def, is_slot_addressed_def,
         arithmeticTheory.MULT_COMM]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx fin Gf tnf sf` by
    (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`Gi`,`fin`,`it`,`st2`,`tni`] >> simp[] >>
     `!x. not_fresh_at sa x ==> not_fresh_at st2 x` by
       (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
     rpt conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> simp[])
     >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl_tac [`Gi`,`tni`] >> simp[pred_setTheory.SUBSET_REFL] >>
     `!q. not_fresh_at sa q ==> not_fresh_at st2 q` by
       (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
     rpt strip_tac >> simp[ptrDisciplineTheory.op_taint_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
     metis_tac[]) >>
  `alloca_inv it` by
    (drule exprSimWordArgsTheory.expr_post_state >>
     disch_then assume_tac >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func sf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `wb_frame cenv mid fin sm s it` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `eval_operand p.ptr_operand s = SOME w` by
    (`?bw. eval_operand p.ptr_operand s = SOME bw` by
       ((qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ mid tv _ s` mp_tac >>
        simp[NoAsms, vv_post_def, vv_holds_def] >> metis_tac[])) >>
     `eval_operand p.ptr_operand it = SOME bw` by
       ((irule exprBopSimPropsTheory.eval_operand_frame >>
        conj_tac >- simp[] >>
        qexistsl_tac [`sm`,`s`] >> simp[] >>
        qpat_assum `wb_frame cenv mid fin sm s it` mp_tac >> simp[wb_frame_def] >> (metis_tac[wb_frame_def, exprBopSimPropsTheory.eval_operand_frame]))) >>
     gvs[]) >>
  `val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) =
   type_memory_size (ArrayTV etv (Fixed n))` by simp[val_footprint_def] >>
  `!v. child = Value v ==> vv_own cenv cx ann sa sb fin (Value v)
            (LocatedValue ann (mk_ptr (Var out) LocMemory)) sf` by
    (rpt strip_tac >> suspend "selected_own") >>
  `vv_store_bound cx ann ann fin child
       (LocatedValue ann (mk_ptr (Var out) LocMemory)) sf` by
    suspend "selected_capacity" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sf` by
    (qpat_assum `sf = it with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp it` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[NoAsms]) >>
  `(mk_ptr (Var out) LocMemory).ptr_location = LocMemory /\
   (mk_ptr (Var out) LocMemory).ptr_operand = Var out` by
    simp[contextTheory.mk_ptr_def] >>
  qexistsl [`sc`,`s_mul`,`off`,`out`,`INL child`,`OK sf`,`Gf`,`tnf`] >>
  simp[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def]
QED

Resume framed_memory_selection_observed[selected_own]:
  `tv = Value (ArrayV av)` by
    (Cases_on `tv`
     >- fs[read_result_def, return_def]
     >- (rename1 `read_result cx (PlaceR pl) fin = _` >> Cases_on `pl` >>
         gvs[select_result_def, extend_place_def, extend_memory_place_def,
             bind_def, ignore_bind_def, return_def, lift_sum_def, raise_def,
             AllCaseEqs()]) >>
     fs[read_result_def, raise_def]) >>
  `local_ptrs_rel func cenv mid.scopes s` by
    (qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ mid tv _ s`
       (strip_assume_tac o REWRITE_RULE[vv_post_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!name b sz. local_region cenv fin.scopes sf name b sz ==>
               local_region cenv mid.scopes s name b sz` by
    (drule_all exprSimSubscriptArrayFrameTheory.local_region_wb_frame >>
     metis_tac[]) >>
  `vv_own cenv cx (ArrayT ann (Fixed n)) sa sb fin tv
     (LocatedValue (ArrayT ann (Fixed n)) (mk_ptr p.ptr_operand LocMemory)) sf` by
    (`vv_own cenv cx (ArrayT ann (Fixed n)) sa sm mid tv
        (LocatedValue (ArrayT ann (Fixed n)) p) s` by
       (qpat_assum `!v'. tv = Value v' /\ _ ==> _` (qspec_then `ArrayV av` mp_tac) >>
        simp[is_word_type_def, is_bytestring_type_def]) >>
     qpat_x_assum `vv_own _ _ _ _ sm _ _ _ s` mp_tac >>
     simp[vv_own_def, contextTheory.mk_ptr_def, read_result_def, return_def] >>
     strip_tac
     >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (b,sz)` >>
         `FLOOKUP it.vs_allocas aid = SOME (b,sz)` by
           (qpat_assum `wb_frame cenv mid fin sm s it`
              (mp_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
            disch_then drule >> simp[]) >>
         `aid < sb.cs_next_id` by decide_tac >>
         disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
         rpt gen_tac >> disch_tac >>
         qpat_assum `!n lb lsz. local_region cenv mid.scopes s n lb lsz ==> _` irule >>
         metis_tac[]) >>
     simp[]) >>
  `j * type_memory_size etv + val_footprint etv x <=
      val_footprint (ArrayTV etv (Fixed n)) (ArrayV av)` by
    (`val_footprint etv x <= val_store_size etv x /\
      val_store_size etv x <= type_memory_size etv` by
       simp[exprSimPropsTheory.val_footprint_le_store_size, exprSimPropsTheory.val_store_size_le] >>
     qpat_assum `val_footprint (ArrayTV _ _) _ = _` SUBST1_TAC >>
     decide_tac) >>
  irule vv_own_memory_slice >>
  goal_assum (drule_at (Pat `vv_own _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_result cx tv _ = _`)) >>
  qexistsl_tac [`etv`,`x`,`w + n2w (j * type_memory_size etv)`,
                `j * type_memory_size etv`,`ArrayTV etv (Fixed n)`,`w`] >>
  simp[] >>
  metis_tac[]
QED

Resume framed_memory_selection_observed[selected_capacity]:
  Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC)
    `type_memory_size etv = 0 \/
     w2n (w + n2w (j * type_memory_size etv)) + type_memory_size etv <= sf.vs_alloca_next`
  >- (qpat_assum `vv_store_bound _ _ _ mid tv _ s`
       (mp_tac o cj 2 o REWRITE_RULE [exprSimMemDefsTheory.vv_store_bound_def]) >>
     disch_then (qspecl_then [`ArrayT ann (Fixed n)`,`p.ptr_operand`,
                              `ArrayTV etv (Fixed n)`,`w`] mp_tac) >>
     qpat_x_assum `j * type_memory_size etv + type_memory_size etv <= _` mp_tac >>
     Cases_on `type_memory_size etv = 0` >> simp[] >> decide_tac) >>
  irule (exprSimMemDefsTheory.vv_store_bound_capacity |>
    INST_TYPE [alpha |-> ``:256``] |>
    Q.INST [`e` |-> `Subscript ann e1 e2`] |>
    SRULE [vyperASTTheory.expr_type_def, post_value_type_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ (Subscript ann e1 e2) _ _ _ _ _ child _ sf`
    drule >>
  disch_then (irule_at Any) >>
  qpat_x_assum `type_memory_size etv = 0 \/ _` mp_tac >>
  qpat_x_assum `w2n (w + n2w (j * type_memory_size etv)) = _` mp_tac >>
  simp[contextTheory.mk_ptr_def, AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM] >>
  strip_tac >> simp[]
QED

Resume framed_memory_selection_observed[rejected_selection]:
  `select_result cx (ArrayT ann (Fixed n)) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))) fin =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
    (irule framed_array_select_error >> simp[] >> conj_tac
     >- gvs[vyperArrayTheory.valid_index_def] >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `e1`, `mid`] >> simp[]) >>
  `!tail. select_result cx (ArrayT ann (Fixed n)) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)))
      (fin with gas_obs := tail) =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)` by
    simp[select_result_nonstorage_gas_obs] >>
  qexistsl [`sc`,`s_mul`,`off`,`out`,
    `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
    `Abort Revert_abort sf`,`Gf`,`tnf`] >>
  simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]
QED

Finalise framed_memory_selection_observed

Theorem subscript_array_framed_memory_full:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et n.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 /\ body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et (Fixed n) /\
    place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r,t') ==>
      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
      eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  mp_tac (MATCH_MP framed_memory_selection_observed fixed_memory_scalar_unobserved) >>
  ACCEPT_TAC subscript_array_framed_memory_full_from_selection
QED
