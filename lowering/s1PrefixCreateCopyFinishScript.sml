(* Prepare the dynamic initcode window before certifying its dispatch. *)
Theory s1PrefixCreateCopyFinish
Ancestors
  bodyFullCreateHeld s1PrefixCompose s1PrefixFrame fragGasOriginPtr
  builtinCreate vyperInterpreter vyperCreate vyperState vyperCallOutcome
  vyperStorageTrace vyperStorageFootprint vyperTypeInvariants vfmConstants
  loweringPosts exprLoweringProps vyperExprEffects compileEnv codegenRel contextCodegenRel bodyPtrDefs loweringStateRelDefs
  venomState venomMemDefs ptrSafeRun ptrDiscipline memSafeRun

Theorem create_copy_finish_prefix_from_dispatch:
  (!sc buf len t Gmat tt pv sz initcode.
    compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
    fn_has_code sc sb func /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee Gmat tt t) /\
    outcomes_accounts_typed ee.outcomes /\
    eval_operand buf t = SOME pv /\ eval_operand len t = SOME sz /\
    (sz <> 0w ==> ?p. buf = Var p /\ ptr_covers Gmat tt p t (w2n sz)) /\
    (sz <> 0w ==> w2n pv + w2n sz <= t.vs_alloca_next \/
      (ctx_has_dalloca ctx /\ w2n t.vs_initial_fmp <= w2n pv /\
       w2n pv + w2n sz <= w2n t.vs_fmp)) /\
    read_memory (w2n pv) (w2n sz) t = initcode /\
    (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tt.t_mem) /\
    op_taint tt buf = {} /\ op_taint tt len = {} /\
    eval_operand amount t = SOME aw /\ op_taint tt amount = {} /\
    (case sop of NONE => sw = NONE | SOME op =>
       ?w. sw = SOME w /\ eval_operand op t = SOME w /\ op_taint tt op = {}) /\
    (!tail. source (ee with gas_obs := tail) =
      if w2n sz > 2 * max_code_size then
        (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
      else
        bind (ignore_bind (check_not_static cx)
          (create_oracle_result sw (w2n aw) initcode rof))
          (read_result cx) (ee with gas_obs := tail)) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,t,Gmat,tt)) /\
  compile_create_copy target amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) marks (OK s,G,tn) /\
  (!fn i z. contextRawReachable$frag_reachable ctx func s0 fn i z ==> dalloca_fmp_headroom i z) /\
  storage_trace_domain cx st0 ee.storage_trace /\ valid_horizon cx st0 H ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  accounts_well_typed ee.accounts /\ LENGTH bs = 20 /\ outcomes_accounts_typed ee.outcomes /\
  eval_operand target s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn target = {} /\ eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
    ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!x. target = Var x \/ amount = Var x \/ sop = SOME (Var x) ==> not_fresh_at sm x) /\
  code = (lookup_account (word_of_bytes_be bs) ee.accounts).code /\
  storage_trace_frame source /\
  (!tail. source (ee with gas_obs := tail) =
    if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),
                        ee with gas_obs := tail)
    else bind (ignore_bind (check_not_static cx)
      (create_oracle_result sw (w2n aw) (create_copy_initcode code) rof))
      (read_result cx) (ee with gas_obs := tail)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `code = []`
  >- (irule gas_prefix_full_no_outcome >> simp[] >>
      rpt gen_tac >> strip_tac >> gvs[]) >>
  qpat_assum `gas_origin_ptr_path _ _ _ _`
    (mp_then Any (drule_all_then mp_tac) create_copy_prepared_path) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choose_then `sc` (qx_choose_then `buf` (qx_choose_then `len`
    (qx_choose_then `p` (qx_choose_then `t` (qx_choose_then `Gmat` (qx_choose_then `tt`
      (qx_choose_then `pv` (qx_choose_then `sz` (map_every assume_tac o CONJUNCTS)))))))))) >>
  `LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code <= 24576` by
    fs[accounts_well_typed_def,account_well_typed_def] >>
  `~(w2n sz > 2 * max_code_size)` by
    (qpat_assum `sz = _` SUBST1_TAC >>
     qspec_then `LENGTH code + 11`
       mp_tac (INST_TYPE [``:'a`` |-> ``:256``] wordsTheory.word_n2w_le2) >>
     simp[max_code_size_def]) >>
  irule gas_prefix_full_zero_prefix_guarded >> simp[] >>
  qexistsl [`Gmat`,`t`,`tt`] >> simp[] >>
  qpat_assum `!sc buf len t Gmat tt pv sz initcode. _` irule >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand buf t = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand len t = SOME _` (irule_at Any) >>
  qpat_assum `read_memory _ _ t = _` (irule_at Any) >>
  qpat_x_assum `sz = _` kall_tac >> simp[]
QED
