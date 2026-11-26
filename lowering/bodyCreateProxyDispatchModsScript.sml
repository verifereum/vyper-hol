(* The minimal-proxy suffix starts at the prepared 54-byte window. *)
Theory bodyCreateProxyDispatchMods
Ancestors
  bodyCreateDispatchMods bodyFullPostsMods gasOutcomeFullMods
  exprSimHypsDefs stateRelProj loweringStateRelDefs loweringPosts
  builtinCreate vyperCreate vyperInterpreter vyperState vyperStorageFootprint
  vfmConstants venomInst venomState bodyPtrDefs words list

Theorem create_proxy_read_prepared_mods:
  IS_SOME ee.outcomes /\ dest_AddressV tv = SOME addr /\
  dest_NumV av = SOME value /\ dest_optional_salt salt = SOME sw /\
  LENGTH ts = (if IS_SOME salt then 3 else 2) ==>
  bind (eval_create_operands cx CreateMinimalProxy (IS_SOME salt) rof ts off
        (tv::av::(case salt of NONE => [] | SOME v => [v])))
    (read_result cx) ee =
  bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw value (minimal_proxy_initcode addr) rof))
    (read_result cx) ee
Proof
  Cases_on `salt` >>
  simp[NoAsms,eval_create_operands_def,create_operand_layout_def,dest_optional_salt_def] >>
  rpt strip_tac >>
  qpat_x_assum `LENGTH ts = _` mp_tac >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [eval_create_def] >>
  simp[dest_create_args_def,make_create_operands_def,dest_optional_num_def,
       dest_optional_salt_def,create_arg_ctor_types_def,build_create_code_def] >>
  simp[bind_def,ignore_bind_def,lift_option_type_def,lift_option_def,
       get_accounts_def,check_def,check_not_static_def,assert_def,return_def,raise_def] >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

Theorem create_proxy_dispatch_prepared_mods:
  compile_create_dispatch (Var p) (Lit 54w) amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    immutable_frame_mods func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  expr_sim_inv_mods mods cenv cx env ee /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 54 /\
  w2n w + 54 <= s.vs_alloca_next /\
  read_memory (w2n w) 54 s = minimal_proxy_initcode addr /\
  (!i. w2n w <= i /\ i < w2n w + 54 ==> i NOTIN tn.t_mem) /\
  op_taint tn (Var p) = {} /\ eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  dest_AddressV tv = SOME addr /\ dest_NumV av = SOME (w2n aw) /\
  dest_optional_salt salt = SOME sw /\ LENGTH ts = (if IS_SOME salt then 3 else 2) /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_create_operands cx CreateMinimalProxy (IS_SOME salt) rof ts off
           (tv::av::(case salt of NONE => [] | SOME v => [v]))) (read_result cx)) (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `IS_SOME ee.outcomes` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     drule stmt_state_rel_state_rel >> simp[state_rel_def]) >>
  `outcomes_accounts_typed ee.outcomes` by
    fs[expr_sim_inv_mods_def] >>
  `54 < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `w2n (54w:256 word) = 54` by
    (simp[wordsTheory.w2n_n2w_compute]) >>
  `w2n (54w:256 word) <= 2 * max_code_size` by
    (simp[vfmConstantsTheory.max_code_size_def]) >>
  drule (Q.INST [`sz` |-> `54w`] create_dispatch_outcome_full_mods) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  qexists `sw` >>
  conj_tac >- (gen_tac >> irule create_proxy_read_prepared_mods >> simp[]) >>
  Cases_on `sop` >> fs[ptrDisciplineTheory.op_taint_def]
QED
