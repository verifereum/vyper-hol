(* Dispatch a prepared initcode buffer, with or without an outcome to consume. *)
Theory bodyCreateDispatchMods
Ancestors
  bodyCreateDispatchAbortMods bodyCreateDispatchAdoptMods
  bodyFullPostsMods gasOutcomeFullMods builtinCreate vfmConstants
  bodyFullShadowBodyInv bodyPtrDefs loweringPosts loweringStateRelDefs
  exprSimDefs compileEnv fragExec ptrDiscipline allocaHistory
  venomState venomInst venomMemDefs vyperState vyperCreate vyperStorageFootprint words

Theorem create_dispatch_outcome_full_mods:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
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
  outcomes_accounts_typed ee.outcomes /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  read_memory (w2n pv) (w2n sz) s = initcode /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0 source (ee,s,G,tn)
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
  Cases_on `w2n sz > 2 * max_code_size \/ cx.txn.is_static \/ s.vs_outcomes = []`
  >- (drule create_dispatch_preconsume_mods >> disch_then irule >>
      rpt conj_tac >> rpt HINT_EXISTS_TAC >> asm_rewrite_tac[] >>
      qexists_tac `d` >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `~(_ \/ _)` mp_tac >>
  simp_tac bool_ss [DE_MORGAN_THM, arithmeticTheory.GREATER_DEF,
                   arithmeticTheory.NOT_LESS] >> strip_tac >>
  drule create_dispatch_consume_mods >> disch_then irule >>
  rpt conj_tac >> rpt HINT_EXISTS_TAC >> asm_rewrite_tac[]
QED
