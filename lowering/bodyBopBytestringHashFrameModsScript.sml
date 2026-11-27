(* Read-only linked frame on the fixed dynamic bytestring hash run. *)
Theory bodyBopBytestringHashFrameMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPostsMods
  bodyPtrBopHashSuffix bodyFullHashKeccakFixed bodyMemBopRestWordPath
  bytestringHashProps exprLoweringProps exprSimWordArgs exprSimProps
  bodyPtrDefs freshWrites loweringStateRelDefs compileEnv fragExec
  venomState list finite_map pred_set

Theorem bytestring_hash_history[local]:
  compile_bytestring_hash (Var p) cb = (h,sz) /\
  fn_has_code cb sz func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = cb.cs_current_bb /\
  t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  alloca_history func t /\ alloca_inv t /\
  run_inst_seq (emitted_insts cb sz) t = OK raw ==>
  alloca_history func (raw with vs_inst_idx := LENGTH sz.cs_current_insts)
Proof
  strip_tac >> drule_then strip_assume_tac compile_bytestring_hash_shape >>
  irule emitted_alloca_history >> simp[] >>
  qexistsl [`emitted_insts cb sz`,`t`,`cb`] >> simp[] >>
  fs[EVERY_MEM]
QED

Theorem bytestring_hash_frame_mods:
  lower_value compile_expr cenv (expr_type e) e sa = (Var p,cb) /\
  compile_bytestring_hash (Var p) cb = (h,sz) /\ not_fresh_at cb p /\
  fn_has_code cb sz func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ~t.vs_halted /\ t.vs_current_bb = cb.cs_current_bb /\
  t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  expr_post_mods H ctx func cenv cx e es sa cb s ee v (Var p) t /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s G tn /\
  lookup_var p t = SOME w /\
  run_inst_seq (emitted_insts cb sz) t = OK raw /\
  u = (raw with vs_inst_idx := LENGTH sz.cs_current_insts) /\
  (!x. not_fresh_at cb x ==> lookup_var x raw = lookup_var x t /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  stmt_state_rel H ctx func cenv cx ee u /\
  immutable_frame_mods func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' u /\
  ghost_kept_at lo cenv es sa G0 tn0 s G' tn' /\
  ~u.vs_halted /\ u.vs_current_bb = sz.cs_current_bb /\
  u.vs_inst_idx = LENGTH sz.cs_current_insts /\
  alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  wb_frame cenv es ee sa s u /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s u)
Proof
  strip_tac >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_state >>
  drule_then assume_tac rest_word_state_alloca_inv >>
  drule_then strip_assume_tac (CONJUNCT2 compile_expr_grows) >>
  drule_all_then assume_tac local_ptrs_reserved_next_var >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (qpat_assum `u = _` SUBST1_TAC >>
     irule bop_hash_compile_state_rel >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
     goal_assum (drule_at (Pat `compile_bytestring_hash _ _ = _`)) >>
     goal_assum (drule_at (Pat `lookup_var _ _ = SOME _`)) >> simp[]) >>
  `alloca_history func u` by
    (qpat_assum `u = _` SUBST1_TAC >>
     drule_all_then ACCEPT_TAC bytestring_hash_history) >>
  drule_all_then assume_tac bop_hash_compile_readonly >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\ u.vs_call_ctx = t.vs_call_ctx /\
   u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
   u.vs_immutables = t.vs_immutables /\ u.vs_data_section = t.vs_data_section /\
   u.vs_current_bb = t.vs_current_bb /\ u.vs_halted = t.vs_halted` by
    (qpat_assum `raw with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at cb x` by (irule freshWritesTheory.not_fresh_at_mono >>
       qexists `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at cb x ==> _` (qspec_then `x` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     fs[lookup_var_def]) >>
  drule_then strip_assume_tac bop_hash_compile_layout >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `u.vs_inst_idx = LENGTH sz.cs_current_insts` by simp[] >>
  qpat_x_assum `u = _` kall_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by
    (gen_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  simp[] >> conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`t`,`sa`] >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`t`,`sa`,`tn`] >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
      gen_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac
  >- (`wb_frame cenv es ee sa s t` by drule_then ACCEPT_TAC expr_post_frame >>
      irule wb_frame_readonly_tail >> qexistsl [`sa`,`t`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t`
        (qspec_then `z` mp_tac) >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `t` >> simp[] >>
  drule_all_then ACCEPT_TAC expr_post_pure_frame
QED
