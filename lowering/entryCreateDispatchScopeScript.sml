(* The prepared CREATE has no operand evaluations left. Attach scope to the
   very dispatch and result-check witnesses used by the full simulation. *)
Theory entryCreateDispatchScope
Ancestors
  bodyFullCreateHeld entryCreatePathScope entryCreateCompletedCut
  createSizeCutRegion createSizeCutCode createSizeResultCheckCode createResultTail createSizeEdgePC
  createMarkedPath createSizePrefixReplay createExprSizeExitDefs
  builtinCreate compileEnv emitHelper fragExec fragGasOrigin fragGasOriginPtr
  gasOutcomeFull gasStorage gasSummary vyperStorageFootprint
  venomExecSemantics venomExecProofs venomInst venomState gasEvents
  exprSimDefs exprSimMemDefs loweringPosts vyperCreate vyperInterpreter
  words list rich_list relation arithmetic vfmConstants

Theorem dispatch_closed_code[local]:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) ==>
  create_cut_code {} sm sb
Proof
  strip_tac >>
  `create_cut_code {} sm (SND (compile_create_dispatch codep len amount sop rof sm))`
    suffices_by simp[] >>
  Cases_on `sop` >> simp[NoAsms,compile_create_dispatch_def] >>
  irule create_cut_code_bind >> simp[create_result_check_cut_code] >>
  irule create_cut_code_emit_op >> simp[create_cut_targets_def]
QED

Theorem dispatch_start_region[local]:
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  create_cut_region sm sb s
Proof
  metis_tac[create_cut_region_rules]
QED

Theorem dispatch_edge_scope[local]:
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_cut_region sm sb p /\
  (p.vs_current_bb = sb.cs_current_bb ==> p.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  gas_origin_edge mem explicit ctx f p marks (OK q) ==>
  create_expr_prefix sm sb explicit ctx f p marks q /\ create_cut_region sm sb q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_cut_region_rules >> strip_tac >>
  `gas_origin_edge F explicit ctx f p marks (OK q)` by
    (qpat_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_origin_edge_def] >> metis_tac[]) >>
  `?bb i. lookup_block p.vs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb p.vs_inst_idx = SOME i` by
    (qpat_assum `gas_origin_edge F _ _ _ _ _ _` (mp_tac o REWRITE_RULE[gas_origin_edge_def]) >>
     metis_tac[]) >>
  reverse conj_tac
  >- metis_tac[venomExecProofsTheory.lookup_block_MEM, ZERO_LESS_EQ] >>
  `create_marked_edge (create_prefix_step sm sb explicit ctx f) (p,[]) (q,marks)` by
    (simp[create_marked_edge_def, create_prefix_step_def] >> metis_tac[]) >>
  metis_tac[create_expr_prefix_marked, RTC_SINGLE]
QED

(* A terminal path that stays in a region disjoint from the continuation. *)
Theorem dispatch_terminal_region[local]:
  !mem explicit ctx f s marks r. gas_origin_path mem explicit ctx f s marks r ==>
  mem /\ exit_result r /\ P s /\
  (!p. P p ==> p.vs_current_bb <> sb.cs_current_bb \/ p.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  (!p m q. P p /\ gas_origin_edge T explicit ctx f p m (OK q) ==>
           P q /\ create_expr_prefix sm sb explicit ctx f p m q) ==>
  ?left p last. create_expr_prefix sm sb explicit ctx f s left p /\ P p /\
                 marks = left ++ last /\ gas_origin_edge T explicit ctx f p last r
Proof
  ho_match_mp_tac gas_origin_path_ind >> simp[exit_result_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      rename1 `gas_origin_edge T explicit ctx f s head (OK mid)` >>
      `P mid /\ create_expr_prefix sm sb explicit ctx f s head mid` by metis_tac[] >>
      qpat_x_assum `_ ==> ?left p last. _` mp_tac >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      metis_tac[create_expr_prefix_append, APPEND_ASSOC]) >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`[]`,`s`,`marks`] >> simp[]
QED

Theorem dispatch_terminal_scope[local]:
  gas_origin_path T explicit ctx f s marks r /\ exit_result r /\ P s /\
  (!p. P p ==> p.vs_current_bb <> sb.cs_current_bb \/ p.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  (!p m q. P p /\ gas_origin_edge T explicit ctx f p m (OK q) ==>
           P q /\ create_expr_prefix sm sb explicit ctx f p m q) ==>
  create_operand_full_scope sm sb explicit ctx f s marks r
Proof
  metis_tac[dispatch_terminal_region, create_operand_full_scope_terminal]
QED

(* The result JNZ has a concrete successor. For failure the native path
   supplies this edge; for a nonzero result it is the jump to the exit. *)
Theorem dispatch_result_jump_edge[local]:
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME j /\
  j.inst_opcode = JNZ /\ j.inst_operands = [op; Label yes; Label no] /\
  eval_operand op u = SOME w /\ ~u.vs_halted ==>
  gas_origin_edge F explicit ctx f u [] (OK (jump_to (if w = 0w then no else yes) u))
Proof
  strip_tac >> simp[gas_origin_edge_def] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, gas_events_step_def,
       is_terminator_def] >> metis_tac[]
QED

Theorem dispatch_result_jump_pc[local]:
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME j /\
  j.inst_opcode = JNZ /\ j.inst_operands = [op; Label yes; Label no] /\
  eval_operand op u = SOME w /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_edge mem explicit ctx f u marks (OK v) ==>
  v.vs_inst_idx = 0 /\ v.vs_current_bb = (if w = 0w then no else yes)
Proof
  strip_tac >>
  `gas_origin_edge F explicit ctx f u marks (OK v)` by
    (qpat_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_origin_edge_def] >> metis_tac[]) >>
  drule_all create_ok_edge_pc >> Cases_on `w = 0w` >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, jump_to_def] >>
  metis_tac[venomExecProofsTheory.lookup_block_MEM]
QED

Theorem dispatch_result_jump_not_terminal[local]:
  lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME j /\
  j.inst_opcode = JNZ /\ j.inst_operands = [op; Label yes; Label no] /\
  eval_operand op u = SOME w /\ ~u.vs_halted /\
  gas_origin_edge T explicit ctx f u marks r ==> ~exit_result r
Proof
  Cases_on `w = 0w` >> rw[gas_origin_edge_def] >> gvs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, jump_to_def, exit_result_def]
QED

Theorem dispatch_result_fail_scope[local]:
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  create_cut_region sm sb u /\
  (u.vs_current_bb <> sb.cs_current_bb \/ u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block u.vs_current_bb f.fn_blocks = SOME cb /\
  get_instruction cb u.vs_inst_idx = SOME j /\
  j.inst_opcode = JNZ /\ j.inst_operands = [op;Label sb.cs_current_bb;Label failure_lbl] /\
  eval_operand op u = SOME 0w /\ ~u.vs_halted /\
  failure_lbl <> sb.cs_current_bb /\ lookup_block failure_lbl f.fn_blocks = SOME fb /\
  MAP (\i. i.inst_opcode) fb.bb_instructions = [RETURNDATASIZE;ALLOCA;RETURNDATACOPY;REVERT] /\
  exit_result r /\ gas_origin_path T explicit ctx f u [] r ==>
  create_operand_full_scope sm sb explicit ctx f u [] r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE[gas_origin_path_cases]) >> simp[] >>
  strip_tac >> gvs[exit_result_def]
  >- (rename1 `gas_origin_edge T explicit ctx f u [] (OK mid)` >>
      drule_all dispatch_result_jump_pc >> simp[] >> strip_tac >>
      drule_all dispatch_edge_scope >> strip_tac >>
      `create_operand_full_scope sm sb explicit ctx f mid [] r` by
        (irule dispatch_terminal_scope >> simp[] >>
         qexists_tac `\p. create_cut_region sm sb p /\ p.vs_current_bb = failure_lbl /\ p.vs_inst_idx < 4` >>
         simp[] >> rpt strip_tac >>
         `(p.vs_current_bb = sb.cs_current_bb ==> p.vs_inst_idx <> LENGTH sb.cs_current_insts)`
           by simp[] >>
         drule_all dispatch_edge_scope >> strip_tac >> simp[] >>
         `gas_origin_edge F explicit ctx f p m (OK q)` by
           (qpat_assum `gas_origin_edge T _ _ _ _ _ _` mp_tac >>
            pure_rewrite_tac[gas_origin_edge_def] >> metis_tac[]) >>
         metis_tac[create_result_tail_fail_step]) >>
      Cases_on `r` >> gvs[exit_result_def, create_operand_full_scope_def] >>
      metis_tac[create_expr_prefix_append, APPEND]) >>
  metis_tac[dispatch_result_jump_not_terminal]
QED

Theorem dispatch_consumed_scope[local]:
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  create_cut_region sm sb s /\
  (s.vs_current_bb = sb.cs_current_bb ==> s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  compile_check_create_result op rof mid = (result,sb) /\ fn_has_code mid sb f /\
  u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
  u.vs_inst_idx = SUC s.vs_inst_idx /\ ~u.vs_halted /\ eval_operand op u = SOME w /\
  gas_origin_edge T explicit ctx f s [] (OK u) /\
  (if rof /\ w = 0w then exit_result r /\ gas_origin_path T explicit ctx f u [] r
   else r = OK (if rof then jump_to sb.cs_current_bb u else u)) ==>
  create_operand_full_scope sm sb explicit ctx f s [] r
Proof
  strip_tac >> drule_all dispatch_edge_scope >> strip_tac >>
  Cases_on `rof`
  >- (gvs[] >> drule_all create_result_check_layout_distinct >> strip_tac >>
      `u.vs_inst_idx <> LENGTH sb.cs_current_insts` by
        (strip_tac >> gvs[]) >>
      `get_instruction cb u.vs_inst_idx = SOME j` by
        simp[get_instruction_def, EL_APPEND_EQN] >>
      Cases_on `w = 0w`
      >- (fs[] >>
          rename1 `j.inst_operands = [op; Label sb.cs_current_bb; Label failure_lbl]` >>
          `create_operand_full_scope sm sb explicit ctx f u [] r` by
            (irule dispatch_result_fail_scope >> goal_assum (drule_at Any) >> fs[] >>
             qexistsl_tac [`failure_lbl`,`fb`,`j`,`op`] >>
             simp[get_instruction_def, EL_APPEND_EQN]) >>
          Cases_on `r` >> gvs[exit_result_def,create_operand_full_scope_def] >>
          metis_tac[create_expr_prefix_append, APPEND]) >>
      fs[] >>
      rename1 `j.inst_operands = [op; Label sb.cs_current_bb; Label failure_lbl]` >>
      qabbrev_tac `z = jump_to sb.cs_current_bb u` >>
      `gas_origin_edge F explicit ctx f u [] (OK z)` by
        (simp[Abbr `z`] >>
         `jump_to sb.cs_current_bb u = jump_to (if w = 0w then failure_lbl else sb.cs_current_bb) u`
           by simp[] >>
         pop_assum SUBST1_TAC >> irule dispatch_result_jump_edge >>
         metis_tac[]) >>
      `create_expr_prefix sm sb explicit ctx f u [] z` by
        (qpat_assum `gas_origin_edge F _ _ _ _ _ _`
           (mp_then Any (qspecl_then [`sm`,`sb`] mp_tac) dispatch_edge_scope) >> simp[]) >>
      `create_expr_prefix sm sb explicit ctx f s [] z` by
        metis_tac[create_expr_prefix_append, APPEND] >>
      simp[create_operand_full_scope_def] >> simp[Abbr `z`, jump_to_def]) >>
  gvs[compile_check_create_result_def, comp_return_def, create_operand_full_scope_def]
QED

Theorem dispatch_witness_scoped[local]:
  ~s.vs_halted /\
  create_dispatch_prepared_outcome (DF,lo,explicit,ctx,func,PG) cx st0 source
    (ee,s,G,tn) Q R (\r. create_operand_full_scope sm sb explicit ctx func s [] r) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 sm sb source
    (ee,s,G,tn) Q R
Proof
  simp[create_dispatch_prepared_outcome_def] >> strip_tac >>
  rename1 `!tail. source (ee with gas_obs := tail) = (res,ef with gas_obs := tail)` >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> simp[] >>
  Cases_on `storage_trace_domain cx st0 ef.storage_trace`
  >- (disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  disj1_tac >> simp[gas_bad_storage_at_def,create_operand_focus_scope_def] >>
  conj_tac >- (qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[storage_trace_domain_def, gas_origin_ptr_focus_rules, gas_origin_ptr_path_rules]
QED

(* The dispatch entry is before the enclosing continuation. This is a
   compile-site PC check, not an assumption that the CREATE will succeed. *)
Theorem create_dispatch_scoped_outcome:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!b. MEM b func.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
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
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 sm sb
    source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dispatch_closed_code >> strip_tac >>
  `create_cut_region sm sb s` by (irule dispatch_start_region >> metis_tac[]) >>
  irule dispatch_witness_scoped >> simp[] >>
  irule create_dispatch_outcome_witness >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule (SIMP_RULE (srw_ss()) []
        (Q.INST [`left` |-> `[]`, `last` |-> `[]`] create_operand_full_scope_terminal)) >>
      simp[] >> qexists_tac `s` >> simp[] >> metis_tac[]) >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> rpt (goal_assum (drule_at Any)) >>
  simp[] >> rpt strip_tac >> irule dispatch_consumed_scope >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_assum `compile_check_create_result _ _ _ = _` (irule_at Any) >>
  qpat_assum `gas_origin_edge T _ _ _ _ _ (OK _)` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
