(* The normal RawLog post, framed independently of the LOG path. *)
Theory bodyRawLogDynamicPostFrameMods
Ancestors
  bodyFullRawLogDynamicTailFrame bodyFullRawLogDynamicSequenceFrame
  bodyForRangeScalarFrameMods bodyFullGhostFrame bodyFullPostsMods
  bodyFullHashKeccakFixed exprSimWordArgs exprSimProps stmtSimLogEmit
  bodyFullLogSuffix
  vyperStorageFootprint exprLoweringProps emitHelper emitHelperProps compileEnv
  loweringStateRelDefs loweringPosts bodyPtrDefs ptrDiscipline
  venomState venomInst vyperEvent vyperState
Libs horizonTypeLib

Theorem raw_log_dynamic_post_frame_mods:
  let ev = encode_raw_event_values cx.txn.target vals bs in
  let q = p with vs_inst_idx := LENGTH s2.cs_current_insts in
  let fin = q with <|vs_logs := q.vs_logs ++ [ev];
                     vs_inst_idx := LENGTH sb.cs_current_insts|> in
  expr_post_mods (H : (bool # bytes32 # type_value) list # num list)
    ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  (p with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x p = lookup_var x s /\
    FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)) /\
  tp.t_mem = tn.t_mem /\ tp.t_stor = tn.t_stor /\
  tp.t_trans = tn.t_trans /\ tp.t_imm = tn.t_imm /\
  ghost_kept_at lo cenv ee sm G tn s Gp tp /\
  ghost_inv_at (DF H) 0 d cenv cx ee Gp tp p ==>
  expr_post_mods H ctx func cenv cx (Call ann RawLog es_call dflt)
    es sa sb s0 (ee with logs := ee.logs ++ [ev]) NoneV (Lit 0w) fin /\
  expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) fin /\
  fin.vs_current_bb = sb.cs_current_bb /\
  fin.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func fin /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp fin) /\
  s0.vs_alloca_next <= fin.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx (ee with logs := ee.logs ++ [ev]) Gp tp fin /\
  ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) Gp tp fin /\
  (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) Gp fin) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `fin = p with <|vs_logs := p.vs_logs ++
    [encode_raw_event_values cx.txn.target vals bs]; vs_inst_idx := LENGTH sb.cs_current_insts|>` >>
  `p = s with vs_vars := p.vs_vars` by
    (qpat_assum `(p with vs_vars := _) = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `sm.cs_current_bb = s1.cs_current_bb` by
    (qpat_assum `emit_op MLOAD _ sm = _` (mp_tac o MATCH_MP emit_op_same_blocks) >>
     simp[same_blocks_def]) >>
  `s1.cs_current_bb = s2.cs_current_bb` by
    (qpat_assum `emit_op ADD _ s1 = _` (mp_tac o MATCH_MP emit_op_same_blocks) >>
     simp[same_blocks_def]) >>
  `s2.cs_current_bb = sb.cs_current_bb` by
    (qpat_assum `emit_inst LOG _ _ s2 = _`
      (mp_then Any mp_tac emit_inst_extends) >> simp[]) >>
  `fin.vs_memory = s.vs_memory /\ fin.vs_allocas = s.vs_allocas /\
   fin.vs_alloca_next = s.vs_alloca_next /\ fin.vs_data_section = s.vs_data_section /\
   fin.vs_call_ctx = s.vs_call_ctx /\ fin.vs_accounts = s.vs_accounts /\
   fin.vs_transient = s.vs_transient /\ fin.vs_immutables = s.vs_immutables /\
   fin.vs_current_bb = s.vs_current_bb /\ fin.vs_inst_idx = LENGTH sb.cs_current_insts /\
   (!x. lookup_var x fin = lookup_var x p)` by
    (simp[Abbr `fin`,lookup_var_def] >>
     qpat_assum `p = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x fin = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)` by
    simp[] >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule expr_post_state >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee p` by
    (qpat_assum `p = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     irule (horizonTypeLib.at_horizon_named "H" stmt_state_rel_vars_frame) >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at sm p'` by metis_tac[local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x fin = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) fin` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee p`
      (mp_then Any mp_tac log_append_stmt_state_rel) >>
     simp[Abbr `fin`, stmt_state_rel_inst_idx]) >>
  `storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `storage_well_formed_on cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      (FST H)` by
    (`(ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]).accounts = ee.accounts /\
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]).tStorage = ee.tStorage` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `storage_well_formed_on cx ee (FST H)` mp_tac >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `ghost_inv_at (DF H) 0 d cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      Gp tp fin` by
    (`ghost_inv_at (DF H) 0 d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
        Gp tp fin <=>
      ghost_inv_at (DF H) 0 d cenv cx ee Gp tp fin` by
       simp[ghost_inv_at_def,
            vyperStateTheory.evaluation_state_component_equality] >>
     rw[] >>
     qpat_assum `ghost_inv_at (DF H) 0 d cenv cx ee Gp tp p` mp_tac >>
     simp[ghost_inv_at_logs_idx, Abbr `fin`]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      Gp tp fin` by
    (irule ghost_inv_at_mods_exterior_frame >>
     rpt conj_tac >> simp[Abbr `fin`,
       vyperStateTheory.evaluation_state_component_equality] >> metis_tac[]) >>
  `immutable_frame_mods func cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) fin` by
    (irule immutable_frame_mods_exterior_frame >>
     rpt conj_tac >> simp[Abbr `fin`,
       vyperStateTheory.evaluation_state_component_equality] >> metis_tac[]) >>
  `alloca_history func fin` by
    (irule raw_log_dynamic_sequence_history >>
     qexistsl_tac [`data_op`, `len_op`, `ops`, `ptr_op`, `s`, `s1`, `s2`, `sb`, `sm`] >>
     rpt conj_tac >> simp[Abbr `fin`] >> metis_tac[]) >>
  `ghost_kept_at 0 cenv es sa G0 tn0 s0 G tn` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
      (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ghost_kept_at_def] >> metis_tac[]) >>
  `ghost_kept_at 0 cenv ee sm G tn s Gp tp` by
    (qpat_assum `ghost_kept_at lo cenv ee sm G tn s Gp tp`
      (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ghost_kept_at_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      NoneV (Lit 0w) fin /\
    expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) fin /\
    alloca_history func fin /\
    s0.vs_alloca_next <= fin.vs_alloca_next /\
    ghost_inv_at (DF H) 0 d cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      Gp tp fin /\
    ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt))
      NoneV (Lit 0w) Gp tp fin /\
    (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
      ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) Gp fin) /\
    ghost_kept_at 0 cenv es sa G0 tn0 s0 Gp tp` by
    (unabbrev_all_tac >>
     irule raw_log_dynamic_tail_post_frame >>
     ((reverse (rpt conj_tac)) >-
       (qexistsl_tac [`G`, `data`, `data_op`, `s`, `sm`, `p`, `tn`] >>
        rpt conj_tac >> simp[] >> metis_tac[])) >>
     simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gp tp` by
    (qpat_assum `ghost_kept_at 0 cenv es sa G0 tn0 s0 Gp tp`
      (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[ghost_kept_at_def] >> metis_tac[]) >>
  `((p with vs_inst_idx := LENGTH s2.cs_current_insts) with
      <|vs_logs := (p with vs_inst_idx := LENGTH s2.cs_current_insts).vs_logs ++
          [encode_raw_event_values cx.txn.target vals bs];
        vs_inst_idx := LENGTH sb.cs_current_insts|>) =
    (p with <|vs_logs := p.vs_logs ++
          [encode_raw_event_values cx.txn.target vals bs];
        vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    simp[venomStateTheory.venom_state_component_equality] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  `(p with <|vs_logs := p.vs_logs ++
          [encode_raw_event_values cx.txn.target vals bs];
        vs_inst_idx := LENGTH sb.cs_current_insts|>) = fin` by
    simp[Abbr `fin`] >>
  pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp
      (p with <|vs_logs := p.vs_logs ++
          [encode_raw_event_values cx.txn.target vals bs];
        vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx _ _`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  rewrite_tac[expr_post_mods_def] >>
  rpt conj_tac >> simp[] >> metis_tac[]
QED
