Theory bodyFullBopInLiteralTail
Ancestors
  bodyFullHashKeccakFixed
  bodyPtrBopInLiteralTyped bodyPtrBopInScalarTransport bodyPtrBopInLiteralRun
  fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeqPtr gasOutcomeFullCompose bodySimFull
  varsExt freshWrites instIdxIndep fragExecMem instMemFrontier memSafeRun
  exprSimWordArgs exprSimProps exprSimMemDefs exprLoweringProps
  bodyPtrSignedConvertSourceFrame bodyFullUnwrapRun allocaHistoryFragment
  loweringSlice valueEncoding vyperAST compileEnv loweringPosts
  bodyFullGhostFrame bodyPtrDefs exprSimBopInLiteralWord
  vyperState loweringStateRelDefs fragExec
  list finite_map venomState venomInst venomExecSemantics

(* The scalar suffix fixes its value and ghost endpoints before the dead
   region (and therefore before the source-storage horizon) is chosen. *)
Theorem bop_in_literal_clean_uniform:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sm sb) (drop_fresh sm s) = OK u /\
    eval_operand dst u = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
    (!D k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb)
      (drop_fresh sm s with vs_inst_idx := k) G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all literal_typed_clean_run >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> simp[] >>
  map_every qx_gen_tac [`D`,`k`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all literal_typed_clean_run >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `G' = G'' /\ tn' = tn''` by
    (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  gvs[]
QED

Theorem bop_in_literal_actual_uniform:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sm sb) s = OK u /\
    eval_operand dst u = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
    (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb) s G' tn') /\
    op_prov G' dst = NONE /\ op_taint tn' dst = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (u with vs_vars := s.vs_vars) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_in_literal_clean_uniform >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[]
     >- (drule literal_in_code_shape >> simp[]) >>
     drule literal_notin_code_shape >> simp[]) >>
  `vars_ext (drop_fresh sm s) s` by simp[vars_ext_drop_fresh] >>
  `inst_seq_ptr ARB 0 ctx fn PG G tn (emitted_insts sm sb)
     (drop_fresh sm s) G' tn'` by
    (qpat_x_assum `!D k. _` (qspecl_then [`ARB`,`(drop_fresh sm s).vs_inst_idx`] mp_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (drop_fresh sm s)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[drop_fresh_def, ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all scalar_inst_seq_ptr_vars_ext >> strip_tac >>
  qexistsl_tac [`u1`,`G'`,`tn'`] >> simp[] >>
  `eval_operand dst u1 = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs))` by
    (qpat_assum `vars_ext u u1` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
     drule eval_operand_vars_ext >> disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]) >> simp[] >>
  conj_tac >- (gen_tac >> irule scalar_sequence_check_vars_ext >>
    simp[] >> qexists_tac `drop_fresh sm s` >> simp[] >>
    qpat_x_assum `!D k. _` (qspecl_then [`D`,`(drop_fresh sm s).vs_inst_idx`] mp_tac) >> simp[]) >>
  irule membership_scalar_run_frame >> qexists_tac `emitted_insts sm sb` >> simp[] >>
  qpat_x_assum `EVERY _ (emitted_insts sm sb)` mp_tac >> simp[EVERY_MEM]
QED

Theorem bop_in_literal_origin_uniform:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (dst,sb) /\
  ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sm sb) s = OK u /\
  (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb) s G' tn') ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)),G',tn')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[]
     >- (drule literal_in_code >> simp[]) >>
     drule literal_notin_code >> simp[]) >>
  gen_tac >> irule (cj 1 run_inst_seq_origin_ptr_lift) >>
  simp[] >>
  conj_tac
  >- (disch_tac >> rpt gen_tac >> strip_tac >>
      irule dalloca_no_wrap_non_dalloca >>
      qpat_x_assum `EVERY _ (emitted_insts sm sb)` mp_tac >>
      simp[EVERY_APPEND] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `EVERY _ _` mp_tac >>
      simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  irule run_inst_seq_mem_ok_every >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  simp[EVERY_MEM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[inst_dload_in_section_def] >>
  match_mp_tac below_frontier_no_ranges >> simp[]
QED

Theorem bop_in_literal_suffix_post:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sb) s = OK u /\
  z = (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (u with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
  eval_operand op z = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
  sa.cs_next_var <= sm.cs_next_var /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
  storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
  wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
  (~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
    pure_frame cenv func es sa s0 s) ==>
  expr_post H ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
    es sa sb s0 (ee with gas_obs := [])
    (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op z /\
  expr_store_bound cx (BaseT BoolT)
    (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks sm sb /\
    EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[]
     >- (drule literal_in_code >> simp[]) >>
     drule literal_notin_code >> simp[]) >>
  `z = s with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|>` by
    gvs[venom_state_component_equality] >>
  `stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) z` by
    (irule stmt_state_rel_readonly_vars_pc >> metis_tac[]) >>
  `wb_frame cenv es (ee with gas_obs := []) sa s0 z` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`,`s`] >>
     gvs[venom_state_component_equality]) >>
  `~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
     pure_frame cenv func es sa s0 z` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >>
     gvs[venom_state_component_equality]) >>
  `alloca_history func z` by
    (qpat_assum `z = u with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
     irule emitted_alloca_history >>
     simp[] >> qexistsl_tac [`emitted_insts sm sb`,`s`,`sm`] >>
     simp[] >> conj_tac >- gvs[stmt_state_rel_def] >>
     conj_tac >- gvs[same_blocks_def] >>
     qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  conj_tac
  >- (irule expr_post_word_intro >>
      simp[expr_type_def, is_word_type_def, word_value_def, val_to_w256_def] >>
      Cases_on `if bop = In then MEM v vs else ~MEM v vs` >>
      gvs[bool_to_word_def, expr_has_effect_thm, EVERY_MEM, EXISTS_MEM]) >>
  simp[expr_store_bound_word, is_word_type_def] >>
  gvs[same_blocks_def, venom_state_component_equality]
QED

Theorem bop_in_literal_suffix_ghost:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_inv_at D lo d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  run_inst_seq (emitted_insts sm sb) s = OK u /\
  (u with vs_vars := s.vs_vars) = s /\
  (tn' with t_var := tn.t_var) = tn /\
  (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
       op_taint tn' (Var p) = op_taint tn (Var p)) /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  z = (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)) ==>
  ghost_inv_at D lo d cenv cx (ee with gas_obs := []) G' tn' z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
  ptr_val_ok cx (BaseT BoolT)
    (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op G' tn' z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `writes_fresh sm (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[] >>
     metis_tac[literal_membership_straight, straight_fresh_def]) >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!p. not_fresh_at sa p ==>
     lookup_var p z = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (qpat_x_assum `tn' with t_var := _ = tn` mp_tac >>
     Cases_on `tn'` >> Cases_on `tn` >>
     simp[ptrDisciplineTheory.recordtype_taint_seldef_t_var_fupd_def]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`,`ee with gas_obs := []`,`s`,`sa`,`tn`] >>
      gvs[venom_state_component_equality]) >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
      gvs[] >> metis_tac[pred_setTheory.SUBSET_REFL]) >>
  simp[ptr_val_ok_def, is_word_type_def]
QED

Theorem bop_in_literal_continuation_full_exit:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
    (~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
      pure_frame cenv func es sa s0 s)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (return (BoolV (if bop = In then MEM v vs else ~MEM v vs))) (ee,s,G,tn)
    (\H res ee G tn z. ?v. res = INL v /\
      expr_post H ctx func cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
        es sa sb s0 ee v op z /\
      expr_store_bound cx (BaseT BoolT) v op z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx (BaseT BoolT) v op G tn z /\
      (~is_word_type (BaseT BoolT) ==>
       ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop bop)
         [e1; Builtin a (MakeArray t n) elems]) op G z) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_in_literal_actual_uniform >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   same_blocks sm sb /\ writes_fresh sm (emitted_insts sm sb)` by
    (Cases_on `bop = In` >> gvs[] >>
     metis_tac[literal_membership_straight, straight_fresh_def, same_blocks_def]) >>
  qabbrev_tac `z = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `z = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)` by
    simp[Abbr `z`] >>
  `!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s` by
    (drule_all run_inst_seq_writes_fresh >> strip_tac >>
     simp[Abbr `z`, lookup_var_def]) >>
  `eval_operand op z = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs))` by
    simp[Abbr `z`, eval_operand_def, lookup_var_def] >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`,`ee`,`[]`,
    `OK z`,`INL (BoolV (if bop = In then MEM v vs else ~MEM v vs))`,`tn'`] >>
  simp[return_def] >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' z /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
   ptr_val_ok cx (BaseT BoolT)
     (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op G' tn' z` by
    (irule bop_in_literal_suffix_ghost >> metis_tac[]) >>
  `expr_post H ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
    es sa sb s0 (ee with gas_obs := [])
    (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op z /\
   expr_store_bound cx (BaseT BoolT)
    (BoolV (if bop = In then MEM v vs else ~MEM v vs)) op z /\
   z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
   alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next` by
    (irule bop_in_literal_suffix_post >> metis_tac[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn')` by
    (qpat_assum `z = u with vs_inst_idx := s.vs_inst_idx + _`
       (fn th => once_rewrite_tac[th]) >>
     irule bop_in_literal_origin_uniform >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- gvs[ghost_inv_at_def] >>
     gvs[fn_has_code_def, same_blocks_def] >>
     qpat_x_assum `isPREFIX (_ ++ _) _`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     simp[DROP_APPEND, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    first_assum (ACCEPT_TAC o MATCH_MP
      bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
      CONJUNCT1 o REWRITE_RULE [expr_post_def]) >>
  gvs[is_word_type_def] >> gvs[Abbr `z`]
QED

Theorem bop_in_literal_continuation_full:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\
  EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
  ~ctx_has_dalloca ctx /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
    (~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
      pure_frame cenv func es sa s0 s)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (return (BoolV (if bop = In then MEM v vs else ~MEM v vs))) (ee,s,G,tn)
    (\H res ee G tn z. ?v. res = INL v /\
      expr_post H ctx func cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
        es sa sb s0 ee v op z /\
      expr_store_bound cx (BaseT BoolT) v op z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx (BaseT BoolT) v op G tn z /\
      (~is_word_type (BaseT BoolT) ==>
       ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop bop)
         [e1; Builtin a (MakeArray t n) elems]) op G z) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `~ctx_has_dalloca ctx`
    (fn static => irule (SIMP_RULE bool_ss [static]
      (SPEC_ALL bop_in_literal_continuation_full_exit))) >> metis_tac[]
QED
