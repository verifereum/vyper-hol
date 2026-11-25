(* The scalar membership tail neither observes source gas nor writes memory.
   Its machine and ghost endpoints are independent of the storage horizon. *)
Theory bodyMembershipLiteralSuffixMods
Ancestors
  bodyFullBopInLiteralTail bodyForRangeScalarFrameMods stateRelProj
  gasOutcomeFullPostMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrBopInLiteralRun bodyPtrSignedConvertSourceFrame exprSimWordArgs
  bodyFullUnwrapRun bodyFullHashKeccakFixed exprSimBopInLiteralWord
  exprSimProps freshWrites exprLoweringProps exprSimMemDefs loweringPosts
  bodyPtrDefs fragExec compileEnv vyperState vyperAST vyperInterpreter
  loweringStateRelDefs venomState venomInst ptrDiscipline rich_list finite_map list
  loweringSlice venomExecSemantics valueEncoding

Triviality literal_suffix_layout:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  writes_fresh sm (emitted_insts sm sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  Cases_on `bop = In` >> simp[] >> strip_tac >> gvs[] >>
  FIRST [drule_then strip_assume_tac literal_in_code,
         drule_then strip_assume_tac literal_notin_code] >>
  `writes_fresh sm (emitted_insts sm sb)` by
    metis_tac[literal_membership_straight, straight_fresh_def] >>
  fs[same_blocks_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[is_terminator_def]
QED

Triviality literal_suffix_prefix:
  fn_has_code sm sb func /\ sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[fn_has_code_def] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `isPREFIX _ _` (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `bb.bb_instructions = sm.cs_current_insts ++ (emitted_insts sm sb ++ l)` by
    metis_tac[APPEND_ASSOC] >>
  qpat_x_assum `bb.bb_instructions = sb.cs_current_insts ++ l` kall_tac >>
  fs[IS_PREFIX_APPEND] >> qexists_tac `l` >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Triviality literal_suffix_word_post:
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\ wb_frame cenv es ee sa s0 s /\
  (~expr_has_effect (Builtin (BaseT BoolT) (Bop bop)
      [e1; Builtin a (MakeArray t n) elems]) ==> pure_frame cenv func es sa s0 s) /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  z = s with <|vs_vars := vars; vs_inst_idx := k|> /\
  (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s) /\
  eval_operand op z = SOME (bool_to_word b) ==>
  expr_post_mods H ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
    es sa sb s0 ee (BoolV b) op z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel H ctx func cenv cx ee z` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  simp[expr_post_mods_def] >> conj_tac
  >- (irule expr_post_word_intro >>
      simp[expr_type_def, is_word_type_def, word_value_def] >>
      conj_tac >- (Cases_on `b` >> gvs[bool_to_word_def, val_to_w256_def]) >>
      conj_tac
      >- (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> fs[]) >>
      conj_tac
      >- (irule wb_frame_readonly_tail >>
          qpat_assum `wb_frame _ _ _ _ _ s` (irule_at Any) >>
          qexists_tac `sm` >> gvs[] >> rpt strip_tac >>
          qpat_assum `!p. not_fresh_at sm p ==> _` drule >> simp[]) >>
      gvs[]) >>
  irule immutable_frame_mods_exterior_frame >>
  qpat_assum `immutable_frame_mods _ _ _ ee s` (irule_at Any) >>
  qexists_tac `sm` >> gvs[]
QED

Theorem bop_in_literal_suffix_mods:
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
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s /\
    immutable_frame_mods func cenv cx (ee with gas_obs := []) s /\
    storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx (ee with gas_obs := []) G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    wb_frame cenv es (ee with gas_obs := []) sa s0 s /\
    (~expr_has_effect (Builtin (BaseT BoolT) (Bop bop)
       [e1; Builtin a (MakeArray t n) elems]) ==> pure_frame cenv func es sa s0 s)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (return (BoolV (if bop = In then MEM v vs else ~MEM v vs))) (ee,s,G,tn)
    (\H res ee G tn z. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
        es sa sb s0 ee v op z /\
      expr_store_bound cx (BaseT BoolT) v op z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn z /\
      ptr_val_ok cx (BaseT BoolT) v op G tn z /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac literal_suffix_layout >>
  drule_all_then strip_assume_tac literal_suffix_prefix >>
  drule_all bop_in_literal_actual_uniform >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  drule_all_then strip_assume_tac run_inst_seq_writes_fresh >>
  qabbrev_tac `z = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `z = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)` by
    simp[Abbr `z`] >>
  `z = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qunabbrev_tac `z` >> qpat_assum `u = s with vs_vars := _`
       (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s` by
    simp[Abbr `z`, lookup_var_def] >>
  qabbrev_tac `b = if bop = In then MEM v vs else ~MEM v vs` >>
  `eval_operand op z = SOME (bool_to_word b)` by
    (simp[Abbr `z`] >> simp[eval_operand_def, lookup_var_def]) >>
  `local_ptrs_reserved cenv sm` by
    (fs[local_ptrs_reserved_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!p. not_fresh_at sa p ==>
    lookup_var p z = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> `not_fresh_at sm p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (rpt conj_tac >>
     qpat_assum `tn' with t_var := _ = tn` (fn th => once_rewrite_tac[SYM th]) >> simp[]) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`,`ee`,`INL (BoolV b)`,`z`,`tn'`] >>
  simp[NoAsms, return_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (`allocas_from lo s` by
        fs[ghost_inv_at_mods_def] >>
      qpat_assum `z = u with vs_inst_idx := s.vs_inst_idx + _`
        (fn th => pure_once_rewrite_tac[th]) >>
      irule bop_in_literal_origin_uniform >>
      qpat_assum `(if _ then compile_list_membership_in _ _ else _) _ = _`
        (irule_at Any) >> qexists_tac `bb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func z` by
    (qunabbrev_tac `z` >> irule emitted_alloca_history >>
     qpat_assum `fn_has_code sm sb func` (irule_at Any) >>
     qpat_assum `run_inst_seq _ s = OK u` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_post_mods H ctx func cenv cx
    (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
    es sa sb s0 (ee with gas_obs := []) (BoolV b) op z` by
    (irule literal_suffix_word_post >>
     qpat_assum `z = s with <|vs_vars := _; vs_inst_idx := _|>` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' z` by
    (irule ghost_inv_at_mods_exterior_frame >>
     qexistsl_tac [`G`,`ee with gas_obs := []`,`s`,`sa`,`tn`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]) >>
  simp[expr_store_bound_word, ptr_val_ok_def, is_word_type_def, allocas_below_fmp_def] >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[allocas_below_fmp_def] >> metis_tac[]
QED
