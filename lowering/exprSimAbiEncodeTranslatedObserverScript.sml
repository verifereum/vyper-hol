Theory exprSimAbiEncodeTranslatedObserver
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeTranslatedRelabel exprSimAbiEncodeTranslatedNoBlock
  exprSimAbiEncodeRelabelObserver exprSimAbiEncodeRelabelResources
  exprSimAbiEncodeExecution exprSimAbiEncodeEmptyComplex
  exprSimAbiEncodeWindowRoom exprSimAbiEncodeObliviousSimulation
  exprSimAbiEncodeObliviousContext abiBuiltinEncodeCode abiBuiltinEncodeContext
  abiEncoderCounters abiDecoderContract abiDecoderReentry exprLoweringProps
  compileEnv venomState venomInst words list exprSimAbiEncodeRelabelBoundary
  exprSimAbiGasBridge abiEncoderSourceInvoke abiBuiltinEncodeWord
  exprSimAbiEncodeFramedSuffix exprSimAbiEncodeObserverEntry
  exprSimAbiEncodeStateTransport exprSimAbiEncodeExecFrame

Theorem abi_encode_translated_relabel_observer:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  obs.fn_name = func.fn_name /\ fn_inst_ids_distinct obs /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) obs /\
  sa.cs_blocks <> sb.cs_blocks /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p actual.
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_decode_sim ctx obs (s with vs_current_bb := L) actual /\
    stmt_state_rel ctx func ce cx es' actual /\
    abi_encode_exec_frame obs (s with vs_current_bb := L) actual /\
    LENGTH s.vs_memory <= LENGTH actual.vs_memory /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  drule_all abi_encode_nonword_observer_entry >>
  disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[optionTheory.IS_SOME_EXISTS,
      exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion] >>
  `vyper_to_abi_type (get_tenv cx) (expr_type e) =
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  drule_all abi_encode_nonword_observer_geometry >>
  simp_tac bool_ss [LET_THM] >> disch_then assume_tac >>
  drule_all abi_encode_lower_phase_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `ready`
    (qx_choose_then `len` (qx_choose_then `body_end`
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_encode_translated_relabel_resources >>
  disch_then (qspec_then `L` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `source_word` (qx_choose_then `ct` (qx_choose_then `rv`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_encode_relabel_finish_equation >>
  disch_then (qspec_then `L` assume_tac) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `out = FST ops` SUBST_ALL_TAC >>
  qabbrev_tac `rst = start_relabel L ids sa` >>
  qabbrev_tac `rr = start_swap sa L ids ready` >>
  qabbrev_tac `re = start_swap sa L ids body_end` >>
  qabbrev_tac `rf = start_swap sa L ids sb` >>
  qmatch_asmsub_abbrev_tac `eval_operand op rs = SOME source_word` >>
  `fn_has_code rst rr obs /\ fn_has_code rr re obs /\ fn_has_code re rf obs` by
    (drule_all abi_builtin_encode_code >> strip_tac >> asm_rewrite_tac[]) >>
  `~rs.vs_halted /\ rs.vs_current_bb = rst.cs_current_bb /\
   rs.vs_inst_idx = LENGTH rst.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rf`, Abbr `rs`, Abbr `rst`,
       abi_encode_start_relabel_resources, start_relabel_def] >> asm_rewrite_tac[]) >>
  `rf.cs_current_bb = sb.cs_current_bb /\
   LENGTH rf.cs_current_insts = LENGTH sb.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rf`] >>
     `cs_extends sa sb` by metis_tac[lower_abi_encode_extends] >>
     drule_all abi_encode_start_swap_control >>
     disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >> asm_rewrite_tac[]) >>
  suspend "phases"
QED

Resume abi_encode_translated_relabel_observer[phases]:
  qpat_x_assum `abi_builtin_encode_setup _ _ sa = _` kall_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ ready = _` kall_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ body_end = _` kall_tac >>
  `!x. op = Var x ==> not_fresh_at rst x` by
    (simp_tac (srw_ss()) [Abbr `rst`, start_relabel_def, not_fresh_at_def] >>
     qpat_assum `!x. op = Var x ==> not_fresh_at sa x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def]) >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  `abi_encode_empty_phases_result (ctx with ctx_functions := [obs]) obs
    rst rr re rf ops len mid
    (32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4)))
    p (case mid of NONE => 0 | SOME _ => 32)
    (p+32+(case mid of NONE => 0 | SOME _ => 4))
    (case mid of NONE => 0 | SOME _ => 4) ct rv rs` by
    (Cases_on `val_footprint tv v = 0` >- suspend "empty" >> suspend "positive") >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_empty_phases_result_def]) >>
  suspend "transport"
QED

Resume abi_encode_translated_relabel_observer[positive]:
  `0 < val_footprint tv v` by decide_tac >>
  qpat_assum `0 < val_footprint tv v ==> _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[abi_encode_empty_phases_result_def] >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)
    (abi_encode_framed_phases_open |> SPEC_ALL
     |> Q.INST [`ctx` |-> `ctx with ctx_functions := [obs]`, `func` |-> `obs`]
     |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
     |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
                `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
     |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES]) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room (ctx with ctx_functions := [obs]) obs _`)) >>
  disch_then (drule_at (Pat `fn_has_code re rf _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >- (rewrite_tac[wordsTheory.n2w_w2n] >>
    qpat_assum `enc ct rv = _` (fn eq => rewrite_tac[eq]) >>
    asm_rewrite_tac[] >> simp_tac std_ss [])) >>
  simp_tac bool_ss []
QED

Resume abi_encode_translated_relabel_observer[empty]:
  `(ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc ct rv = []` by
    (qpat_assum `val_footprint tv v = 0 /\ _ \/ _` mp_tac >>
     qpat_assum `val_footprint tv v = 0` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) []) >>
  qpat_assum `val_footprint tv v = 0` (fn zero =>
    qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [zero])) >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)
    (exprSimAbiEncodeEmptyComplexTheory.abi_encode_empty_phases_open |> SPEC_ALL
     |> Q.INST [`ctx` |-> `ctx with ctx_functions := [obs]`, `func` |-> `obs`]
     |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
     |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
                `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
     |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES]) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room (ctx with ctx_functions := [obs]) obs _`)) >>
  disch_then (drule_at (Pat `fn_has_code re rf _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
  qpat_assum `enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av`
    (fn eq => qpat_assum `enc ct rv = []` (fn zero =>
      map_every (fn pat => qpat_x_assum pat
        (assume_tac o PURE_REWRITE_RULE [SYM eq, zero]))
       [`p+32+_+LENGTH _ <= _`,
        `venomMemDefs$regions_disjoint (p+32,_) (_,LENGTH _)`,
        `!inst b sz. MEM inst _ /\ _ ==> _`])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
    (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [] >> metis_tac[])) >>
  simp_tac bool_ss []
QED

Resume abi_encode_translated_relabel_observer[transport]:
  qpat_assum `vyper_to_abi_type _ (expr_type e) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `enc ct rv = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!p. 32 + _ <= _ /\ _` (qspec_then `p` strip_assume_tac) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `rst.cs_next_var <= rr.cs_next_var /\ rst.cs_next_var <= re.cs_next_var` by decide_tac >>
  `stmt_state_rel ctx func ce cx es' actual /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`outsz` |-> `32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4))`]
       (SPEC_ALL abi_encode_phases_caller_state))) >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [Abbr `rst`, Abbr `rs`, start_relabel_def,
       local_region_def, lookup_var_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_sim ctx obs rs actual` by
    (drule_all abi_decode_sim_ctx_no_invoke >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w)` by
    (drule abi_encode_caller_phase_registers >> disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >> asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [Abbr `rst`, Abbr `rs`, start_relabel_def,
       not_fresh_at_def, lookup_var_def,
       abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `(!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row)` by
    (drule_all abi_encode_caller_phase_allocations >>
     disch_then (mp_tac o CONJUNCT1) >> simp_tac (srw_ss()) [Abbr `rs`]) >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> metis_tac[]) >>
  `rst.cs_next_id <= rr.cs_next_id` by
    (qpat_assum `rr.cs_next_id = _` mp_tac >>
     Cases_on `mid` >> simp_tac (srw_ss()) []) >>
  `(!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory)` by
    (drule abi_encode_caller_phase_old_rows >> disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >> asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [Abbr `rst`, Abbr `rs`, start_relabel_def]) >>
  qexistsl [`p`, `actual`] >> simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `Abbrev (rs = _)` (SUBST_ALL_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >>
  qpat_assum `LENGTH _.vs_memory <= LENGTH actual.vs_memory` mp_tac >>
  simp_tac (srw_ss()) []
QED
Finalise abi_encode_translated_relabel_observer
