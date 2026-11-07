Theory exprSimAbiEncodeRelabelObserver
Ancestors
  exprSimAbiEncodeRelabelResources exprSimAbiEncodeExecution
  exprSimAbiEncodeEmptyExecution exprSimAbiEncodeWindowRoom
  exprSimAbiEncodeObliviousSimulation exprSimAbiEncodeObliviousContext
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiEncoderCounters abiEncoderAdmissible
  abiDecoderContract abiDecoderReentry exprLoweringProps compileEnv
  venomState venomInst words list
  exprSimAbiEncodeRelabelBoundary exprSimAbiGasBridge abiEncoderSourceInvoke
  abiBuiltinEncodeWord exprSimAbiEncodeFramedSuffix exprSimAbiEncodeEmptyFramed
  exprSimAbiEncodeObserverEntry exprSimAbiEncodeStateTransport exprSimAbiEncodeExecFrame

Theorem abi_encode_finish_entry_action[local]:
  entry_action (abi_builtin_encode_finish buf len m)
Proof
  simp[abi_builtin_encode_finish_def] >> IF_CASES_TAC >>
  simp[entry_action_bind, entry_action_emit_op, entry_action_emit_void]
QED

Theorem abi_encode_relabel_finish_equation:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  abi_builtin_encode_finish (FST ops) len m (start_swap sa L ids body_end) =
    ((),start_swap sa L ids final)
Proof
  strip_tac >>
  `entry_shape sa sa` by simp[entry_shape_refl] >>
  `entry_action (abi_builtin_encode_setup mid maxlen)` by
    (Cases_on `mid` >>
     simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
       entry_action_bind, entry_action_ignore_bind, entry_action_return,
       entry_action_alloc_buffer, entry_action_emit_op, entry_action_emit_void]) >>
  pop_assum mp_tac >> rewrite_tac[entry_action_def] >>
  disch_then drule_all >> disch_then (qspec_then `L` strip_assume_tac) >>
  mp_tac (cj 2 entry_action_encoder_mutual) >>
  rewrite_tac[entry_action_def] >> disch_then drule_all >>
  disch_then (qspec_then `L` strip_assume_tac) >>
  mp_tac (Q.INST [`buf` |-> `FST (ops:operand # operand)`] abi_encode_finish_entry_action) >>
  rewrite_tac[entry_action_def] >>
  disch_then drule_all >> simp[]
QED

  val bytes_phases = abi_encode_framed_phases_open |> SPEC_ALL
    |> Q.INST [`ctx` |-> `ctx with ctx_functions := [obs]`, `func` |-> `obs`]
    |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
    |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
               `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
    |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES];
  val empty_phases = abi_encode_empty_framed_phases_open |> SPEC_ALL
    |> Q.INST [`ctx` |-> `ctx with ctx_functions := [obs]`, `func` |-> `obs`]
    |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
    |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
               `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
    |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES];
Theorem abi_encode_nonword_relabel_observer:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (expr_type e))
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
  fresh_vars_wrt sb s /\ ~s.vs_halted /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p actual.
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av in
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
    LENGTH s.vs_memory <= LENGTH actual.vs_memory
Proof
  strip_tac >>
  drule_all abi_encode_nonword_observer_entry >>
  disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
  drule_all abi_encode_nonword_observer_geometry >>
  simp_tac bool_ss [LET_THM] >>
  disch_then assume_tac >>
  drule_all abi_encode_lower_phase_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `ready`
    (qx_choose_then `len` (qx_choose_then `body_end`
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_encode_nonword_relabel_resources >>
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
  `abi_encoder_admissible ei` by metis_tac[abi_enc_plan_admissible] >>
  `fresh_vars_wrt rf rs /\ ~rs.vs_halted /\
   rs.vs_current_bb = rst.cs_current_bb /\
   rs.vs_inst_idx = LENGTH rst.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rf`, Abbr `rs`, Abbr `rst`,
       abi_encode_start_relabel_resources, start_relabel_def] >>
     asm_rewrite_tac[]) >>
  `rf.cs_current_bb = sb.cs_current_bb /\
   LENGTH rf.cs_current_insts = LENGTH sb.cs_current_insts` by
    (simp_tac (srw_ss()) [Abbr `rf`] >>
     `cs_extends sa sb` by metis_tac[lower_abi_encode_extends] >>
     drule_all abi_encode_start_swap_control >>
     disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
     asm_rewrite_tac[]) >>
  suspend "live"
QED

Resume abi_encode_nonword_relabel_observer[live]:
  `rr.cs_next_var <= rf.cs_next_var /\ re.cs_next_var <= rf.cs_next_var` by
    (simp_tac (srw_ss()) [Abbr `rr`, Abbr `re`, Abbr `rf`,
       abi_encode_start_swap_resource_fields] >> asm_rewrite_tac[] >> decide_tac) >>
  qpat_x_assum `abi_builtin_encode_setup _ _ sa = _` kall_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ ready = _` kall_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ body_end = _` kall_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `abi_decoder_operand_live rst.cs_next_var op` by
    (simp_tac (srw_ss()) [Abbr `rst`, start_relabel_def] >>
     qpat_assum `!x. op = Var x ==> _` mp_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  `abi_decoder_operand_live rr.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `rst.cs_next_var` >>
     conj_tac
     >- (qpat_assum `rr.cs_next_var = _` (fn th => rewrite_tac[th]) >>
         Cases_on `mid` >> simp_tac (srw_ss()) []) >>
     first_assum ACCEPT_TAC) >>
  `(!x. op = Var x \/ SND ops = Var x ==> not_fresh_at rr x) /\
   (!x. FST ops = Var x ==> not_fresh_at rr x) /\
   abi_decoder_operand_live re.cs_next_var (FST ops)` by
    (conj_tac
     >- (rpt strip_tac
         >- (qpat_assum `abi_decoder_operand_live rr.cs_next_var op` mp_tac >>
             qpat_assum `op = Var x` (fn th => rewrite_tac[th]) >>
             simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
               not_fresh_at_def]) >>
         qpat_assum `abi_decoder_operand_live rr.cs_next_var (SND ops)` mp_tac >>
         qpat_assum `SND ops = Var x` (fn th => rewrite_tac[th]) >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           not_fresh_at_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `abi_decoder_operand_live rr.cs_next_var (FST ops)` mp_tac >>
         qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           not_fresh_at_def]) >>
     irule abi_decoder_operand_live_mono >> qexists_tac `rr.cs_next_var` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `val_footprint tv v = 0`
  >- suspend "empty"
  >> suspend "positive"
QED

Resume abi_encode_nonword_relabel_observer[positive]:
  `0 < val_footprint tv v` by decide_tac >>
  qpat_assum `0 < val_footprint tv v ==> _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`) bytes_phases >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room (ctx with ctx_functions := [obs]) obs _`)) >>
  disch_then (drule_at (Pat `fn_has_code re rf _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  qpat_assum `enc ct rv = _` (fn eq => rewrite_tac[eq]) >>
  impl_tac
  >- (rewrite_tac[wordsTheory.n2w_w2n] >> asm_rewrite_tac[] >> simp_tac std_ss []) >>
  strip_tac >> suspend "transport_positive"
QED

Resume abi_encode_nonword_relabel_observer[empty]:
  `ei = AbiCopy 0` by
    (qpat_assum `val_footprint tv v = 0 /\ _ \/ _` mp_tac >>
     qpat_assum `val_footprint tv v = 0` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) []) >>
  qpat_x_assum `ei = AbiCopy 0` SUBST_ALL_TAC >>
  qpat_assum `val_footprint tv v = 0` (fn zero =>
    qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _`
      (assume_tac o PURE_REWRITE_RULE [zero])) >>
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`) empty_phases >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  disch_then (qspec_then `rf` mp_tac) >>
  qpat_assum `enc ct rv = _` (fn eq => rewrite_tac[eq]) >>
  impl_tac
  >- (reverse (rpt conj_tac)
      >- (rpt strip_tac >>
          qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
            (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          simp_tac bool_ss [] >> metis_tac[]) >>
      asm_rewrite_tac[] >> simp_tac std_ss []) >>
  strip_tac >> suspend "transport"
QED
Resume abi_encode_nonword_relabel_observer[transport]:
  qpat_x_assum `enc ct rv = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!p. 32 + _ <= _ /\ _` (qspec_then `p` strip_assume_tac) >>
  `rst.cs_next_var <= rr.cs_next_var /\ rst.cs_next_var <= re.cs_next_var` by
    (simp_tac (srw_ss()) [Abbr `rst`, Abbr `rr`, Abbr `re`,
      start_relabel_def, abi_encode_start_swap_resource_fields] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es' actual` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`outsz` |-> `32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4))`]
       (SPEC_ALL abi_encode_phases_caller_state))) >> simp[]) >>
  `abi_decode_sim ctx obs rs actual` by
    (drule_all abi_decode_sim_ctx_no_invoke >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  qexistsl [`p`, `actual`] >> simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `Abbrev (rs = _)` (SUBST_ALL_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >> drule abi_encode_exec_frame_memory_length >> simp_tac (srw_ss()) []
QED
Resume abi_encode_nonword_relabel_observer[transport_positive]:
  qpat_x_assum `enc ct rv = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!p. 32 + _ <= _ /\ _` (qspec_then `p` strip_assume_tac) >>
  `rst.cs_next_var <= rr.cs_next_var /\ rst.cs_next_var <= re.cs_next_var` by
    (simp_tac (srw_ss()) [Abbr `rst`, Abbr `rr`, Abbr `re`,
      start_relabel_def, abi_encode_start_swap_resource_fields] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es' actual` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`outsz` |-> `32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4))`]
       (SPEC_ALL abi_encode_phases_caller_state))) >> simp[]) >>
  `abi_decode_sim ctx obs rs actual` by
    (drule_all abi_decode_sim_ctx_no_invoke >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  qexistsl [`p`, `actual`] >> simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `Abbrev (rs = _)` (SUBST_ALL_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >> drule abi_encode_exec_frame_memory_length >> simp_tac (srw_ss()) []
QED
Finalise abi_encode_nonword_relabel_observer
