Theory abiReturnPrefixTransport
Ancestors
  abiReturnSize abiReturnReject abiMalformedRecursiveInterface
  abiMalformedPruneState abiDecoderReentry freshWrites
  exprLoweringProps builtinSimple emitHelperProps exprLowering emitHelper
  compileEnv venomExecSemantics venomState venomInst finite_map words list rich_list

Definition abi_return_decode_ready_def:
  abi_return_decode_ready ctx func cenv cx es a sites dstid live base_op dst
      B cap bs d n s <=>
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv a /\
    abi_malformed_allocated_window live B (LENGTH (TAKE cap bs)) (TAKE cap bs) s /\
    live NOTIN sites /\ live <> dstid /\ dstid NOTIN sites /\
    abi_malformed_destination func cenv es.scopes dstid d n s /\
    d + n < dimword (:256) /\ eval_operand base_op s = SOME (n2w B) /\
    eval_operand dst s = SOME (n2w d) /\
    EVERY (abi_decoder_operand_live a.cs_next_var) [base_op;dst]
End

Theorem abi_return_size_outputs[local]:
  compile_return_value_decode lo cap a = (hi,b) ==>
  hi <> Lit 0w /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = RETURNDATASIZE) /\
    EVERY (\x. ~not_fresh_at a x) i.inst_outputs) (emitted_insts a b)
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp_tac (srw_ss()) [mk_inst_def, fresh_write_op_def, not_fresh_at_def] >>
  rpt conj_tac >> qexists_tac `a.cs_next_var` >> simp[]
QED

Theorem abi_return_size_reserved:
  compile_return_value_decode lo cap a = (hi,b) /\
  run_inst_seq (emitted_insts a b) s = OK u ==>
  !x. not_fresh_at a x ==> lookup_var x u = lookup_var x s
Proof
  strip_tac >> drule abi_return_size_outputs >> strip_tac >>
  mp_tac (Q.SPECL [`emitted_insts a b`, `not_fresh_at a`, `s`, `u`]
    run_inst_seq_protected_frame) >>
  impl_tac >- (
    reverse conj_tac >- simp[] >>
    map_every qx_gen_tac [`i`, `s1`, `t1`] >> strip_tac >>
    qpat_x_assum `EVERY _ (emitted_insts a b)` mp_tac >>
    rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
    simp[] >> disch_then assume_tac >>
    Cases_on `i.inst_opcode = RETURNDATASIZE`
    >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
        simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()] >>
        strip_tac >> gvs[update_var_def, venom_state_component_equality] >>
        rpt strip_tac >> gvs[EVERY_MEM] >>
        `x <> out` by metis_tac[] >>
        qpat_x_assum `_ = t1.vs_vars` (SUBST1_TAC o SYM) >>
        simp[FLOOKUP_UPDATE]) >>
    conj_tac >- metis_tac[step_fresh_write_op] >>
    rpt strip_tac >>
    `~MEM x i.inst_outputs` by (fs[EVERY_MEM] >> metis_tac[]) >>
    metis_tac[step_fresh_write_op]) >>
  simp[lookup_var_def]
QED

Theorem abi_return_prefix_transport:
  compile_return_value_decode lo cap a = (hi,b) /\ fresh_vars_wrt a s /\
  lo < dimword (:256) /\ cap < dimword (:256) /\ s.vs_returndata = bs /\
  LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  abi_return_decode_ready ctx func cenv cx es a sites dstid live base_op dst
    B cap bs d n s ==>
  ?u. run_inst_seq (emitted_insts a b) s = OK u /\ fresh_vars_wrt b u /\
    abi_malformed_entry ctx func cenv cx es b sites dstid live base_op hi
      (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d n
      (u with vs_inst_idx := LENGTH b.cs_current_insts) /\
    (?vars. u = s with vs_vars := vars)
Proof
  strip_tac >>
  `LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
  drule_all abi_return_size_run >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule abi_return_size_reserved >>
  disch_then (qspecl_then [`u`, `s`] mp_tac) >> simp[] >>
  disch_then assume_tac >>
  drule abi_return_size_outputs >> strip_tac >>
  `a.cs_next_var <= b.cs_next_var` by
    (mp_tac (Q.SPECL [`lo`, `cap`, `a`] ci_mono_compile_return_value_decode) >>
     simp[ci_mono_def]) >>
  fs[abi_return_decode_ready_def] >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >>
     reverse conj_tac >- simp[] >> qexists_tac `a` >> simp[]) >>
  `local_ptrs_reserved cenv b` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_operand_live b.cs_next_var base_op /\
   abi_decoder_operand_live b.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_decoder_operand_live b.cs_next_var hi` by
    (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  reverse conj_tac >- (qexists_tac `vars` >> simp[]) >>
  pure_rewrite_tac[abi_malformed_entry_def] >>
  `s with <|vs_vars := vars; vs_inst_idx := LENGTH b.cs_current_insts|> =
   u with vs_inst_idx := LENGTH b.cs_current_insts` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[stmt_state_rel_inst_idx,
       abiBytesFinalExecutionTheory.abi_bytes_eval_operand_inst_idx,
       abi_decoder_operand_live_def, eval_operand_def] >>
  fs[abi_malformed_allocated_window_def, abi_malformed_destination_def] >>
  simp[LENGTH_TAKE, arithmeticTheory.MIN_COMM] >>
  conj_tac >- (qexistsl_tac [`inst`, `q`] >> simp[]) >>
  simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]
QED
