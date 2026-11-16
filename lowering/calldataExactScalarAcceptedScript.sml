Theory calldataExactScalarAccepted
Ancestors
  calldataWordLive calldataWordPtr calldataFiniteTransport calldataDynOwned
  decoderWorldFramePtr decoderGhostFramePtr abiEncoderWindowLookup
  bodyPtrEnvBuiltinsSequenceFrame abiDecoderFrameCompose ptrDiscipline bodyPtrDefs
  abiCallerAllocation
  abiDecoderReentry abiDecoderVarSequence abiDecoderFrame fragGasOriginPtr fragExecMem
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  loweringStateRelDefs venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map pred_set

Theorem scalar_emitted_bounds[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord cl) st = ((),last) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\
    abi_decoder_reentry_opcode i.inst_opcode /\
    EVERY (not_fresh_at last) i.inst_outputs /\
    (!name. not_fresh_at st name ==> ~MEM name i.inst_outputs))
    (emitted_insts st last)
Proof
  Cases_on `cl` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def,
    not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_TRANS, DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem scalar_step_tvar_frame[local]:
  ~MEM name inst.inst_outputs ==>
  FLOOKUP (step_taint inst s t tn).t_var name = FLOOKUP tn.t_var name
Proof
  simp[step_taint_def, set_var_taint_def] >>
  Cases_on `inst.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  rename1 `inst.inst_outputs = h::outs` >>
  Cases_on `outs` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem calldata_word_accepted_resource_joint:
  !st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG cl.
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord cl) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+32 <= base_addr+cap /\ d+32 < dimword (:256) /\
  ptr_covers G tn child initial 32 /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_clamp_ok cl (abi_decode_load CALLDATALOAD p initial) ==>
  ?v H u.
    run_inst_seq (emitted_insts st last) initial =
      OK (v with vs_inst_idx := initial.vs_inst_idx) /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    mem_word_at d v.vs_memory = abi_decode_load CALLDATALOAD p initial /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    abi_decode_footprint_frame [(d,32)] initial v /\
    v.vs_allocas = initial.vs_allocas /\ v.vs_alloca_next = initial.vs_alloca_next /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v 32 /\
    (!i. d <= i /\ i < d+32 ==> i NOTIN u.t_mem) /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    v.vs_accounts = initial.vs_accounts /\ v.vs_transient = initial.vs_transient /\
    v.vs_logs = initial.vs_logs /\ v.vs_outcomes = initial.vs_outcomes /\
    v.vs_requests = initial.vs_requests /\
    v.vs_pending_deletions = initial.vs_pending_deletions /\
    v.vs_tx_ctx = initial.vs_tx_ctx /\ v.vs_block_ctx = initial.vs_block_ctx /\
    v.vs_fmp = initial.vs_fmp /\ v.vs_gas_readings = initial.vs_gas_readings /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  rpt gen_tac >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  `d+32 <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> metis_tac[]) >>
  drule_all calldata_word_accepted_live >> strip_tac >>
  `not_fresh_at st child /\ (!x. src = Var x ==> not_fresh_at st x)` by
    metis_tac[calldata_operand_live_not_fresh] >>
  drule_all calldata_word_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule scalar_emitted_bounds >> strip_tac >>
  `fresh_vars_wrt limit s'` by
    (qpat_assum `s' = _` SUBST1_TAC >>
     irule abi_window_seq_fresh_idx >>
     qexistsl_tac [`last`,`emitted_insts st last`,`initial`] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       qpat_x_assum `EVERY _ (emitted_insts st last)` mp_tac >>
       pure_rewrite_tac [EVERY_MEM] >> metis_tac[]]) >>
  `!name. not_fresh_at st name ==>
    FLOOKUP tn'.t_var name = FLOOKUP tn.t_var name` by
    (rpt strip_tac >>
     irule (inst_seq_ptr_invariant |> SPEC_ALL |> Q.INST
       [`R` |-> `\H u. FLOOKUP u.t_var name = FLOOKUP tn.t_var name`]
       |> BETA_RULE) >>
     conj_tac >- simp[] >>
     qpat_assum `!D. inst_seq_ptr D lower ctx fn PG G tn _ initial G' tn'`
       (qspec_then `ARB` assume_tac) >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     qpat_x_assum `FLOOKUP q.t_var name = _` (fn th => rewrite_tac [GSYM th]) >>
     irule scalar_step_tvar_frame >>
     qpat_x_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st last)` by
    (qpat_x_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> metis_tac[]) >>
  drule_all decoder_run_world_frame >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderClampedWordTheory.abi_decoder_clamped_word_shape >> strip_tac >>
  drule calldataWordLeafTheory.calldata_word_opcodes >> strip_tac >>
  `frag_exec_mem ctx st last (\s. s = initial) (\v. v = s') (\r. F)` by
    (irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       gen_tac >> BETA_TAC >> disch_then SUBST1_TAC >> conj_tac
       >- (ho_match_mp_tac (GEN_ALL calldata_word_prefix_live) >>
           qexistsl_tac [`src`,`p`,`Var child`,`d`,`cl`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
       disj1_tac >> qexists_tac `t` >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `s' = _` (fn th => rewrite_tac [th])]) >>
  `!fuel r. run_from fuel ctx fn s' = r /\ (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn initial = r /\
      (mem_safe_run fuel ctx fn s' ==> mem_safe_run fuel' ctx fn initial)` by
    (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [frag_exec_mem_def] >>
     disch_then (qspecl_then [`fn`,`initial`] mp_tac) >>
     simp_tac bool_ss [] >>
     impl_tac >- metis_tac[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `w2n (n2w d : bytes32) = d` by
    (qpat_assum `d < dimword (:256)` mp_tac >>
     simp_tac (srw_ss()) [w2n_n2w]) >>
  qpat_assum `w2n (n2w d : bytes32) = d`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qexistsl_tac [`s'`,`G'`,`tn'`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (rename1 `abi_decode_footprint_frame _ _ _` >>
     qpat_assum `s' = _` SUBST1_TAC >>
     qpat_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_footprint_frame_def, abi_footprint_disjoint_def,
       abiDecoderContractTheory.abi_decode_frame_def] >>
     strip_tac >> first_assum ACCEPT_TAC),
    (irule calldata_alloca_inv_fields >> qexists_tac `initial` >>
     rpt conj_tac >> first_assum ACCEPT_TAC),
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >>
     rpt conj_tac >> first_assum ACCEPT_TAC),
    (CHANGED_TAC
      (qpat_assum `s'.vs_allocas = initial.vs_allocas`
         (fn th => rewrite_tac [th]) >>
       qpat_assum `s'.vs_alloca_next = initial.vs_alloca_next`
         (fn th => rewrite_tac [th])) >>
     FIRST [first_assum ACCEPT_TAC, simp_tac (srw_ss()) [] >> NO_TAC]),
    (rpt strip_tac >> qpat_assum `s' = _` SUBST1_TAC >>
     pure_rewrite_tac [instIdxIndepTheory.eval_op_inst_idx] >>
     first_assum irule >> first_assum ACCEPT_TAC),
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!x. not_fresh_at st x ==> FLOOKUP G' x = _ /\ _`
           (irule o cj 1) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP tn'.t_var x = _` irule >>
     first_assum ACCEPT_TAC),
    (qpat_assum `s' = _` SUBST1_TAC >>
     qpat_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_frame_def] >>
     strip_tac >> first_assum ACCEPT_TAC),
    (qpat_assum `_ ==> !D explicit. gas_origin_ptr_path _ _ _ _` mp_tac >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then MATCH_ACCEPT_TAC)]
QED
