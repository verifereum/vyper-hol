(* Observed live member-address navigation, before decoding a child. *)
Theory entryReachBodyMemberSetup
Ancestors
  loweringStateRelDefs abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderContract
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop
  entryReachBodyOperationalPath entrySinkExtraction
  entryReachBodyScratchSet entryReachBodyOwnedRegion
  abiAllocationHistory allocaFrontierBound allocaBudgetProps venomMemDefs
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  venomState venomInst words list rich_list arithmetic

Theorem member_setup_observation_code[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,mid) /\
  mid.cs_next_var <= limit_st.cs_next_var ==>
  mid.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. MEM i.inst_opcode
    [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
      i.inst_outputs) (emitted_insts st mid) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st mid)
Proof
  Cases_on `dyn` >>
  simp[abi_decode_member_setup_def, abiEncoderTheory.compile_abi_dec_addr_def, compile_getelemptr_abi_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem entry_member_setup_endpoint:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,mid) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (sb+ao) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) u = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD /\ abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def] >>
  drule_all (SIMP_RULE bool_ss [eval_operand_def, arithmeticTheory.ADD]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0`] abi_decode_member_setup_reentry)) >> strip_tac >>
  drule_all member_setup_observation_code >> strip_tac >>
  drule_all entry_sequence_observations >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (irule entry_decode_emitted_path >> simp[] >> qexists_tac `st` >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  qexists_tac `t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  gvs[entry_loop_fields_def, abi_decoder_address_frame_def, fresh_vars_wrt_def,
      eval_operand_def, inst_extends_def]
QED

(* Nonallocating navigation transports the complete ambient resource package. *)
Theorem entry_member_resource_frame:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  entry_scratch_ready sites b cap s /\
  entry_owned_region oid root extent d sz s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s ==>
  entry_scratch_ready sites b cap t /\
  entry_owned_region oid root extent d sz t /\ alloca_inv t /\
  abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t
Proof
  strip_tac >>
  `entry_scratch_ready sites b cap t` by
    metis_tac[entry_scratch_ready_frame] >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[entry_owned_region_def, alloca_frontier_inv_def, abi_alloca_history_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED
