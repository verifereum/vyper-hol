(* Same-witness frames for actual decoder navigation sequences. *)
Theory entryDecoderSetupEndpoint
Ancestors
  calldataDynStep calldataMembers abiDecoderArraySetupInputs loweringStateRelDefs
  abiDecoderReentry abiDecoderReentryAddress abiDecoderLoopSetup
  abiDecoderIndexedAddress abiEncoder compileEnv emitHelper emitHelperProps
  entryDecoderStateFrame entryDecoderHistoryFrame successfulSequenceEndpoint
  exprLoweringProps instIdxIndep venomState venomExecSemantics
  words list rich_list arithmetic venomInst abiDecoderVarSequence
  abiDecoderContract abiDecoderDynamicLoopSetup fragExec safeSequence fragExecMem
  venomInstProofs venomInstProofs1 venomExecProps finite_map pred_set

Theorem entry_element_setup_reentry_code:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,ready) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st ready)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dec_info_needs_offset di` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, compile_abi_decode_dyn_elem_ptr_def,
    comp_bind_def, comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >>
  simp[abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem entry_sequence_nonoutput_lookup[local]:
  !insts s t x.
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~MEM x i.inst_outputs) insts /\
    run_inst_seq insts s = OK t ==> lookup_var x t = lookup_var x s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  qpat_x_assum `!s t x. _` drule_all >> simp[]
QED

Theorem entry_element_setup_outputs[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,ready) /\ abi_decoder_older_vars st.cs_next_var x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st ready)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dec_info_needs_offset di` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND, EVERY_DEF, MEM] >>
  fs[abi_decoder_older_vars_def]
QED

Theorem entry_sequence_nonterminator_labels[local]:
  !insts s t. EVERY (\i. ~is_terminator i.inst_opcode) insts /\
    run_inst_seq insts s = OK t ==> t.vs_labels = s.vs_labels
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  qpat_x_assum `!s t. _` drule_all >> simp[]
QED

Theorem entry_element_setup_total_frame:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    fs[EVERY_MEM] >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >> strip_tac >>
  irule entry_sequence_nonoutput_lookup >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `_ IN abi_decoder_older_vars _`
    (assume_tac o REWRITE_RULE [IN_APP]) >>
  drule_all entry_element_setup_outputs >> strip_tac >> fs[EVERY_MEM]
QED

Theorem entry_element_setup_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di
    abi_sz mem_sz st = (ops,ready) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t =
      SOME (if dec_info_needs_offset di then
        n2w (sb + 32 + w2n (abi_decode_load CALLDATALOAD
          (n2w (sb + 32 + j * abi_sz) : bytes32) s))
        else n2w (sb + 32 + j * abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * mem_sz)) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st ready /\ entry_decoder_obs s t /\ alloca_history fn t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> drule_all calldata_element_setup_reentry >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> drule_all entry_element_setup_total_frame >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ _) _` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `p`] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`P` |-> `\s:venom_state. T`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qexists_tac `t with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  fs[abi_decoder_address_frame_def, eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem entry_sequence_output_disjoint_fresh[local]:
  !code s t.
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    (!n. limit.cs_next_var <= n ==>
      ~MEM (STRING #"%" (toString n)) i.inst_outputs)) code /\
  fresh_vars_wrt limit s /\ run_inst_seq code s = OK t ==>
  fresh_vars_wrt limit t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ARB h s = OK u` by simp[step_inst_non_invoke] >>
  drule step_preserves_non_output_vars >> asm_rewrite_tac[] >> strip_tac >>
  simp_tac bool_ss [fresh_vars_wrt_def] >> rpt strip_tac >>
  `~MEM (STRING #"%" (toString n)) h.inst_outputs` by fs[GREATER_EQ] >>
  qpat_x_assum `!v. ~MEM v _ ==> _` (qspec_then `STRING #"%" (toString n)` mp_tac) >>
  fs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF]
QED

Theorem entry_member_navigation_outputs[local]:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  mid.cs_next_var <= limit.cs_next_var ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    (!n. limit.cs_next_var <= n ==>
      ~MEM (STRING #"%" (toString n)) i.inst_outputs)) (emitted_insts st mid)
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def] >>
  rpt strip_tac >> irule fresh_var_distinct >> decide_tac
QED

Theorem entry_member_navigation_endpoint:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME q /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ fn_has_code st mid fn /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
    t.vs_inst_idx = LENGTH mid.cs_current_insts /\
    eval_operand dp t = SOME (q + n2w vo) /\
    eval_operand ep t = SOME
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
       else p + n2w ao) /\
    abi_decoder_operand_live mid.cs_next_var ep /\
    abi_decoder_operand_live mid.cs_next_var dp /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st mid /\ st.cs_next_var <= mid.cs_next_var /\
    entry_decoder_obs s t /\ alloca_history fn t /\
    ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> drule calldata_member_address_shape >> strip_tac >>
  drule_all calldata_member_address_repeat >> strip_tac >>
  drule_all entry_member_navigation_outputs >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st mid) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     (!n. limit_st.cs_next_var <= n ==>
       ~MEM (STRING #"%" (toString n)) i.inst_outputs)) (emitted_insts st mid) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st mid) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st mid)` by
    (rpt conj_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_sequence_output_disjoint_fresh >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  `isPREFIX st.cs_current_insts mid.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st mid) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.INST [`ready` |-> `mid`, `P` |-> `\s:venom_state. T`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qexists_tac `t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry setup endpoint inherited admission"
    end) [entry_element_setup_reentry_code, entry_sequence_nonoutput_lookup,
          entry_element_setup_outputs, entry_sequence_nonterminator_labels,
          entry_element_setup_total_frame, entry_element_setup_endpoint,
          entry_sequence_output_disjoint_fresh, entry_member_navigation_outputs,
          entry_member_navigation_endpoint];
