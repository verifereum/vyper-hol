(* Exact nonwriting prefix observations for both bytestring copy strategies. *)
Theory abiMalformedBytesExecution
Ancestors
  abiMalformedBulkConstructor abiMalformedRecursiveInterface abiBoundedLeafReflection
  abiDecoderComposition abiDecoderBytesFrame abiDecoderAbortReentry
  abiMalformedConstructorContract abiMalformedConstructorInduction
  abiDecoderBytestringCases abiEncoder fragExec contractABI vyperABI
  abiDecoderReentryPointer abiDecoderVarSequence
  abiDecoderCoherence abiDecoderBytesPrefix abiBoundedBytesExecution
  abiDecoderBytesRuntime abiDecoderBytesPhases abiDecoderBytesBound abiDecoderGuards
  abiDecoderRange abiDecoderContract abiDecoderReentry abiEncoder
  emitHelper emitHelperProps exprLowering exprLoweringProps compileEnv loweringStateRelDefs venomInst
  venomState venomExecSemantics venomExecProofs words finite_map list rich_list arithmetic

Theorem abi_malformed_bytes_prefix_step[local]:
  MEM inst.inst_opcode [ADD; LT; GT; ISZERO; AND; ASSERT; MLOAD] /\
  step_inst_base inst s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. ~MEM x inst.inst_outputs ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  simp[] >> strip_tac
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_malformed_bytes_prefix_instructions[local]:
  abi_decode_bytes_position_prefix src MLOAD base_op hi n st = ((addr,cnt),en) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; LT; GT; ISZERO; AND; ASSERT; MLOAD] /\
    (!x. not_fresh_at st x ==> ~MEM x i.inst_outputs)) (emitted_insts st en)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_bytes_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bytes_prefix_exact:
  abi_decode_bytes_position_prefix src MLOAD base_op hi n st = ((addr,cnt),en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule abi_malformed_bytes_prefix_instructions >> strip_tac >>
  `t = s with vs_vars := t.vs_vars /\
   (!x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)` by
    (irule run_inst_seq_protected_frame >> goal_assum (drule_at Any) >>
     rpt strip_tac >>
     `MEM i.inst_opcode [ADD; LT; GT; ISZERO; AND; ASSERT; MLOAD] /\
      (!x. not_fresh_at st x ==> ~MEM x i.inst_outputs)` by
       (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[EVERY_MEM] >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     drule_all abi_malformed_bytes_prefix_step >> simp[] >> metis_tac[]) >>
  simp[lookup_var_def]
QED

Theorem abi_malformed_bytes_prefix_resource:
  abi_decode_bytes_position_prefix src MLOAD base_op hi n st = ((addr,cnt),en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >> drule_all abi_malformed_bytes_prefix_exact >> strip_tac >>
  irule abi_malformed_resource_register_update >>
  conj_tac >- fs[abi_malformed_entry_def] >>
  qexists_tac `s` >> simp[] >>
  irule abi_malformed_resource_refl >> fs[abi_malformed_entry_def]
QED

Theorem abi_malformed_bytes_tail_step_lookup[local]:
  MEM inst.inst_opcode [ADD; NOT; AND; MSTORE; MCOPY; LT; GT; ISZERO; ASSERT; MLOAD] /\
  step_inst_base inst s = OK t ==>
  !x. ~MEM x inst.inst_outputs ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  simp[] >> strip_tac >>
  FIRST [
    (mp_tac (Q.SPECL [`inst`, `s`, `t`] step_pure_opcode_frame) >> simp[] >> NO_TAC),
    (mp_tac (Q.INST [`inst` |-> `inst`, `s` |-> `s`, `t` |-> `t`]
       abi_malformed_bytes_prefix_step) >> simp[] >> NO_TAC),
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
     simp[exec_write2_def, AllCaseEqs(), mstore_def, mcopy_def,
       write_memory_with_expansion_def] >> rpt strip_tac >> gvs[])]
QED

Theorem abi_malformed_bytes_tail_sequence_lookup[local]:
  !is P s t.
  EVERY (\i. MEM i.inst_opcode [ADD; NOT; AND; MSTORE; MCOPY; LT; GT; ISZERO; ASSERT; MLOAD] /\
    (!x. P x ==> ~MEM x i.inst_outputs)) is /\
  run_inst_seq is s = OK t ==>
  !x. P x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  mp_tac (Q.INST [`inst` |-> `h`, `t` |-> `v`] abi_malformed_bytes_tail_step_lookup) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!P' s'' t'. _` (qspecl_then [`P`, `v`, `t`] mp_tac) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem abi_malformed_bytes_runtime_tail_lookup:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !x. not_fresh_at st x ==> lookup_var x t = lookup_var x s
Proof
  strip_tac >> simp[lookup_var_def] >>
  match_mp_tac (Q.SPECL [`emitted_insts st en`, `not_fresh_at st`]
    abi_malformed_bytes_tail_sequence_lookup) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bytes_prefix_reflected_total:
  abi_decode_bytes_position_prefix src MLOAD base_op hi n st = ((addr,cnt),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_bytes ce ty <= outsz /\ fresh_vars_wrt st s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?c t. c <= n /\ p+32+c <= L /\
    run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand addr t = SOME (n2w (B+p)) /\
    eval_operand cnt t = SOME (n2w c) /\ fresh_vars_wrt en t /\
    abi_malformed_reflected_post env ty (DROP p xs)
      ctx func cenv cx es st.cs_next_var sites dstid s t)
Proof
  strip_tac >>
  `d+outsz < dimword (:256)` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_bytestring_capacity >> strip_tac >>
  `abi_decode_source_opcode MLOAD /\ hi <> Lit 0w /\
   eval_operand src s = SOME (n2w p) /\ p < dimword (:256) /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L) /\ L < dimword (:256) /\
   n < dimword (:256) /\ B+L < dimword (:256) /\
   mem_bytes_at B L s.vs_memory = xs` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
        abi_decode_source_opcode_def] >> decide_tac) >>
  drule_all abi_decode_bytes_position_prefix_total >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`c`, `t`] >> simp[] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    (drule_all abi_malformed_bytes_prefix_resource >> simp[]) >>
  simp[abi_malformed_reflected_post_def] >>
  `mem_bytes_at (B+p) (L-p) (abi_decode_source MLOAD s) = DROP p xs` by
    (simp[abi_decode_source_def] >> irule abi_malformed_source_suffix >> simp[]) >>
  irule abi_decoder_bytestring_memory_reflect >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ce`, `sf`, `tv`] >> simp[]
QED

Theorem abi_malformed_bytes_runtime_tail_resource:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand addr s = SOME (n2w a) /\ eval_operand cnt s = SOME (n2w c) /\
  c+31 < dimword (:256) /\ 32+c < dimword (:256) /\
  32+32*((c+31) DIV 32) <= outsz /\ a < dimword (:256) /\
  fresh_vars_wrt st s /\ fn_inst_ids_distinct func ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `d+outsz < dimword (:256) /\ eval_operand dst s = SOME (n2w d) /\
   local_ptrs_reserved cenv st` by fs[abi_malformed_entry_def] >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all abi_malformed_bytes_runtime_tail_exact >> strip_tac >>
  drule abi_malformed_bytes_runtime_tail_lookup >>
  disch_then (drule_at (Pos hd)) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule abi_malformed_resource_register_update >> simp[] >>
  qexists_tac `mcopy d a (32+c) (mstore (d+32*((c+31) DIV 32)) 0w s)` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      simp_tac std_ss [mcopy_def, mstore_def, write_memory_with_expansion_def,
        lookup_var_def, LET_THM, venom_state_accfupds]) >>
  `d <= d+32*((c+31) DIV 32) /\
   d+32*((c+31) DIV 32)+32 <= d+outsz /\ 32+c <= outsz` by
    (mp_tac (Q.INST [`c` |-> `c`] abi_decode_bytes_round_bounds) >> decide_tac) >>
  drule_all abi_malformed_bytes_store_copy_resource >> simp[]
QED

Theorem abi_malformed_bytes_fixed_tail_resource:
  emit_void MCOPY [dst; src; Lit (n2w ncopy)] st = ((),en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  ncopy <= outsz /\ fresh_vars_wrt st s /\ fn_inst_ids_distinct func ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `d+outsz < dimword (:256) /\ p < dimword (:256) /\
   eval_operand src s = SOME (n2w p) /\
   eval_operand dst s = SOME (n2w d)` by fs[abi_malformed_entry_def] >>
  `ncopy < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w ncopy)) s = SOME (n2w ncopy)` by simp[eval_operand_def] >>
  drule_all emit_void_MCOPY_correct >> strip_tac >>
  gvs[w2n_n2w, LESS_MOD] >> simp[] >>
  `d <= d /\ d+ncopy <= d+outsz` by decide_tac >>
  drule_all abi_malformed_destination_copy_resource >> simp[]
QED

Theorem abi_malformed_bytes_prefix_entry:
  abi_decode_bytes_position_prefix src MLOAD base_op hi n st = ((addr,cnt),en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  abi_malformed_entry ctx func cenv cx es en sites dstid live
    base_op hi src dst B L xs p d outsz t
Proof
  strip_tac >> drule_all abi_malformed_bytes_prefix_resource >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> fs[abi_malformed_entry_def]) >>
  `EVERY (abi_decoder_operand_live en.cs_next_var) [base_op;hi;src;dst]` by
    (fs[abi_malformed_entry_def] >>
     rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src t = SOME (n2w p) /\ eval_operand dst t = SOME (n2w d)` by
    (fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >> metis_tac[]) >>
  `d <= d /\ d+outsz <= d+outsz /\ sites SUBSET sites /\
   p < dimword (:256) /\ d+outsz < dimword (:256)` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_child_entry >> simp[]
QED

Theorem abi_malformed_bytes_fresh_total:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_bytes ce ty <= outsz /\ fresh_vars_wrt st s /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
    abi_malformed_reflected_post env ty (DROP p xs)
      ctx func cenv cx es st.cs_next_var sites dstid s t)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `d+outsz < dimword (:256)` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_bytestring_capacity >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_prefix_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> disch_tac >> gvs[] >> PairCases_on `ac` >> gvs[] >>
  drule_all abi_malformed_bytes_prefix_reflected_total >> strip_tac
  >- suspend "abort" >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK s1` >>
  `abi_malformed_entry ctx func cenv cx es mid sites dstid live
     base_op hi src dst B L xs p d outsz s1` by
    (drule_all abi_malformed_bytes_prefix_entry >> simp[]) >>
  drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
  Cases_on `base_op = Lit 0w`
  >- suspend "fixed" >>
  suspend "runtime"
QED

Resume abi_malformed_bytes_fresh_total[abort]:
  disj1_tac >> drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
  `inst_extends cs' en` by
    (Cases_on `base_op = Lit 0w` >> gvs[abi_decode_copy_opcode_def] >>
     metis_tac[inst_extends_emit_void, abi_decode_bytes_runtime_tail_shape]) >>
  drule_all run_inst_seq_abort_extends >> simp[] >> metis_tac[]
QED
Resume abi_malformed_bytes_fresh_total[fixed]:
  gvs[abi_decode_copy_opcode_def] >> disj2_tac >>
  drule_all abi_malformed_bytes_fixed_tail_resource >> strip_tac >>
  `inst_extends mid en` by metis_tac[inst_extends_emit_void] >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s1 t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`mid.cs_next_var`, `sites`] >> simp[]) >>
  fs[abi_malformed_reflected_post_def] >>
  drule_all abi_malformed_resource_trans >> simp[]
QED
Resume abi_malformed_bytes_fresh_total[runtime]:
  gvs[] >> disj2_tac >>
  `B+L < dimword (:256)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  `c+31 < dimword (:256) /\ 32+c < dimword (:256) /\ B+p < dimword (:256)` by decide_tac >>
  `32+32*((c+31) DIV 32) <= outsz` by
    (qpat_assum `c <= n` (mp_then Any mp_tac abi_decode_bytes_round_capacity) >> decide_tac) >>
  drule_all abi_malformed_bytes_runtime_tail_resource >> strip_tac >>
  `inst_extends mid en` by metis_tac[abi_decode_bytes_runtime_tail_shape] >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s1 t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`mid.cs_next_var`, `sites`] >> simp[]) >>
  fs[abi_malformed_reflected_post_def] >>
  drule_all abi_malformed_resource_trans >> simp[]
QED
Finalise abi_malformed_bytes_fresh_total

Theorem abi_malformed_bytes_lookup:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !x. not_fresh_at st x ==> lookup_var x t = lookup_var x s
Proof
  strip_tac >> simp[lookup_var_def] >>
  match_mp_tac (Q.SPECL [`emitted_insts st en`, `not_fresh_at st`]
    abi_malformed_bytes_tail_sequence_lookup) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_prefix_phases, abi_decode_source_opcode_def,
    comp_bind_def, LET_THM] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_bytes_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
    abi_decode_copy_opcode_def, abi_decode_bytes_runtime_tail_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_bytes_reflected_run:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_bytes ce ty <= outsz /\ fn_inst_ids_distinct func /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt ceiling t /\
    abi_malformed_reflected_post env ty (DROP p xs)
      ctx func cenv cx es st.cs_next_var sites dstid s t)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule abi_malformed_entry_prune >> strip_tac >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_decoder_prune_fresh] >>
  drule_all abi_malformed_bytes_fresh_total >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  `fresh_vars_wrt ceiling t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  drule_all abi_decoder_sequence_runtime_reentry >> strip_tac >>
  rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x clean` by
    (drule abi_malformed_bytes_lookup >> disch_then (drule_at (Pos hd)) >>
     strip_tac >>
     qpat_assum `run_inst_seq _ (abi_decoder_prune_vars _ _) = OK clean`
       (mp_then Any mp_tac abi_malformed_bytes_lookup) >>
     simp[] >> rpt strip_tac >>
     fs[abi_decoder_prune_vars_def, lookup_var_def, FLOOKUP_DRESTRICT,
        abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv st` by fs[abi_malformed_entry_def] >>
  fs[abi_malformed_reflected_post_def] >>
  drule_all abi_malformed_resource_restore >> strip_tac >>
  fs[abi_malformed_resource_post_def, abi_decoder_prune_vars_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var s) = SOME w` by
    simp[abi_decoder_prune_eval] >>
  fs[abi_decoder_prune_vars_def] >> metis_tac[]
QED

Theorem abi_malformed_bytes_constructor:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  fn_inst_ids_distinct func /\ type_memory_bytes ce ty <= outsz ==>
  abi_malformed_constructor env ty (DecBytestring n) ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  strip_tac >>
  `is_dynamic (vyper_to_abi_type env ty)` by
    (drule_all abi_decoder_bytestring_cases >> strip_tac >>
     gvs[vyper_to_abi_type_def, is_dynamic_def]) >>
  simp[abi_malformed_constructor_def] >> rpt strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> fs[inst_extends_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all abi_malformed_bytes_reflected_run >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_reflected_post_inst_idx, fresh_vars_wrt_def]
QED

Theorem abi_malformed_bytes_type_contract:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n ==>
  abi_malformed_type_contract ce env sf ty tv
Proof
  simp[abi_malformed_type_contract_def] >> rpt strip_tac >>
  irule abi_malformed_bytes_constructor >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
