(* Zero-length copy has no source-frontier requirement. *)
Theory abiEncodeEmptySourceCopyMem
Ancestors
  abiEncoderWindowLeaves abiEncoderLeaves abiEncoderWindowContract
  abiEncoderWindowSequence abiEncoderWindowSequenceFrameMem abiEncoderWindowMemFrame
  windowSequenceMem memContinuation abiEncoderLeafGlobals abiDecoderVarSequence
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect abiEncoderExtendSim
  abiEncoderWindow abiEncoderInput allocaFootprint emitHelperProps
  exprLoweringProps freshWrites compileEnv venomExecSemantics venomState
  valueEncoding valueEncodingProofs words list arithmetic pred_set

Theorem empty_source_copy_run_mem:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,en) /\
  abi_encoder_admissible (AbiCopy 0) /\
  abi_encoder_window_input (AbiCopy 0) at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_strong_result ctx func st en out at av d s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  `enc at av = []` by fs[abi_encoder_window_copy_iff, valueEncodingDefsTheory.mem_bytes_at_def] >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (simp_tac (srw_ss()) [window_alloca_sites_def] >> rpt strip_tac >> metis_tac[]) >>
  pop_assum (mk_asm "sizes") >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  drule abi_encode_copy_code >> strip_tac >>
  `d < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     qpat_x_assum `d + LENGTH _ <= _` mp_tac >>
     asm_rewrite_tac [listTheory.LENGTH, arithmeticTheory.ADD_0] >> decide_tac) >>
  `eval_operand src s = SOME (n2w (w2n (n2w sb : bytes32))) /\
   eval_operand (Lit 0w) s = SOME (n2w 0)` by simp[eval_operand_def] >>
  `w2n (n2w sb : bytes32) < dimword (:256) /\ 0 < dimword (:256)` by simp[] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `window_seq st en s (mcopy d (w2n (n2w sb : bytes32)) 0 s)` by
    (simp[window_seq_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
     metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule emit_mcopy_mem_ok >> disch_then irule >> simp[eval_operand_def] >> metis_tac[]) >>
  suspend "package"
QED

Resume empty_source_copy_run_mem[package]:
  qmatch_asmsub_abbrev_tac `window_seq st en s raw` >>
  `mem_cont_sim ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  `window_mem_frame ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (drule abi_encoder_copy_global_code >> strip_tac >>
     irule window_seq_mem_frame >> simp[] >> qexists `st` >> simp[] >>
     fs[EVERY_MEM, abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  `abi_encoder_extend_sim ctx func s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_extend_sim] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    [(d,0)] s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (simp[Abbr `raw`] >> irule abi_encoder_registered_effect_trans >>
     qexists `mcopy d (w2n (n2w sb : bytes32)) 0 s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st en) [(d,0)] s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st en)`, `[(d,0)]`] >>
     simp[window_alloca_sites_subset]) >>
  qexists `raw with vs_inst_idx := LENGTH en.cs_current_insts` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, valueEncodingDefsTheory.mem_bytes_at_def, abi_encoder_extend_sim_sim] >>
  suspend "resources"
QED

Resume empty_source_copy_run_mem[resources]:
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `w2n (n2w sb : bytes32)`, `n` |-> `0`,
    `ix` |-> `LENGTH en.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> simp[Abbr `raw`] >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  asm "sizes" ACCEPT_TAC
QED

Finalise empty_source_copy_run_mem
