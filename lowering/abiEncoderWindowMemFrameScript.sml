(* S3 endpoint preservation, independent of the S1 window result. *)
Theory abiEncoderWindowMemFrame
Ancestors
  abiEncoderWindowStatePreservation entryDecoderStateFrame abiDecoderVarSequence
  allocaHistoryFragment allocaHistory venomInstProofs1
  exprLoweringProps intCallCallee loweringHalt venomExecSemantics venomState venomInst list

Definition window_mem_frame_def:
  window_mem_frame ctx func s t <=>
    t.vs_code = s.vs_code /\
    t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_outcomes = s.vs_outcomes /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_fmp = s.vs_fmp /\
    (fmp_room ctx func s ==> fmp_room ctx func t) /\
    (alloca_history func s ==> alloca_history func t)
End

Theorem window_mem_frame_refl[simp]:
  window_mem_frame ctx func s s
Proof
  simp[window_mem_frame_def]
QED

Theorem window_mem_frame_trans:
  window_mem_frame ctx func s t /\ window_mem_frame ctx func t u ==>
  window_mem_frame ctx func s u
Proof
  simp[window_mem_frame_def] >> metis_tac[]
QED

Theorem window_mem_frame_static:
  window_mem_frame ctx func s t ==>
  t.vs_code = s.vs_code /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_data_section = s.vs_data_section /\
  t.vs_fmp = s.vs_fmp
Proof
  simp[window_mem_frame_def]
QED

Theorem window_mem_frame_room:
  window_mem_frame ctx func s t /\ fmp_room ctx func s ==>
  fmp_room ctx func t
Proof
  simp[window_mem_frame_def]
QED

Theorem window_mem_frame_history:
  window_mem_frame ctx func s t /\ alloca_history func s ==>
  alloca_history func t
Proof
  simp[window_mem_frame_def]
QED

Theorem window_mem_frame_sequence_code[local]:
  !code s t. EVERY (\i. ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK t ==> t.vs_code = s.vs_code
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem window_mem_frame_sequence:
  fn_inst_ids_distinct func /\ alloca_inv s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = code ++ rest /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) code /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode \/
    MEM i.inst_opcode [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP]) code /\
  run_inst_seq code s = OK t ==>
  window_mem_frame ctx func s
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all encoder_sequence_observations >> strip_tac >>
  drule_all window_mem_frame_sequence_code >> strip_tac >>
  gvs[entry_decoder_obs_def] >>
  simp[window_mem_frame_def] >> conj_tac
  >- metis_tac[abi_encoder_sequence_room] >>
  strip_tac >> drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem window_mem_frame_jump:
  window_mem_frame ctx func s (jump_to lbl s)
Proof
  simp[window_mem_frame_def, jump_to_def, fmp_room_def,
       pending_alloca_size_def] >>
  strip_tac >> irule alloca_history_jump >> simp[] >>
  qexists `s` >> simp[]
QED

Theorem window_mem_frame_control:
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK t ==> window_mem_frame ctx func s t
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> simp[window_mem_frame_jump]
QED

(* This covers both a fresh scratch allocation and reuse of its registered site. *)
Theorem window_mem_frame_scratch:
  fn_inst_ids_distinct func /\ alloca_inv s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    mk_inst id ALLOCA [Lit 32w] [out] :: rest /\
  MEM (mk_inst id ALLOCA [Lit 32w] [out]) (fn_insts func) ==>
  ?t. run_inst_seq [mk_inst id ALLOCA [Lit 32w] [out]] s = OK t /\
      window_mem_frame ctx func s
        (t with vs_inst_idx := s.vs_inst_idx + 1)
Proof
  strip_tac >>
  qspecl_then [`id`, `32w`, `out`, `s`] strip_assume_tac step_alloca_frame >>
  qexists `s1` >> conj_asm1_tac
  >- simp[run_inst_seq_def] >>
  `window_mem_frame ctx func s
    (s1 with vs_inst_idx := s.vs_inst_idx +
      LENGTH [mk_inst id ALLOCA [Lit 32w] [out]])` suffices_by simp[] >>
  irule window_mem_frame_sequence >>
  goal_assum (drule_at Any) >>
  simp[abi_decoder_reentry_opcode_def, mk_inst_def, is_terminator_def] >>
  metis_tac[]
QED
