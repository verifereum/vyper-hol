(* Finite fetched decoder paths, including real block transitions. *)
Theory abiDecoderFiniteControl
Ancestors
  abiDecoderSequenceReach abiDecoderExecution fragExec venomExecSemantics
  venomExecProofs venomInstProofs venomState venomInst relation arithmetic

Definition Dedge_def:
  Dedge ctx fn s t <=>
    decoder_straight_step fn s t \/
    (~s.vs_halted /\ ?bb target.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      (!fuel. exec_block fuel ctx bb s = OK t) /\
      ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
      phi_prefix_length target.bb_instructions = 0)
End

Definition Dreach_def:
  Dreach ctx fn = RTC (Dedge ctx fn)
End

Definition Dabort_def:
  Dabort ctx fn s a t <=> ?fuel. run_from fuel ctx fn s = Abort a t
End

Theorem decoder_straight_step_run_from:
  decoder_straight_step fn s t ==>
  !fuel. run_from fuel ctx fn s = run_from fuel ctx fn t
Proof
  rw[decoder_straight_step_def, block_step_def] >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  rename1 `step_inst_base inst s = OK u` >>
  `u.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  simp[next_inst_def, GSYM ADD1] >> irule run_from_step >> metis_tac[]
QED

Theorem Dedge_fuel:
  Dedge ctx fn s t ==>
  ?k. !fuel. run_from (k + fuel) ctx fn s = run_from fuel ctx fn t
Proof
  rw[Dedge_def]
  >- (qexists_tac `0` >> simp[decoder_straight_step_run_from]) >>
  qexists_tac `1` >> gen_tac >>
  `run_blocks (SUC fuel) ctx fn t = run_from fuel ctx fn t` by
    (drule_all run_blocks_run_from_no_phi >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_from_def])) >>
  simp[GSYM ADD1]
QED

Theorem Dreach_refl:
  Dreach ctx fn s s
Proof
  simp[Dreach_def]
QED

Theorem Dreach_trans:
  Dreach ctx fn s t /\ Dreach ctx fn t u ==> Dreach ctx fn s u
Proof
  metis_tac[Dreach_def, RTC_TRANSITIVE, transitive_def]
QED

Theorem Dreach_edge:
  Dedge ctx fn s t ==> Dreach ctx fn s t
Proof
  simp[Dreach_def, RTC_SINGLE]
QED

Theorem Dreach_straight_prefix:
  decoder_straight_prefix fn s t ==> Dreach ctx fn s t
Proof
  simp[decoder_straight_prefix_def, Dreach_def] >>
  map_every qid_spec_tac [`t`, `s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[Dreach_def, RTC_REFL] >>
  metis_tac[Dedge_def, RTC_RULES]
QED

Theorem Dreach_fuel:
  Dreach ctx fn s t ==>
  ?k. !fuel. run_from (k + fuel) ctx fn s = run_from fuel ctx fn t
Proof
  simp[Dreach_def] >>
  map_every qid_spec_tac [`t`, `s`] >>
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (gen_tac >> qexists_tac `0` >> simp[]) >>
  rpt strip_tac >> drule Dedge_fuel >> strip_tac >>
  qexists_tac `k' + k` >> gen_tac >>
  `fuel + (k' + k) = k' + (fuel + k)` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem Dreach_abort:
  Dreach ctx fn s t /\ Dabort ctx fn t a u ==> Dabort ctx fn s a u
Proof
  rw[Dabort_def] >> drule Dreach_fuel >> strip_tac >>
  qexists_tac `k + fuel` >> simp[]
QED

Theorem Dreach_position_ready_header:
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl id ip src opc base_op first /\
  abi_decode_position_loop_ready hdr ip src opc base_op B sb p ncount j s /\
  abi_decode_source_opcode opc /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  ncount < dimword(:256) ==>
  Dreach ctx fn s
    (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb j ncount s))
Proof
  strip_tac >> irule Dreach_edge >> rewrite_tac[Dedge_def] >> disj2_tac >>
  gvs[abi_decode_position_loop_cfg_def, abi_decode_position_loop_ready_def] >>
  Cases_on `j < ncount` >>
  (qexists_tac `if j < ncount then bb else bb'` >>
   Cases_on `base_op = Lit 0w` >>
   simp[jump_to_def, abi_decode_position_header_state_def, update_var_def] >>
   gen_tac >> drule_all abi_decode_position_header_control >>
   simp[jump_to_def, abi_decode_position_header_state_def, update_var_def])
QED

Theorem Dreach_backedge:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  Dreach ctx fn s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i))
      (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> irule Dreach_edge >> rewrite_tac[Dedge_def] >> disj2_tac >>
  simp[jump_to_def, mstore_def, update_var_def] >>
  gen_tac >> drule_all abi_decode_backedge_control >>
  simp[jump_to_def, mstore_def, update_var_def]
QED
