Theory bodyFullAbiDecodeCutFirstJump
Ancestors
  abiEncoderObserver exprSimAbiGasBridge fragExec emitHelper
  venomState venomInst venomExecSemantics

(* The shadow enters the actual header from L.  Its predecessor is not
   replaced by the original entry label when relating the two endpoints. *)
Theorem abi_decode_cut_first_jump:
  frag_relabel_state L entry u t /\
  u.vs_current_bb = L /\ ~u.vs_halted /\ (L,u.vs_inst_idx) <> cut /\
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) /\
  hdr <> L /\ lookup_block hdr obs.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  abi_observer_step ctx obs cut u (jump_to hdr u) /\
  frag_relabel_state L entry (jump_to hdr u) (jump_to hdr t) /\
  (jump_to hdr u).vs_prev_bb = SOME L
Proof
  strip_tac >> conj_tac
  >- simp[abi_observer_step_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          mk_inst_def, is_terminator_def, jump_to_def, eval_phis_no_phi] >>
  simp[jump_to_def] >>
  qpat_x_assum `frag_relabel_state L entry u t` mp_tac >>
  simp[frag_relabel_state_def] >> strip_tac >>
  qexists `SOME entry` >>
  simp[jump_to_def, venom_state_component_equality]
QED
