(* Concrete header observations and extension stability on both selected edges. *)
Theory abiEncoderSharedArrayHeader
Ancestors
  abiEncoderArrayHeader abiEncoderArrayHeaderFrame abiEncoderExtendSim abiEncoderVarTransport
  abiEncoderRegisteredEffect abiDecoderVarExtend execEquivParamDefs
  abiDecoderLoop abiDecoderContract venomState venomExecSemantics venomMemDefs
  words list arithmetic

Theorem abi_encoder_array_header_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras
    (jump_to label (abi_encode_array_header_state iv cmp done i n s))
    (jump_to label (abi_encode_array_header_state iv cmp done i n t))
Proof
  strip_tac >>
  `abi_decoder_vars_extend extras (abi_encode_array_header_state iv cmp done i n s)
    (abi_encode_array_header_state iv cmp done i n t)` by
    (simp_tac bool_ss [abi_encode_array_header_state_def] >>
     rpt (irule abi_decoder_vars_extend_update) >> asm_rewrite_tac []) >>
  pop_assum mp_tac >>
  simp[abi_decoder_vars_extend_def, jump_to_def, vsr_frame_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_array_header_extend_sim:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  abi_encoder_extend_sim ctx func s (jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_encode_array_header_sim >> simp[]) >>
  rpt strip_tac >>
  drule abi_encoder_vars_extend_control >> strip_tac >>
  `eval_operand ip t = SOME p /\ eval_operand count_op t = SOME (n2w n)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  `s.vs_memory = t.vs_memory` by
    fs[abi_decoder_vars_extend_def, vsr_frame_def, venom_state_component_equality,
      Excl "vsr_complete_mask_equality"] >>
  `mload (w2n p) t = n2w i` by fs[mload_def] >>
  qexists_tac `jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n t)` >> conj_tac
  >- (irule abi_encoder_array_header_extend_state >> asm_rewrite_tac []) >>
  gvs[] >>
  irule abi_encode_array_header_sim >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`count_op`,`id`,`ip`] >> simp[]
QED

Theorem abi_encoder_array_header_registered:
  abi_encoder_registered_effect ids outs s
    (jump_to label (abi_encode_array_header_state iv cmp done i n s)) /\
  (alloca_inv s ==> alloca_inv (jump_to label (abi_encode_array_header_state iv cmp done i n s)))
Proof
  simp[abi_encoder_registered_effect_def, jump_to_def, abi_encode_array_header_state_def,
    update_var_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array header admission, axiom or hypothesis"
  end) [abi_encoder_array_header_extend_state, abi_encoder_array_header_extend_sim,
    abi_encoder_array_header_registered];
