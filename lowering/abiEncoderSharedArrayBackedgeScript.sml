(* Rich observations of the existing concrete ADD/MSTORE/JMP backedge. *)
Theory abiEncoderSharedArrayBackedge
Ancestors
  abiEncoderArrayBackedge abiEncoderSharedArrayEntry abiEncoderExtendSim
  abiEncoderVarTransport abiDecoderVarExtend execEquivParamDefs
  abiEncoderRegisteredEffect abiDecoderExecution abiDecoderArrayBackedge
  abiDecoderFootprint abiDecoderAllocation abiDecoderLoop abiDecoderContract
  abiDecoderReentry exprLoweringProps venomState venomExecSemantics venomMemDefs
  abiEncoderSharedContract abiEncoderOpenInputFrame abiScratchFootprint
  abiDecoderFrame valueEncodingProps valueEncoding finite_map pred_set words list arithmetic

Theorem abi_encoder_array_backedge_extend_state:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras
    (jump_to hdr (mstore slot w (update_var nv w s)))
    (jump_to hdr (mstore slot w (update_var nv w t)))
Proof
  strip_tac >> irule abi_encoder_array_jump_extend_state >>
  drule (Q.INST [`x` |-> `nv`, `v` |-> `w`] abi_decoder_vars_extend_update) >>
  simp[abi_decoder_vars_extend_def, vsr_frame_def, mstore_def,
    write_memory_with_expansion_def, update_var_def,
    venom_state_component_equality, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_encoder_array_backedge_extend_sim:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword (:256) ==>
  abi_encoder_extend_sim ctx func s
    (jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)))
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_extend_sim_def] >> conj_tac
  >- (drule_all abi_decode_backedge_sim >> simp[]) >>
  rpt strip_tac >> drule abi_encoder_vars_extend_control >> strip_tac >>
  `eval_operand (Var iv) t = SOME (n2w i) /\ eval_operand ip t = SOME p` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  qexists_tac `jump_to hdr (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) t))` >>
  conj_tac
  >- (irule abi_encoder_array_backedge_extend_state >> asm_rewrite_tac []) >>
  irule abi_decode_backedge_sim >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists_tac `ncount` >> simp[]) >>
  qexistsl_tac [`bb`,`id`,`ip`,`iv`,`prefix`] >> gvs[]
QED

Theorem abi_encoder_array_backedge_registered:
  site IN ids /\ FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  abi_encoder_registered_effect ids outs s
    (jump_to hdr (mstore slot w (update_var nv w s))) /\
  (alloca_inv s ==> alloca_inv (jump_to hdr (mstore slot w (update_var nv w s))))
Proof
  strip_tac >> conj_tac
  >- (`!a. (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
          a < b \/ b+sz <= a) ==>
        mem_bytes_at a 1 (mstore slot w s).vs_memory = mem_bytes_at a 1 s.vs_memory` by
        (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
         first_x_assum (qspec_then `site` mp_tac) >> simp[] >> decide_tac) >>
      fs[abi_encoder_registered_effect_def, jump_to_def, mstore_def,
        update_var_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_shared_array_backedge_reach:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  site IN ids /\ FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op s) /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s actual /\
    abi_encoder_registered_effect ids outs s actual /\ (alloca_inv s ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func s actual /\
    actual = jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))
Proof
  strip_tac >>
  drule_all (Q.INST [`fuel` |-> `0:num`] abi_encoder_array_backedge_execute) >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_extend_sim ctx func s actual` by
    (drule_all abi_encoder_array_backedge_extend_sim >>
     simp[w2n_n2w] >> gvs[]) >>
  `abi_encoder_registered_effect ids outs s actual /\ (alloca_inv s ==> alloca_inv actual)` by
    (gvs[] >> irule abi_encoder_array_backedge_registered >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_shared_input_registered_write:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) s /\
  first <= site /\ site < last /\ FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  abi_decode_footprint_frame [(slot,32)] s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) t
Proof
  strip_tac >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_registered_member >> simp[abi_decoder_ids_def] >>
     qexists_tac `site` >> simp[]) >>
  `abi_footprint_disjoint sb source_cap [(slot,32)]` by
    (fs[abi_footprint_disjoint_def] >> metis_tac[]) >>
  `mem_bytes_at sb source_cap s.vs_memory = mem_bytes_at sb source_cap t.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[]) >>
  `abi_encoder_open_input ei at av sb source_cap t.vs_memory` by
    (drule_all abi_encoder_open_input_mem_agree >> simp[]) >>
  simp[abi_encoder_shared_input_def] >> gvs[abi_decoder_child_scratch_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared backedge admission, axiom or hypothesis"
  end) [abi_encoder_array_backedge_extend_state, abi_encoder_array_backedge_extend_sim,
    abi_encoder_array_backedge_registered, abi_encoder_shared_array_backedge_reach,
    abi_encoder_shared_input_registered_write];
