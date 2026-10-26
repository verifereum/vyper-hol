(* The concrete increment/store/jump closes a primitive body iteration. *)
Theory abiDecoderPrimitiveLoopBackedge
Ancestors
  abiDecoderPrimitiveLoopReach abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopFrames
  abiDecoderPrimitiveLoopInvariant abiDecoderArrayBackedge abiDecoderArrayInvariant
  abiDecoderExecution abiDecoderLoop abiDecoderFrame abiDecoderReentry abiDecoderContract
  exprLoweringProps compileEnv valueEncoding venomExecSemantics venomState venomInst
  words list arithmetic
Libs
  Omega

Theorem abi_decoder_primitive_backedge_code:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\ abi_decode_source_opcode opc ==>
  ?bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id iv
        (STRING #"%" (toString st1.cs_next_var)) ip hdr /\
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions := abi_decode_header_insts hid ip src opc
        (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
        (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3)))
        st0.cs_current_bb exit_lbl|> /\
    phi_prefix_length (abi_decode_header_insts hid ip src opc
      (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
      (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3)))
      st0.cs_current_bb exit_lbl) = 0
Proof
  strip_tac >> drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  fs[abi_decoder_primitive_loop_compiled_def, abi_decoder_primitive_loop_code_def,
     abi_decode_loop_cfg_def] >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >> metis_tac[]
QED

Theorem abi_decoder_primitive_loop_separation:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp ==>
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot \/
    slot + 32 <= sb)
Proof
  strip_tac >> drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  `LENGTH vs * 32 <= maxn * 32` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decoder_primitive_loop_data_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[Excl "enc_def"] >> Omega.OMEGA_TAC
QED

Theorem abi_decoder_primitive_loop_backedge_reach:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_body_end opc (vyper_to_abi_type env ty) avs tv vs sb d
    first limit_st fp initial st1 iv j u /\ j < LENGTH vs ==>
  ?v. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr (SUC j) v /\ abi_decode_sim ctx fn u v
Proof
  strip_tac >>
  `abi_decode_source_opcode opc /\ slot < dimword (:256) /\ MEM (slot,32) fp` by
    fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_backedge_code >> strip_tac >>
  drule_all abi_decoder_primitive_loop_separation >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_primitive_body_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_body_end_def]) >>
  drule_all abi_decoder_loop_inputs_eval >> strip_tac >>
  `abi_decoder_operand_live first ip` by fs[abi_decoder_loop_inputs_def] >>
  `fresh_vars_wrt limit_st u` by fs[abi_decoder_loop_rel_def] >>
  `st1.cs_next_var < limit_st.cs_next_var` by fs[abi_decoder_primitive_loop_compiled_def] >>
  mp_tac (Q.INST [`fuel` |-> `0:num`, `s` |-> `u:venom_state`,
    `next` |-> `st1.cs_next_var`, `prefix` |-> `st1.cs_current_insts`,
    `id` |-> `st1.cs_next_id`, `aty` |-> `vyper_to_abi_type env ty`]
    abi_decoder_array_backedge) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_footprint_frame [(slot,32)] u v` >>
  `abi_decode_footprint_frame fp u v` by
    (drule_all abi_decoder_footprint_member_frame >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp u v` by
    (asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >>
     fs[abi_decoder_loop_rel_def]) >>
  `abi_decoder_loop_rel first limit_st fp initial v` by
    metis_tac[abi_decoder_loop_rel_trans] >>
  `ip <> Var (STRING #"%" (toString st1.cs_next_var))` by
    (drule_all abi_decoder_live_excludes_output >> simp[]) >>
  `abi_decode_sim ctx fn u v` by
    (qpat_assum `v = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule abi_decode_backedge_sim >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [abi_decoder_primitive_loop_inv_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_BACKEDGE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop backedge not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopBackedge");
