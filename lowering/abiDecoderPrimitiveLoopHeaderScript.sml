(* The generated header preserves the full loop invariant and selects its edge. *)
Theory abiDecoderPrimitiveLoopHeader
Ancestors
  abiDecoderPrimitiveLoopInvariant abiDecoderLoopRegisters abiDecoderArrayInvariant
  abiDecoderArrayBackedge abiDecoderReentry abiDecoderExecution abiDecoderLoop
  abiDecoderFrame abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv venomState words arithmetic

Theorem abi_decoder_footprint_frame_jump[simp]:
  abi_decode_footprint_frame fp s (jump_to lbl t) <=> abi_decode_footprint_frame fp s t
Proof
  simp[abi_decode_footprint_frame_def, jump_to_def]
QED

Theorem abi_decoder_loop_rel_header:
  first + 4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  abi_decoder_loop_rel first limit_st fp s
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) i ncount s))
Proof
  strip_tac >> drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `h = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
    (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
    (STRING #"%" (toString (first+3))) i ncount s)` >>
  `fresh_vars_wrt limit_st h` by simp[Abbr`h`] >>
  `!op. abi_decoder_operand_live first op ==> eval_operand op h = eval_operand op s` by
    asm_simp_tac bool_ss [Abbr`h`, abi_decoder_operand_jump] >>
  `h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
   h.vs_halted = s.vs_halted` by
    simp[Abbr`h`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  `abi_decode_footprint_frame fp s h` by
    (simp_tac bool_ss [Abbr`h`, abi_decoder_footprint_frame_jump] >>
     irule (cj 1 abi_decode_header_observations)) >>
  asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >> metis_tac[]
QED

Theorem abi_decoder_primitive_loop_header:
  abi_decoder_primitive_loop_inv opc aty avs tv vs sb d slot first limit_st fp initial hdr j s /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  LENGTH avs = LENGTH vs /\ LENGTH vs < dimword (:256) /\ slot < dimword (:256) /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) /\
  abi_decode_source_opcode opc /\ first + 4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first ip /\
  eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) ==>
  ?h. abi_decoder_primitive_loop_inv opc aty avs tv vs sb d slot first limit_st fp
      initial (if j < LENGTH vs then body_lbl else exit_lbl) j h /\ abi_decode_sim ctx fn s h
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_inv_def]) >>
  `fresh_vars_wrt limit_st s` by fs[abi_decoder_loop_rel_def] >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    metis_tac[abi_decoder_loop_rel_eval] >>
  drule_all abi_decoder_array_memory_count >> strip_tac >>
  `abi_decode_loop_ready hdr ip src opc (n2w slot) (n2w sb) (LENGTH vs) j s` by
    fs[abi_decode_loop_ready_def, abi_decoder_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `src <> Var (STRING #"%" (toString first))` by
    (mp_tac (Q.INST [`next` |-> `first:num`, `op` |-> `src:operand`]
       abi_decoder_live_excludes_output) >> simp[]) >>
  `STRING #"%" (toString (first:num)) <> STRING #"%" (toString (first+1))` by simp[] >>
  qabbrev_tac `h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  `abi_decode_sim ctx fn s h` by
    (drule_all abi_decode_ready_header_sim >> simp[Abbr`h`]) >>
  `abi_decoder_loop_rel first limit_st fp s h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_decoder_loop_rel_header >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp initial h` by
    (drule_all abi_decoder_loop_rel_trans >> simp[]) >>
  qexists_tac `h` >>
  asm_simp_tac (srw_ss()) [abi_decoder_primitive_loop_inv_def, Abbr`h`,
    abi_decode_mload_jump, abi_decode_header_state_def, abi_decode_load_update,
    Excl "enc_def"] >>
  simp[jump_to_def, update_var_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop header not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopHeader");
