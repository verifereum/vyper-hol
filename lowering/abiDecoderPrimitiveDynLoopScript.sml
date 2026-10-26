(* Typed finite execution for an actual compiled primitive-element dynamic loop. *)
Theory abiDecoderPrimitiveDynLoop
Ancestors
  abiDecoderPrimitiveLoopLayout abiDecoderPrimitiveLoopFinite abiDecoderLoopEmit
  abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopInvariant abiDecoderLoop
  fragExec compileEnv valueEncoding venomState words list arithmetic

Theorem abi_decoder_primitive_loop_compiled_mono:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv bounded /\ bounded.cs_next_var <= limit_st.cs_next_var ==>
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st
Proof
  simp_tac bool_ss [abi_decoder_primitive_loop_compiled_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_decoder_primitive_dyn_loop_from_header:
  compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 ip cnt
    start = ((),end_st) /\ fn_has_code start end_st fn /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs start.cs_next_var ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    start.cs_next_var limit_st fp initial
    (fresh_label_output "dec_dyn_hdr" start.cs_next_label) i s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_loop_rel start.cs_next_var limit_st fp initial t /\
    t.vs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\ mload slot t = n2w (LENGTH vs) /\
    abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_primitive_loop_layout >> strip_tac >>
  `abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    (FST labels) (SND (SND labels)) (start.cs_next_id + 1) start.cs_next_var
    (STRING #"%" (toString st0.cs_next_var)) limit_st` by
    (irule abi_decoder_primitive_loop_compiled_mono >> qexists_tac `end_st` >> simp[]) >>
  qpat_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[] >>
  drule_all abi_decoder_primitive_loop_typed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_DYN_LOOP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive dynamic loop not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveDynLoop");
