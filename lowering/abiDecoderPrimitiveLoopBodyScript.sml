(* Actual address setup followed by the typed primitive child. The returned
   index remains available to the generated backedge on every iteration. *)
Theory abiDecoderPrimitiveLoopBody
Ancestors
  abiDecoderArrayChild abiDecoderArrayPrefix abiDecoderPrimitiveMemory abiDecoderStaticLoopSetup
  abiDecoderReentry abiDecoderGuards abiDecoderFrameCompose abiDecoderContract
  abiDecoderCoherence abiDecoderTypedContract abiDecoderDynamic abiDecoderLoopSetup
  exprLoweringProps emitHelperProps compileEnv valueEncoding venomState
  contractABI vyperTyping words arithmetic list

Theorem abi_decoder_primitive_loop_body:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decode_source_opcode opc /\ eval_operand ip initial = SOME p /\
  mload (w2n p) initial = n2w (LENGTH pre) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v (d + 32 + LENGTH pre * 32) actual.vs_memory /\
    (elems_in_memory vpre (d + 32) tv initial.vs_memory ==>
      elems_in_memory (vpre ++ [v]) (d + 32) tv actual.vs_memory) /\
    eval_operand (FST ops) actual = SOME (n2w (LENGTH pre)) /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame (d + 32 + LENGTH pre * 32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_dynarray_primitive_source >> strip_tac >>
  drule abi_decoder_primitive_memory_counters >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `~dec_info_needs_offset (DecPrimWord clamp)` by simp[abiEncoderTheory.dec_info_needs_offset_def] >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) initial = OK prepared` >>
  `mem_bytes_at (sb + 32 + LENGTH pre * 32) 32 (abi_decode_source opc prepared) =
    enc (vyper_to_abi_type env ty) av` by
    gvs[abi_decode_source_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`dst` |-> `SND (SND (ops:operand # operand # operand))`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `st` |-> `middle`, `initial` |-> `prepared`,
    `sb` |-> `sb + 32 + LENGTH (pre:abi_value list) * 32`,
    `d` |-> `d + 32 + LENGTH (pre:abi_value list) * 32`,
    `root_di` |-> `type_to_abi_dec_info ce.ce_struct_fields ce ty`]
    abi_decoder_primitive_memory_reentry) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle st') prepared = OK actual` >>
  `run_inst_seq (emitted_insts st st') initial = OK actual /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `middle`] >> simp[]) >>
  `st.cs_next_var <= middle.cs_next_var` by
    (drule_all abi_decode_static_element_setup_operands >> simp[]) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op initial = SOME w ==> eval_operand op actual = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live middle.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  `eval_operand (FST ops) actual = SOME (n2w (LENGTH pre))` by metis_tac[] >>
  `abi_decode_frame (d + 32 + LENGTH pre * 32) 32 initial actual` by
    (gvs[abi_decode_frame_def, Excl "enc_def"] >> first_assum ACCEPT_TAC) >>
  `all_have_type tv vpre` by
    fs[abi_decoder_metadata_def, Once value_has_type_def, all_have_type_EVERY, Excl "enc_def"] >>
  `elems_in_memory vpre (d + 32) tv initial.vs_memory ==>
   elems_in_memory (vpre ++ [v]) (d + 32) tv actual.vs_memory` by
    (strip_tac >> irule abi_decode_frame_append_element >> gvs[Excl "enc_def"] >>
     qexists_tac `initial` >> gvs[Excl "enc_def"]) >>
  qexists_tac `actual` >> gvs[Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop body not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopBody");
