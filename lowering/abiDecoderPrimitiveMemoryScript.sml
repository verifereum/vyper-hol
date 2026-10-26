(* Primitive children need canonical words and an output address, without any
   scratch reservation. This boundary is used inside repeated array bodies. *)
Theory abiDecoderPrimitiveMemory
Ancestors
  abiDecoderReentryPrimitive abiDecoderReentryPrefix abiDecoderReentrySequence
  abiDecoderReentry abiDecoderVarExtend abiDecoderPrimitiveClamp abiDecoderWordTyped
  abiDecoderClampedWord abiDecoderTypedCompose abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract exprLoweringProps emitHelperProps compileEnv valueEncoding
  abiEncoder abiDecoderClamp emitHelper venomState words arithmetic

Theorem abi_decoder_primitive_memory_counters:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') ==>
  st.cs_next_var <= st'.cs_next_var
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_decoder_primitive_memory_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory tv v d t.vs_memory /\ abi_decode_frame d 32 s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_primitive_clamp >> strip_tac >>
  drule_all abi_decoder_clamped_word_copied_window >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mem_bytes_at d 32 t.vs_memory = enc (vyper_to_abi_type env ty) av` by metis_tac[] >>
  drule_all abi_decoder_primitive_canonical_layout >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends st st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_primitive_memory_reentry:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc initial) = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w d)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `mem_bytes_at sb 32 (abi_decode_source opc (abi_decoder_prune_vars st.cs_next_var initial)) =
    enc (vyper_to_abi_type env ty) av` by simp[] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  drule_all abi_decoder_primitive_memory_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive memory boundary not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveMemory");
