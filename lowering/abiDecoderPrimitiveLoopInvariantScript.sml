(* State and code invariants for a complete primitive-element decoder loop. *)
Theory abiDecoderPrimitiveLoopInvariant
Ancestors
  abiDecoderArrayInvariant abiDecoderArrayIteration abiDecoderPrimitiveLoopFragment
  abiDecoderStaticLoopSetup abiDecoderPrimitiveMemory abiDecoderDynamic
  abiDecoderExecution abiDecoderFrame abiDecoderReentry fragExec
  emitHelperProps exprLoweringProps compileEnv venomState venomInst
  words list rich_list arithmetic

Definition abi_decoder_loop_rel_def:
  abi_decoder_loop_rel first limit_st fp initial s <=>
    fresh_vars_wrt limit_st s /\
    (!op w. abi_decoder_operand_live first op /\ eval_operand op initial = SOME w ==>
      eval_operand op s = SOME w) /\
    s.vs_allocas = initial.vs_allocas /\ s.vs_alloca_next = initial.vs_alloca_next /\
    s.vs_halted = initial.vs_halted /\ abi_decode_footprint_frame fp initial s
End

Theorem abi_decoder_loop_rel_refl:
  fresh_vars_wrt limit_st s ==> abi_decoder_loop_rel first limit_st fp s s
Proof
  simp[abi_decoder_loop_rel_def, abi_decode_footprint_frame_refl]
QED

Theorem abi_decoder_loop_rel_trans:
  abi_decoder_loop_rel first limit_st fp s t /\
  abi_decoder_loop_rel first limit_st fp t u ==>
  abi_decoder_loop_rel first limit_st fp s u
Proof
  simp_tac bool_ss [abi_decoder_loop_rel_def] >> strip_tac >>
  metis_tac[abi_decode_footprint_frame_trans]
QED

Theorem abi_decoder_loop_rel_eval:
  abi_decoder_loop_rel first limit_st fp initial s /\
  abi_decoder_operand_live first op /\ eval_operand op initial = SOME w ==>
  eval_operand op s = SOME w
Proof
  simp_tac bool_ss [abi_decoder_loop_rel_def] >> metis_tac[]
QED

Theorem abi_decoder_loop_rel_intro:
  first <= next /\ fresh_vars_wrt limit_st t /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_halted = s.vs_halted /\ abi_decode_footprint_frame fp s t ==>
  abi_decoder_loop_rel first limit_st fp s t
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >> rpt strip_tac >>
  `abi_decoder_operand_live next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >> metis_tac[]
QED

Definition abi_decoder_primitive_loop_inv_def:
  abi_decoder_primitive_loop_inv opc aty avs tv vs sb d slot first limit_st fp
      initial hdr j s <=>
    abi_decoder_array_memory opc aty avs tv vs sb d j s /\
    abi_decoder_loop_rel first limit_st fp initial s /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    mload slot s = n2w j
End

Definition abi_decoder_primitive_loop_code_def:
  abi_decoder_primitive_loop_code fn st0 st1 (ops:operand # operand # operand)
      ip src opc hdr exit_lbl hid first iv <=>
    st0.cs_current_insts = [] /\ first + 4 <= st0.cs_next_var /\
    FST ops = Var iv /\
    abi_decode_loop_cfg fn hdr st0.cs_current_bb exit_lbl hid ip src opc
      (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
      (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
    (?bb. lookup_block st0.cs_current_bb fn.fn_blocks = SOME bb /\
      bb.bb_instructions = st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id iv
          (STRING #"%" (toString st1.cs_next_var)) ip hdr)
End

Theorem abi_decoder_primitive_body_counters:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st1) ==>
  st0.cs_next_var + 7 <= st1.cs_next_var
Proof
  strip_tac >>
  `~dec_info_needs_offset (DecPrimWord clamp)` by simp[abiEncoderTheory.dec_info_needs_offset_def] >>
  drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  drule abi_decoder_primitive_memory_counters >> strip_tac >> decide_tac
QED

Theorem abi_decoder_primitive_body_contained:
  abi_decoder_primitive_loop_code fn st0 st1 ops ip src opc hdr exit_lbl hid first iv /\
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st1) /\ abi_decode_source_opcode opc ==>
  fn_has_code st0 st1 fn
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  qpat_x_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_primitive_loop_code_def] >> strip_tac >>
  rename1 `lookup_block st0.cs_current_bb fn.fn_blocks = SOME body_bb` >>
  simp[fn_has_code_def, emitted_blocks_def] >>
  qexists_tac `body_bb` >> simp[IS_PREFIX_APPEND]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_INVARIANT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop invariant not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopInvariant");
