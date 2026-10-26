(* Compose the real allocator with initialization frames, including reused sites. *)
Theory abiEmptyAllocateEffect
Ancestors
  abiEmptyEffect abiBuiltinAllocationState abiDecoderReentry abiDecoderContract
  exprLoweringProps compileEnv venomState finite_map

Theorem abi_empty_allocate_state_observation:
  (abi_builtin_allocate_state site outsz s).vs_memory = s.vs_memory /\
  (abi_builtin_allocate_state site outsz s).vs_call_ctx = s.vs_call_ctx /\
  (abi_builtin_allocate_state site outsz s).vs_data_section = s.vs_data_section /\
  (abi_builtin_allocate_state site outsz s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (abi_builtin_allocate_state site outsz s) = eval_operand op s)
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, eval_operand_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_empty_allocation_effect:
  abi_builtin_allocation_frame first site outsz initial prepared /\
  abi_empty_effect next p written limit_st prepared actual /\ first <= next ==>
  abi_empty_effect first p written limit_st
    (abi_builtin_allocate_state site outsz initial) actual
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def, abi_empty_effect_def] >> strip_tac >>
  `abi_decode_frame p written (abi_builtin_allocate_state site outsz initial) actual` by
    (qpat_x_assum `abi_decode_frame p written prepared actual` mp_tac >>
     asm_simp_tac bool_ss [abi_decode_frame_def, abi_empty_allocate_state_observation] >>
     strip_tac >> asm_rewrite_tac[]) >>
  asm_simp_tac bool_ss [abi_empty_allocate_state_observation] >>
  rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
  qpat_x_assum `!op w. abi_decoder_operand_live next op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `!op w. abi_decoder_operand_live first op /\ _ ==> _` irule >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_ALLOCATE_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty allocation effect not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyAllocateEffect");
