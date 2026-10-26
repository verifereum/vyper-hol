(* Select the actual proved static or dynamic array loop with precise resources.
   TOP-LEVEL: abi_scratch_array_selected_loop exposes a common executable
   interface for the complete parent array constructor. *)
Theory abiScratchArraySelectedLoop
Ancestors
  abiScratchArrayStaticLoop abiScratchArrayDynamicLoop abiScratchEncoderContract
  abiDecoderLoop abiDecoderReentry abiDecoderContract compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_array_selected_loop:
  (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  FIRST [drule_all abi_scratch_array_dynamic_loop, drule_all abi_scratch_array_static_loop] >>
  disch_then (qspec_then `ctx` assume_tac) >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_SELECTED_LOOP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch selected array loop not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArraySelectedLoop");
