(* Dispatch the two existing shared generated-loop assemblies. *)
Theory abiEncoderSharedArraySelectedLoop
Ancestors
  abiEncoderSharedArrayStaticLoop abiEncoderSharedArrayDynamicLoop
  abiEncoderSharedContract abiEncoderArrayPrefix abiScratchEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv
  valueEncoding contractABI venomState words list

Theorem abi_encoder_shared_array_selected_loop:
  abi_encoder_shared ei /\ (~active ==> abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
   else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (start,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id hi) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES, NOT_CLAUSES, IMP_CLAUSES] >> strip_tac
  >- (drule_all abi_encoder_shared_array_dynamic_loop >> simp[]) >>
  drule_all abi_encoder_shared_array_static_loop >> simp[]
QED
