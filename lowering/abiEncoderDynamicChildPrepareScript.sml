(* Establish the recursive child's pure precondition after emitted dynamic setup. *)
Theory abiEncoderDynamicChildPrepare
Ancestors
  abiEncoderChildPrefixReach abiEncoderChildPrefix abiEncoderChildCode abiEncoderChildInputs
  abiEncoderCorrect abiDecoderEffect abiDecoderArrayInitExec abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding
  venomState words list arithmetic

Theorem abi_encoder_dynamic_child_prepare:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_pre ei at av prepared src (SND (SND ops))
      sb source_cap (d+off) b cap ready /\
    eval_operand (FST ops) ready = SOME (n2w (d+head_offset)) /\
    eval_operand (FST (SND ops)) ready = SOME (n2w off) /\
    abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
    abi_decoder_operand_live prepared.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live prepared.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_prefix_live >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`, `db` |-> `d:num`] abi_encode_child_prefix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_encoder_pre ei at av prepared src (SND (SND ops)) sb source_cap (d+off) b cap ready` by
    (mp_tac (Q.INST [`child_st` |-> `prepared`, `child_dst` |-> `SND (SND (ops:operand # operand # operand))`,
      `actual` |-> `ready:venom_state`, `offset` |-> `off:num`] abi_encoder_child_pre_address) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- fs[abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_DYNAMIC_CHILD_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic child preparation not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderDynamicChildPrepare");
