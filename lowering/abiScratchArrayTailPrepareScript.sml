(* Execute the actual cursor load and dynamic child destination calculation.
   TOP-LEVEL: abi_scratch_array_tail_prepare derives the recursive child's
   exact input from physical parent buffers and actual address execution. *)
Theory abiScratchArrayTailPrepare
Ancestors
  abiScratchChildInput abiScratchEncoderContract abiScratchAddress abiScratchFootprint
  abiEncoderArrayTail abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop
  compileEnv valueEncoding contractABI venomState words arithmetic list

Theorem abi_scratch_array_tail_prepare:
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ slot < dimword (:256) /\
  off+LENGTH (enc at av) <= output_size /\ abi_decoder_budget first last b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
      (LENGTH (enc at av)) first last b cap actual /\
    eval_operand (FST ops) actual = SOME (n2w off) /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    abi_decoder_operand_live prepared.cs_next_var (FST ops) /\
    abi_decoder_operand_live prepared.cs_next_var (SND ops) /\
    abi_decoder_operand_live prepared.cs_next_var dyn_ptr /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `prepared`] abi_encode_array_tail_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`,
    `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
    abi_scratch_address) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_input ei at av prepared src (SND ops) sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap actual` by
    (mp_tac (Q.INST [`dst` |-> `data_op:operand`, `child_dst` |-> `SND (ops:operand # operand)`]
       abi_scratch_child_input_address) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr actual = SOME (n2w slot)` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_TAIL_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array tail preparation not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayTailPrepare");
