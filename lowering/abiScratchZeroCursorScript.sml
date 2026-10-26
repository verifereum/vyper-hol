(* A real zero cursor initializer preserves any complete encoder input.
   TOP-LEVEL: abi_scratch_zero_cursor_prepare exposes the registered cursor,
   complete buffer contract and owned effect for array and member encoders. *)
Theory abiScratchZeroCursor
Ancestors
  abiScratchOwnedPrefix abiScratchPrefixEffect abiScratchInputEffect abiScratchEncoderContract
  abiEncoderComplexPrefix abiEncoderMembersDefs abiDecoderReentry abiDecoderLoop
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_zero_cursor_prepare:
  abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (cursor_op,prepared) /\
  fn_has_code st prepared func /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. abi_scratch_input ei at av prepared src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_cursor T cursor_op st.cs_next_id slot first st.cs_next_id prepared 0 actual /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`infos` |-> `[]:(abi_enc_info # num # num # bool) list`, `dyn_ptr` |-> `cursor_op:operand`,
    `next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`, `stop` |-> `prepared.cs_next_id`,
    `sz` |-> `output_size:num`] abi_scratch_prefix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  rename1 `abi_encoder_cursor T cursor_op st.cs_next_id slot first st.cs_next_id prepared _ actual` >>
  `abi_scratch_input ei at av prepared src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ZERO_CURSOR_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch zero cursor initialization not kernel closed: " ^ n)
  end) (DB.thms "abiScratchZeroCursor");
