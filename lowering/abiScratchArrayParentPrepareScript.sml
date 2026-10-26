(* Execute the actual parent allocation and count copy with precise resources.
   TOP-LEVEL: abi_scratch_array_parent_prepare establishes complete loop input,
   the zero parent cursor, the copied count and one composed owned effect. *)
Theory abiScratchArrayParentPrepare
Ancestors
  abiScratchZeroCursor abiScratchArrayCountPrepare abiScratchCursor abiScratchEncoderContract
  abiScratchEffectWiden abiScratchEffectCompose abiEncoderArrayParentPrepare abiEncoderArrayCursor
  abiEncoderMembersDefs abiDecoderReentry abiDecoderLoop abiDecoderContract
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_array_parent_prepare:
  abi_encode_array_prefix src dst st = (ops,loop_st) /\ fn_has_code st loop_st func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= hi /\ hi <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      loop_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T (FST ops) st.cs_next_id slot first st.cs_next_id loop_st 0 actual /\
    abi_decoder_operand_live loop_st.cs_next_var (SND ops) /\
    eval_operand (SND ops) actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = loop_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_prefix_context >> strip_tac >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ allocated.cs_next_id <= last /\
   loop_st.cs_next_id <= last /\ first <= allocated.cs_next_id /\ st.cs_next_id < last /\
   st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= loop_st.cs_next_var /\
   allocated.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `cursor_op` |-> `parent_ptr:operand`, `prepared` |-> `allocated`]
    abi_scratch_zero_cursor_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial allocated_state` >>
  rename1 `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id allocated 0 allocated_state` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  mp_tac (Q.INST [`st` |-> `allocated`, `st'` |-> `loop_st`, `initial` |-> `allocated_state:venom_state`]
    abi_scratch_array_count_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ allocated _ _ _ _ _ _ _ _ _ _ allocated_state`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr:operand`, `site` |-> `st.cs_next_id`,
    `lo` |-> `st.cs_next_id`, `st` |-> `allocated`, `off` |-> `0:num`, `sz` |-> `output_size:num`,
    `owned_lo` |-> `allocated.cs_next_id`, `owned_hi` |-> `loop_st.cs_next_id`, `next` |-> `allocated.cs_next_var`,
    `initial` |-> `allocated_state:venom_state`] abi_scratch_cursor_protected) >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  `abi_encoder_cursor T parent_ptr st.cs_next_id slot first st.cs_next_id loop_st 0 actual` by
    (irule abi_encoder_cursor_mono >> qexists_tac `allocated` >> asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial allocated_state` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `allocated.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap allocated_state actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `allocated.cs_next_id`, `allocated.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id hi st.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `allocated_state` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `allocated_state` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_PARENT_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual parent initialization not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayParentPrepare");
