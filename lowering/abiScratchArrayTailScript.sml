(* Execute the computed array tail cursor with the precise scratch footprint.
   TOP-LEVEL: abi_scratch_array_tail_reach establishes real containing-function
   execution; its allocation and store preserve every earlier cursor. *)
Theory abiScratchArrayTail
Ancestors
  abiScratchOwnedPrefix abiScratchSequence abiScratchPrefixReach abiScratchFootprint
  abiEncoderArrayTailInitSequence abiEncoderArrayTailInitCode abiEncoderSequenceReach
  abiEncoderComplexPrefixReach abiEncoderMembersDefs abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderLoop
  compileEnv venomState venomInst finite_map pred_set words list arithmetic

Theorem abi_scratch_array_tail_sequence:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual
Proof
  strip_tac >> drule abi_encode_array_tail_init_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`count_op` |-> `count_op`, `asz` |-> `asz:num`, `cnt` |-> `cnt:num`,
    `dyn_ptr` |-> `dyn_ptr`, `st` |-> `st:compile_state`, `st'` |-> `st':compile_state`,
    `limit_st` |-> `limit_st:compile_state`, `first` |-> `first:num`, `last` |-> `last:num`,
    `b` |-> `b:num`, `cap` |-> `cap:num`, `initial` |-> `initial:venom_state`]
    abi_encode_array_tail_init_sequence) >> impl_tac >- gvs[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  `actual.vs_alloca_next <= b+cap` by
    (fs[abi_encoder_complex_prefix_post_def, abi_decoder_budget_def] >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`emitted_insts st st'`, `initial`, `actual`,
       `abi_decoder_ids first last`, `b`, `cap`] abi_scratch_sequence_evolution) >> simp[]) >>
  `st.cs_next_id < st'.cs_next_id` by decide_tac >>
  drule_all abi_scratch_owned_prefix_frame >> disch_then assume_tac >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `site` |-> `st.cs_next_id`,
       `slot` |-> `slot`, `sz` |-> `32`, `s` |-> `initial:venom_state`,
       `t` |-> `actual:venom_state`] abi_scratch_final_slot_frame) >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_array_tail_reach:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  eval_operand count_op initial = SOME (n2w cnt) /\ abi_decoder_operand_live st.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
      st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
      initial actual /\
    (!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
      abi_encoder_cursor T op site slot first lo st' off actual) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_tail_sequence >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `actual = encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  `abi_encoder_complex_prefix_post [(AbiPrimWord,cnt*asz,0,F)] dyn_ptr
    st.cs_next_var st.cs_next_id limit_st first last b cap initial actual /\
   abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id) b cap initial)
    initial actual` by simp[Abbr`actual`, abi_scratch_inst_idx] >>
  `st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `!op site slot lo off. abi_encoder_cursor T op site slot first lo st off initial ==>
    abi_encoder_cursor T op site slot first lo st' off actual` by
    (rpt gen_tac >> strip_tac >> drule_all abi_scratch_owned_prefix_parent >> simp[]) >>
  qexists_tac `actual` >> gvs[Abbr`actual`, abi_scratch_inst_idx]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_TAIL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array tail not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayTail");
