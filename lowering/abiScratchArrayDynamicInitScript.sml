(* Complete execution of the actual dynamic-array loop initializer.
   TOP-LEVEL: abi_scratch_array_dynamic_init composes index and tail allocation,
   preserving source data, processed output, parent cursor and older operands. *)
Theory abiScratchArrayDynamicInit
Ancestors
  abiScratchArrayIndex abiScratchArrayTailInput abiScratchCompose abiScratchFootprint
  abiEncoderArrayDynamicInitContext abiEncoderComplexPrefixReach abiEncoderMembersDefs
  abiEncoderInput abiEncoderArrayPrefix abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderLoop compileEnv valueEncoding
  contractABI venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_array_dynamic_init:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
  fn_has_code start owner_st func /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ owner_st.cs_next_id <= last /\
  owner_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T parent_ptr parent_site parent_slot first lo start off initial /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual index_slot tail_slot.
    abi_encoder_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_encoder_cursor T parent_ptr parent_site parent_slot first lo owner_st off actual /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id
      owner_st 0 actual /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first (start.cs_next_id+2)
      owner_st (LENGTH avs*asz) actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
    (!op. abi_decoder_operand_live start.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    actual.vs_current_bb = owner_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  drule_all abi_scratch_array_index >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial indexed` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 indexed` >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >> simp[]) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule_all (Q.INST [`initial` |-> `indexed:venom_state`] abi_scratch_array_tail_input) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func indexed actual` >>
  rename1 `abi_encoder_cursor T dyn_ptr after_index.cs_next_id tail_slot first after_index.cs_next_id
    owner_st (LENGTH avs*asz) actual` >>
  `abi_encoder_cursor T parent_ptr parent_site parent_slot first lo owner_st off actual` by
    (qpat_assum `!op site slot lo off. _` drule_all >> simp[]) >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 actual` by
    (qpat_assum `!op site slot lo off. _` drule_all >> simp[]) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual` by
    (drule_all abi_scratch_frame_trans >> simp[]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op actual = eval_operand op initial` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live after_index.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
     qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ initial indexed`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ indexed actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
     asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `index_slot`, `tail_slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `indexed` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_DYNAMIC_INIT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array dynamic initializer not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayDynamicInit");
