(* Both actual loop initializers establish the precise executable loop entry.
   TOP-LEVEL: abi_scratch_array_dynamic_init_prepare retains complete buffers,
   initializes distinct index/tail cursors and composes their owned effects. *)
Theory abiScratchArrayDynamicInitPrepare
Ancestors
  abiScratchArrayInitEffects abiScratchEncoderContract abiScratchEffectProtected
  abiScratchEffectWiden abiScratchEffectCompose abiEncoderArrayDynamicInitContext
  abiEncoderMembersDefs abiEncoderInputLayout abiDecoderReentry abiDecoderLoop
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_array_dynamic_init_prepare:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func /\
  abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\ abi_decoder_operand_live start.cs_next_var count_op /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  owner_st.cs_next_id <= hi /\ hi <= last /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?ready index_slot tail_slot.
    abi_scratch_input (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap ready /\
    abi_encoder_array_prefix ty avs 0 d ready.vs_memory /\
    abi_encoder_cursor T (FST ptrs) start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready /\
    abi_encoder_cursor T (SND ptrs) (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
      (LENGTH avs*abi_member_head_size ty) ready /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = owner_st.cs_current_bb /\ ready.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
  `after_index.cs_next_var <= limit_st.cs_next_var /\ after_index.cs_next_id <= last /\
   first <= after_index.cs_next_id /\ owner_st.cs_next_id <= last /\
   start.cs_next_var <= after_index.cs_next_var` by decide_tac >>
  `asz = abi_member_head_size ty` by fs[abi_scratch_input_def, abi_encoder_array_input_iff] >>
  mp_tac (Q.INST [`st` |-> `start`, `st'` |-> `after_index`, `active` |-> `T`, `index_ptr` |-> `ip:operand`]
    abi_scratch_array_index_prepare) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial indexed` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id after_index 0 indexed` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial indexed`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op indexed = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live after_index.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `after_index`, `st'` |-> `owner_st`, `active` |-> `T`,
    `initial` |-> `indexed:venom_state`] abi_scratch_array_tail_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func indexed ready` >>
  rename1 `abi_encoder_cursor T dyn_ptr after_index.cs_next_id tail_slot first after_index.cs_next_id
    owner_st (LENGTH avs*asz) ready` >>
  `abi_encoder_cursor T ip start.cs_next_id index_slot first start.cs_next_id owner_st 0 ready` by
    (qpat_assum `!op cursor_site cursor_slot cursor_lo off. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_encoder_cursor T dyn_ptr (start.cs_next_id+2) tail_slot first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by
    (gvs[abi_encoder_cursor_def] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial indexed` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `after_index.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap indexed ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `after_index.cs_next_id`, `after_index.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `indexed` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`ready`, `index_slot`, `tail_slot`] >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `indexed` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_DYNAMIC_INIT_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complete initializer preparation not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayDynamicInitPrepare");
