Theory calldataScratchArrayConstructorPtr
Ancestors
  calldataScratchArrayEntryPtr calldataScratchArrayCompletePtr calldataScratchLoopEntryPtr arithmetic abiScratchEffect
  abiScratchDecoderLoopInvariant abiDecoderLoopEmit abiDecoderRecursiveLoopContext
  abiDecoderLoop abiDecoderExecution abiDecoderReentry abiDecoderFrame compileEnv venomState bodyPtrDefs ptrDiscipline pred_set finite_map list

Theorem calldata_scratch_array_constructor_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) start = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) start src (Var root) CALLDATALOAD (Lit 0w)
    sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  loop_st.cs_next_id <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ fn_has_code start loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  compile_abi_decode_dyn_loop (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (FST setup) (SND setup) loop_st = ((),final) /\
  fn_has_code loop_st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < loop_st.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  fn_inst_ids_distinct func /\ DISJOINT P tn.t_mem /\ start.cs_next_id <= lo /\
  hi <= final.cs_next_id /\ loop_st.cs_next_id <= final.cs_next_id /\
  start.cs_next_var <= loop_st.cs_next_var ==>
  ?t H u.
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem) /\
    abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ ~t.vs_halted /\
    abi_decode_sim ctx func initial t /\
    ptr_covers H u root t (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x t = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower t /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id final.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP t.vs_allocas site = SOME (slot,32) /\
      mload slot t = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_scratch_array_constructor_entry_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `DISJOINT P u.t_mem` by
    (qpat_assum `DISJOINT P tn.t_mem` mp_tac >>
     qpat_assum `u.t_mem SUBSET tn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> SET_TAC []) >>
  drule_all calldata_scratch_array_loop_complete_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _` kall_tac >>
  suspend "composition"
QED

Resume calldata_scratch_array_constructor_ptr[composition]:
  `abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`loop_st.cs_next_id`,`start.cs_next_id`,`start.cs_next_var`,
       `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap actual t` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`,`hi`,`lo`,`loop_st.cs_next_var`,
       `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     fs[abi_scratch_decoder_loop_inv_def]) >>
  `abi_scratch_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     conj_tac >- decide_tac >> qexists_tac `actual` >> simp[]) >>
  `abi_decode_sim ctx func initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `jump_to (FST labels) actual` >> simp[]) >>
  qexistsl_tac [`t`,`H'`,`u'`] >> asm_simp_tac bool_ss [] >>
  suspend "frames"
QED

Resume calldata_scratch_array_constructor_ptr[frames]:
  `final.cs_current_bb = SND (SND labels) /\ final.cs_current_insts = []` by
    (qhdtm_assum `abi_decoder_recursive_loop_compiled` mp_tac >>
     qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_recursive_loop_compiled_def] >> rpt strip_tac >>
     gvs[abi_decode_loop_suffix_shape, abi_decode_loop_suffix_state_def]) >>
  `t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    fs[abi_scratch_decoder_loop_inv_def] >>
  asm_simp_tac bool_ss [LENGTH] >>
  conj_tac
  >- (qpat_assum `u'.t_mem SUBSET u.t_mem` mp_tac >>
      qpat_assum `u.t_mem SUBSET tn.t_mem` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> SET_TAC []) >>
  conj_tac >- suspend "old_variables" >>
  suspend "slot_frame"
QED

Resume calldata_scratch_array_constructor_ptr[old_variables]:
  qpat_assum `!x. not_fresh_at start x ==> _` mp_tac >>
  qpat_assum `!x. abi_decoder_older_vars loop_st.cs_next_var x ==> _` mp_tac >>
  qpat_assum `start.cs_next_var <= loop_st.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[not_fresh_at_def, abi_decoder_older_vars_def, decoder_jump_fields, lookup_var_def] >>
  metis_tac[LESS_TRANS, LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Resume calldata_scratch_array_constructor_ptr[slot_frame]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_scratch_effect _ _ start.cs_next_id final.cs_next_id _ _ _ _ _ _ initial t`
    (mp_then Any mp_tac abi_scratch_effect_slot) >>
  disch_then irule >>
  fs[abiScratchDecoderContractTheory.abi_scratch_decoder_input_def,
     abiScratchDecoderContractTheory.abi_scratch_decoder_ranges_def]
QED

Finalise calldata_scratch_array_constructor_ptr
