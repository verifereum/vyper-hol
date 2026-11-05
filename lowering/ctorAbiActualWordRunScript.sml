Theory ctorAbiActualWordRun
Ancestors
  ctorAbiActualScalar ctorAbiActualWorld ctorAbiActualReentry
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarExtend
  abiDecoderClampedWord abiDecoderContract abiDecoderLoop
  abiEncoderProps abiEncoderRegisteredEffect abiEncoder compileEnv exprLoweringProps
  allocaFrontierBound allocaBudgetProps venomMemDefs
  fragExec instIdxIndep venomExecSemantics venomState venomInst
  abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract
  valueEncoding words list rich_list arithmetic finite_map

Theorem ctor_actual_word_ceiling_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next
Proof
  strip_tac >>
  qabbrev_tac `pruned = abi_decoder_prune_vars st.cs_next_var initial` >>
  `eval_operand src pruned = SOME (n2w sb) /\ eval_operand dst pruned = SOME (n2w d) /\
   fresh_vars_wrt st pruned /\
   mem_bytes_at sb 32 pruned.vs_data_section = enc (vyper_to_abi_type env ty) av` by
    simp[Abbr `pruned`, abi_decoder_prune_eval, abi_decoder_prune_fresh, abi_decoder_prune_vars_def] >>
  drule_all (Q.INST [`s` |-> `pruned:venom_state`] ctor_actual_word_sequence) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') pruned = OK clean` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  qunabbrev_tac `pruned` >>
  drule_all ctor_actual_reentry_sequence >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  qexists `actual` >> gvs[abi_decoder_prune_vars_def]
QED

Theorem ctor_actual_word_fragment:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      abi_encoder_registered_effect (frag_ids st st') [(d,32)] initial t /\
      (alloca_inv t <=> alloca_inv initial) /\
      (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial)) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `frag_ids st st'`, `func`, `ctx`] assume_tac) >>
  qexists `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
    abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
    remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem ctor_actual_word_run:
  !dst src hi ce env sf ty tv root_di av v st st' limit_st clamp ctx func site initial sb d.
    compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
    type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
    abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
    eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
      initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
    (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
      sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
    (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
    st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
    unit_alloca_budget ctx < dimword (:256) /\
    d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\ FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (d,type_memory_bytes ce ty) (b,sz)) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual. val_in_memory tv v d actual.vs_memory /\
      abi_encoder_registered_effect (frag_ids st st') [(d,type_memory_bytes ce ty)] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
      actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
      fresh_vars_wrt limit_st actual /\ actual.vs_allocas = initial.vs_allocas /\
      actual.vs_alloca_next = initial.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> asm_rewrite_tac[]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
   mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by
    metis_tac[] >>
  drule_all ctor_actual_word_fragment >>
  disch_then (qspecl_then [`site`, `func`, `ctx`] assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def]
QED
