(* Destination-rank integration of same-endpoint typed memory continuations. *)
Theory typedNormalizeRankMem
Ancestors
  typedNormalizeRecursiveMem typedNormalizeStructEntryMem
  typedMemoryCopy typedCopyMetadata typedNormalizeSemanticMem
  context compileEnv venomState memContinuation valueEncoding
  vyperTypeSystem vyperValue vyperTyping vyperTypeArgFits
  list rich_list arithmetic words valueCopy allocaFootprint typedBytesArrayMem
  fragExecMem exprLoweringProps exprSimDefs exprSimProps loweringPosts venomExecSemantics storageDecodeMemory valueEncodingProps
  typedNormalizeDynarray typedNormalizeFastRepresentation

Theorem typed_store_rank_mem_cont:
  !n ce tenv dty sty dtv stv v dst src sa sb ctx fn s dw sw.
  type_rank ce.ce_struct_fields dty = n /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  completeInduct_on `n` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dty`
  >- (qpat_x_assum `!m. m < n ==> _` kall_tac >>
      `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      drule_all typed_store_word_mem_cont >> metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (qpat_x_assum `!m. m < n ==> _` kall_tac >>
      `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      drule_all typed_store_bytestring_mem_cont >> metis_tac[]) >>
  Cases_on `dty`
  >~ [`ArrayT elem bound`] >- suspend "array"
  >~ [`TupleT tys`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct"
  >~ [`NoneT`] >- (qpat_x_assum `!m. m < n ==> _` kall_tac >>
      irule typed_store_empty_mem_cont >>
      simp[] >> qexistsl_tac [`ce`, `dst`, `src`, `stv`, `sty`, `tenv`] >>
      fs[evaluate_type_def]) >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()]
QED
Resume typed_store_rank_mem_cont[struct]:
  `!ty tv cv sd se dp sp u dw sw.
    type_rank ce.ce_struct_fields ty < type_rank ce.ce_struct_fields (StructT name) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv cv /\ val_wf tv cv /\
    compile_store_memory_typed ce dp ty sp ty sd = ((),se) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    w2n dw + type_memory_size tv <= u.vs_alloca_next /\
    w2n sw + type_memory_size tv <= u.vs_alloca_next /\
    w2n dw + type_memory_size tv < dimword(:256) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    (w2n sw + type_memory_size tv <= w2n dw \/
      w2n dw + type_memory_size tv <= w2n sw) /\
    val_in_memory tv cv (w2n sw) u.vs_memory ==>
    ?t. mem_cont_sim ctx fn u t /\ ~t.vs_halted /\
      t.vs_current_bb = se.cs_current_bb /\
      t.vs_inst_idx = LENGTH se.cs_current_insts /\
      val_in_memory tv cv (w2n dw) t.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size tv <= p ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sd.cs_current_bb; vs_inst_idx := LENGTH sd.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sd x ==> lookup_var x t = lookup_var x u)` by
    suspend "struct_child" >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  drule_all typed_store_struct_mem_cont >> strip_tac >>
  qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
  qexists_tac `t` >> fs[GSYM ADD_ASSOC] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[struct_child]:
  qpat_x_assum `!m. m < n ==> _` mp_tac >>
  qpat_x_assum `type_rank _ (StructT _) = n` mp_tac >>
  qpat_x_assum `acyclic_struct_metadata _` mp_tac >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 5 disch_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_rank ce.ce_struct_fields ty < n` by metis_tac[] >>
  qpat_x_assum `!m. m < n ==> _`
    (drule_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`))) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  `type_widens_to tenv ty ty` by simp[] >>
  disch_then (qspecl_then [`tv`, `ctx`, `fn`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED
Resume typed_store_rank_mem_cont[array]:
  drule typed_copy_array_source >> strip_tac >>
  qpat_x_assum `sty = _` SUBST_ALL_TAC >>
  drule typed_copy_array_widening >> disch_then (assume_tac o CONJUNCT2) >>
  Cases_on `bound`
  >~ [`Fixed cap`] >- suspend "fixed_array"
  >> suspend "dynamic_array"
QED
Resume typed_store_rank_mem_cont[fixed_array]:
  qpat_x_assum `(?n m. _) \/ _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `sb' = _` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type tenv (ArrayT se _) = SOME stv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `evaluate_type tenv (ArrayT elem _) = SOME dtv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `ArrayTV _ _ = stv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ArrayTV _ _ = dtv` (SUBST_ALL_TAC o SYM) >>
  `type_widens_to tenv se elem` by
    (qpat_x_assum `type_widens_to _ (ArrayT _ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
       evaluate_type_def] >>
     Cases_on `evaluate_type tenv elem` >> simp[] >> metis_tac[]) >>
  `cap < dimword(:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' _) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> simp[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes ce se = type_memory_size tv /\
   type_memory_bytes ce elem = type_memory_size tv'` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (mp_tac o SRULE [Once compile_store_memory_typed_def,
      is_word_type_def, is_bytestring_type_def]) >> simp[] >> strip_tac >>
  Cases_on `type_memory_bytes ce elem = type_memory_bytes ce se /\
    ~is_abi_dynamic ce.ce_struct_fields elem`
  >- suspend "fixed_bulk" >>
  suspend "fixed_slow"
QED
Resume typed_store_rank_mem_cont[fixed_slow]:
  `emitted_blocks sa sb <> []` by
    (irule typedNormalizeLoopTheory.typed_sarray_emits_blocks >>
     reverse conj_tac >- (goal_assum drule >> simp[]) >>
     goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `emitted_blocks sa sb <> [] ==> _` (drule_then strip_assume_tac) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `eval_operand src s = SOME (n2w (w2n sw)) /\
   eval_operand dst s = SOME (n2w (w2n dw))` by simp[] >>
  drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)
    normalize_sarray_semantic_cont >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  impl_tac >- suspend "fixed_slow_premises" >>
  strip_tac >> qexists_tac `t` >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  fs[] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[fixed_slow_premises]:
  simp[] >>
  conj_tac >- (qpat_x_assum `~(_ /\ ~is_abi_dynamic _ _)` mp_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!m. m < n ==> _` mp_tac >>
  qpat_x_assum `type_rank _ (ArrayT _ _) = n` mp_tac >>
  qpat_x_assum `acyclic_struct_metadata _` mp_tac >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` mp_tac >>
  qpat_x_assum `evaluate_type tenv se = SOME tv` mp_tac >>
  qpat_x_assum `evaluate_type tenv elem = SOME tv'` mp_tac >>
  qpat_x_assum `type_widens_to tenv se elem` mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 8 disch_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_rank ce.ce_struct_fields elem < n` by
    (qpat_x_assum `type_rank _ (ArrayT _ _) = n` mp_tac >>
     simp[Once typedCopyDomainTheory.type_rank_def]) >>
  qpat_x_assum `!m. m < n ==> _`
    (drule_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`))) >>
  disch_then (drule_at (Pat `evaluate_type _ se = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ elem = _`)) >>
  disch_then (drule_at (Pat `value_has_type tv _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
  impl_tac >- suspend "fixed_child_facts" >> simp[]
QED
Resume typed_store_rank_mem_cont[fixed_child_facts]:
  simp[] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[fixed_bulk]:
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `tv = tv'` by
    (irule (typed_copy_static_widening |> INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``]) >>
     qexistsl_tac [`elem`, `ce.ce_struct_fields`, `se`, `tenv`] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `tv = tv'` SUBST_ALL_TAC >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  `cap * type_memory_size tv' = type_memory_size (ArrayTV tv' (Fixed cap))` by
    simp[type_memory_size_def, type_slot_size_def] >>
  `cap * type_memory_size tv' < dimword(:256)` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `w2n dw + type_memory_size _ < _` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  Cases_on `cap * type_memory_size tv' = 0`
  >- suspend "fixed_bulk_zero" >>
  Cases_on `cap * type_memory_size tv'` >- fs[] >>
  qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac[compile_copy_memory_def] >> strip_tac >>
  drule emit_mcopy_run >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mcopy_mem_ok >>
     disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
     disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
     disch_then irule >> simp[eval_operand_def] >> metis_tac[]) >>
  suspend "fixed_bulk_finish"
QED
Resume typed_store_rank_mem_cont[fixed_bulk_finish]:
  qexists_tac `(mcopy (w2n dw) (w2n sw)
    (type_memory_size (ArrayTV tv' (Fixed cap))) s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >>
      fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `typed_copy_state_frame sa (w2n dw)
    (type_memory_size (ArrayTV tv' (Fixed cap))) s
    ((mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[typed_copy_mcopy_state_frame] >>
  `val_in_memory (ArrayTV tv' (Fixed cap)) v (w2n dw)
    (mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[] >>
     metis_tac[val_footprint_le]) >>
  `~(mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_halted /\
   (mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_current_bb = s.vs_current_bb` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def, same_blocks_def] >>
  metis_tac[ADD_COMM]
QED
Resume typed_store_rank_mem_cont[fixed_bulk_zero]:
  `F` suffices_by simp[] >>
  qpat_x_assum `cap * type_memory_size tv' = 0` mp_tac >>
  qpat_x_assum `0 < cap` mp_tac >>
  qpat_x_assum `0 < type_slot_size tv'` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[type_memory_size_slots]
QED
Resume typed_store_rank_mem_cont[dynamic_array]:
  qpat_x_assum `(?n m. _) \/ _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `sb' = _` SUBST_ALL_TAC >>
  rename1 `ArrayT elem (Dynamic cap)` >>
  qpat_x_assum `evaluate_type tenv (ArrayT se _) = SOME stv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `evaluate_type tenv (ArrayT elem _) = SOME dtv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `ArrayTV _ _ = stv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ArrayTV _ _ = dtv` (SUBST_ALL_TAC o SYM) >>
  `type_widens_to tenv se elem` by
    (qpat_x_assum `type_widens_to _ (ArrayT _ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
       evaluate_type_def] >>
     Cases_on `evaluate_type tenv elem` >> simp[] >> metis_tac[]) >>
  `cap < dimword(:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' _) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> simp[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes ce se = type_memory_size tv /\
   type_memory_bytes ce elem = type_memory_size tv'` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (mp_tac o SRULE [Once compile_store_memory_typed_def,
      is_word_type_def, is_bytestring_type_def]) >> simp[] >> strip_tac >>
  Cases_on `type_memory_bytes ce elem = type_memory_bytes ce se /\ elem = se`
  >- suspend "dynamic_equal" >>
  qpat_x_assum `value_has_type (ArrayTV tv (Dynamic _)) v` mp_tac >>
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def] >> strip_tac >>
  suspend "dynamic_slow"
QED
Resume typed_store_rank_mem_cont[dynamic_slow]:
  `emitted_blocks sa sb <> []` by
    (irule typedNormalizeDynarrayLoopTheory.typed_dynarray_emits_blocks >>
     reverse conj_tac >- (goal_assum drule >> simp[]) >>
     goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `emitted_blocks sa sb <> [] ==> _` (drule_then strip_assume_tac) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `eval_operand src s = SOME (n2w (w2n sw)) /\
   eval_operand dst s = SOME (n2w (w2n dw))` by simp[] >>
  drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)
    normalize_dynarray_semantic_cont >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspecl_then [`tv'`, `ctx`] mp_tac) >>
  impl_tac >- suspend "dynamic_slow_premises" >>
  strip_tac >> qexists_tac `t` >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  fs[] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[dynamic_slow_premises]:
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[value_has_type_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `!m. m < n ==> _` mp_tac >>
  qpat_x_assum `type_rank _ (ArrayT _ _) = n` mp_tac >>
  qpat_x_assum `acyclic_struct_metadata _` mp_tac >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` mp_tac >>
  qpat_x_assum `evaluate_type tenv se = SOME tv` mp_tac >>
  qpat_x_assum `evaluate_type tenv elem = SOME tv'` mp_tac >>
  qpat_x_assum `type_widens_to tenv se elem` mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 8 disch_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_rank ce.ce_struct_fields elem < n` by
    (qpat_x_assum `type_rank _ (ArrayT _ _) = n` mp_tac >>
     simp[Once typedCopyDomainTheory.type_rank_def]) >>
  qpat_x_assum `!m. m < n ==> _`
    (drule_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`))) >>
  disch_then (drule_at (Pat `evaluate_type _ se = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ elem = _`)) >>
  disch_then (drule_at (Pat `value_has_type tv _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
  impl_tac >- suspend "dynamic_child_facts" >> simp[]
QED
Resume typed_store_rank_mem_cont[dynamic_child_facts]:
  simp[] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[dynamic_equal]:
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `elem = se` by metis_tac[] >> gnvs[] >>
  qpat_x_assum `value_has_type (ArrayTV tv (Dynamic _)) v` mp_tac >>
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def] >> strip_tac >>
  `LENGTH l <= cap /\ LENGTH l <= n''` by
    fs[value_has_type_def, typed_copy_dynarray_wf] >>
  `LENGTH l * type_memory_size tv <= n'' * type_memory_size tv /\
   LENGTH l * type_memory_size tv <= cap * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  `mload (w2n sw) s = n2w (LENGTH l)` by
    fs[val_in_memory_def, GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `val_in_memory (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l))
     (w2n sw) s.vs_memory` by
    metis_tac[dynarray_in_memory_capacity_irrelevant] >>
  drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)
    normalize_dynarray_equal_window_cont >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspecl_then [`type_memory_size (ArrayTV tv (Dynamic n''))`, `LENGTH l`, `fn`, `ctx`] mp_tac) >>
  impl_tac >- suspend "dynamic_equal_premises" >>
  strip_tac >> suspend "dynamic_equal_finish"
QED
Resume typed_store_rank_mem_cont[dynamic_equal_premises]:
  `val_wf (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l))` by
    fs[typed_copy_dynarray_wf] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  suspend "equal_numeric"
QED
Resume typed_store_rank_mem_cont[equal_numeric]:
  simp[val_footprint_def, type_memory_size_def] >>
  rpt (qpat_x_assum `val_in_memory _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `val_wf _ _` kall_tac) >>
  rpt (qpat_x_assum `value_has_type _ _` kall_tac) >>
  rpt (qpat_x_assum `!name fields. _` kall_tac) >>
  gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >>
  `0 < type_memory_size tv` by simp[type_memory_size_slots] >>
  `0 < n'' * type_memory_size tv /\ 0 < cap * type_memory_size tv` by simp[] >>
  decide_tac
QED
Resume typed_store_rank_mem_cont[dynamic_equal_finish]:
  markerLib.RESUME_TAC >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[typed_dynarray_equal_shape] >>
  simp[] >>
  conj_tac >- metis_tac[dynarray_in_memory_capacity_irrelevant] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      simp[Excl "LE_MULT_RCANCEL"] >>
      qpat_x_assum `type_memory_size (ArrayTV tv (Dynamic cap)) + w2n dw <= _` mp_tac >>
      simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
      qpat_x_assum `s.vs_current_bb = sa.cs_current_bb` mp_tac >>
      qpat_x_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  fs[lookup_var_def]
QED
Resume typed_store_rank_mem_cont[tuple]:
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >>
  qpat_x_assum `sty = TupleT stys` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type tenv (TupleT stys) = SOME stv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >> strip_tac >>
  qpat_x_assum `evaluate_type tenv (TupleT tys) = SOME dtv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >> strip_tac >>
  qpat_x_assum `TupleTV _ = stv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `TupleTV _ = dtv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `v` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gnvs[value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys tys` by
    (irule typed_copy_tuple_children_widen >>
     conj_tac >- metis_tac[] >>
     drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  suspend "tuple_metadata"
QED
Resume typed_store_rank_mem_cont[tuple_metadata]:
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) stys tvs /\
   LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs'` by
    (conj_tac >> irule vyperTypeABITheory.OPT_MMAP_LIST_REL >> simp[]) >>
  `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) stys tvs /\
   LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs'` by
    (qpat_x_assum `!m. m < n ==> _` kall_tac >>
     conj_tac >> fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `LENGTH tys = LENGTH tvs' /\ LENGTH stys = LENGTH tvs /\
   LENGTH tys = LENGTH stys /\ LENGTH l = LENGTH tys /\
   EVERY2 val_wf tvs l /\ EVERY2 val_wf tvs' l` by
    (qpat_x_assum `!m. m < n ==> _` kall_tac >>
     fs[LIST_REL_EL_EQN, val_wf_def,
       abiTupleValueEncodingTheory.abi_values_have_types] >>
     metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def] >> strip_tac >>
  suspend "tuple_adapter"
QED
Resume typed_store_rank_mem_cont[tuple_adapter]:
  pure_rewrite_tac[val_in_memory_def, type_value_case_def, type_memory_size_def] >>
  BETA_TAC >>
  qpat_assum `val_in_memory (TupleTV _) _ _ _`
    (assume_tac o SRULE [val_in_memory_def]) >>
  mp_tac (Q.INST [`DT` |-> `tys`, `ST` |-> `stys`,
    `dtvs` |-> `tvs'`, `stvs` |-> `tvs`, `vs` |-> `l`,
    `a` |-> `w2n (sw : 256 word)`, `b` |-> `w2n (dw : 256 word)`,
    `d` |-> `\i. w2n (dw : 256 word) + SUM (MAP (type_memory_bytes ce) (TAKE i tys))`,
    `h` |-> `\i. w2n (sw : 256 word) + SUM (MAP (type_memory_bytes ce) (TAKE i stys))`]
    typedNormalizeTupleSemanticMemTheory.normalize_tuple_semantic_cont) >>
  (impl_tac >- suspend "tuple_premises") >>
  strip_tac >> qexists_tac `t` >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  fs[] >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[tuple_premises]:
  `SUM (MAP (type_memory_bytes ce) tys) = type_memory_size_list tvs' /\
   SUM (MAP (type_memory_bytes ce) stys) = type_memory_size_list tvs` by
    (conj_tac
     >- (qpat_assum `LIST_REL (\ty tv. type_memory_bytes ce ty = _) tys tvs'`
           (mp_then Any (qspec_then `LENGTH tys` mp_tac) tupleTypedLoadTheory.tuple_prefix_sizes) >>
         simp[valueEncodingProofsTheory.type_memory_size_list_sum, TAKE_LENGTH_TOO_LONG]) >>
     qpat_assum `LIST_REL (\ty tv. type_memory_bytes ce ty = _) stys tvs`
       (mp_then Any (qspec_then `LENGTH stys` mp_tac) tupleTypedLoadTheory.tuple_prefix_sizes) >>
     simp[valueEncodingProofsTheory.type_memory_size_list_sum, TAKE_LENGTH_TOO_LONG]) >>
  simp[TAKE_LENGTH_TOO_LONG] >>
  ntac 5 (conj_tac >- (qpat_x_assum `!m. m < n ==> _` kall_tac >>
    fs[type_memory_size_def] >> metis_tac[])) >>
  conj_tac >- suspend "tuple_children" >> metis_tac[]
QED
Resume typed_store_rank_mem_cont[tuple_children]:
  qpat_x_assum `!m. m < n ==> _` mp_tac >>
  qpat_x_assum `acyclic_struct_metadata _` mp_tac >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  qpat_x_assum `!name fields. FLOOKUP _ name = SOME fields ==> _` mp_tac >>
  qpat_x_assum `LIST_REL (type_widens_to tenv) _ _` mp_tac >>
  rpt (qpat_x_assum `LIST_REL _ _ _` mp_tac) >>
  rpt (qpat_x_assum `values_have_types _ _` mp_tac) >>
  qpat_x_assum `LENGTH tys = LENGTH stys` mp_tac >>
  qpat_x_assum `LENGTH stys = LENGTH tvs` mp_tac >>
  qpat_x_assum `LENGTH tys = LENGTH tvs'` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type tenv (EL i stys) = SOME (EL i tvs) /\
   evaluate_type tenv (EL i tys) = SOME (EL i tvs') /\
   type_widens_to tenv (EL i stys) (EL i tys) /\
   value_has_type (EL i tvs) (EL i l) /\ value_has_type (EL i tvs') (EL i l) /\
   val_wf (EL i tvs) (EL i l) /\ val_wf (EL i tvs') (EL i l) /\
   type_memory_bytes ce (EL i tys) = type_memory_size (EL i tvs') /\
   type_memory_bytes ce (EL i stys) = type_memory_size (EL i tvs)` by
    (qpat_x_assum `!m. m < n ==> _` kall_tac >>
     fs[LIST_REL_EL_EQN, abiTupleValueEncodingTheory.abi_values_have_types]) >>
  `type_rank ce.ce_struct_fields (EL i tys) < type_rank ce.ce_struct_fields (TupleT tys)` by
    (irule typedCopyDomainTheory.member_rank_lt_tuple >> simp[EL_MEM] >> metis_tac[]) >>
  suspend "tuple_child_apply"
QED
Resume typed_store_rank_mem_cont[tuple_child_apply]:
  `SUM (MAP (type_memory_bytes ce) (TAKE (SUC i) tys)) =
     SUM (MAP (type_memory_bytes ce) (TAKE i tys)) + type_memory_size (EL i tvs') /\
   SUM (MAP (type_memory_bytes ce) (TAKE (SUC i) stys)) =
     SUM (MAP (type_memory_bytes ce) (TAKE i stys)) + type_memory_size (EL i tvs)` by
    (qpat_x_assum `!m. m < n ==> _` kall_tac >>
     `i < LENGTH tys /\ i < LENGTH stys` by metis_tac[] >>
     conj_tac
     >- (qpat_assum `i < LENGTH tys`
          (mp_then Any (qspec_then `type_memory_bytes ce` mp_tac)
            typedNormalizeFieldsTheory.normalize_prefix_step) >> simp[]) >>
     qpat_assum `i < LENGTH stys`
       (mp_then Any (qspec_then `type_memory_bytes ce` mp_tac)
         typedNormalizeFieldsTheory.normalize_prefix_step) >> simp[]) >>
  rpt (qhdtm_x_assum `LIST_REL` kall_tac) >>
  rpt (qpat_x_assum `values_have_types _ _` kall_tac) >>
  qabbrev_tac `a = SUM (MAP (type_memory_bytes ce) (TAKE i stys)) + w2n sw` >>
  qabbrev_tac `b = SUM (MAP (type_memory_bytes ce) (TAKE i tys)) + w2n dw` >>
  `a + type_memory_size (EL i tvs) <= u.vs_alloca_next /\
   b + type_memory_size (EL i tvs') <= u.vs_alloca_next /\
   a + type_memory_size (EL i tvs) < dimword(:256) /\
   b + type_memory_size (EL i tvs') < dimword(:256)` by
    (qpat_x_assum `!m. m < n ==> _` kall_tac >>
     simp[Abbr `a`, Abbr `b`] >> decide_tac) >>
  `a < dimword(:256) /\ b < dimword(:256)` by decide_tac >>
  `w2n (n2w a : 256 word) = a /\ w2n (n2w b : 256 word) = b` by simp[] >>
  suspend "tuple_rank_call"
QED
Resume typed_store_rank_mem_cont[tuple_rank_call]:
  qpat_x_assum `!m. m < n ==> _`
    (drule_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`))) >>
  disch_then (drule_at (Pat `evaluate_type _ (EL i stys) = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (EL i tys) = _`)) >>
  disch_then (drule_at (Pat `value_has_type (EL i tvs) _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[ADD_ASSOC, ADD_COMM])) >>
  strip_tac >> qexists_tac `t` >>
  `SUM (MAP (type_memory_bytes ce) (TAKE i tys)) +
     (type_memory_size (EL i tvs') + w2n dw) = b + type_memory_size (EL i tvs')` by
    (simp[Abbr `b`] >> decide_tac) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `val_in_memory _ _ (w2n (n2w b)) _` mp_tac >> simp[]) >>
  qpat_x_assum `!p k. _ ==> mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
  simp[ADD_COMM]
QED
Finalise typed_store_rank_mem_cont
