(* Rank-indexed typed normalization with one counted safe endpoint. *)
Theory typedNormalizeRankPathMem
Ancestors
  typedNormalizeRankMem typedFieldCopyAggregateMem typedArrayCopyPathsMem
  typedSarrayCopyPathsMem
  typedNormalizeFrame stmtSimReturn typedMemoryCopy valueCopyBytes exprSimBufferStore
  allocaFootprint venomInst typedNormalizeFastRepresentation loweringPosts
  typedFieldCopyPathsMem context compileEnv venomState valueEncoding
  vyperTypeSystem vyperValue vyperTyping vyperTypeArgFits
  list rich_list arithmetic words valueCopy exprLoweringProps
  exprSimDefs exprSimProps venomExecSemantics valueEncodingProps fragGasPathMem

Theorem typed_store_rank_path_mem:
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
  ?ngas t. gas_path_mem ctx fn s ngas (OK t) /\ ~t.vs_halted /\
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
  >- suspend "word" >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  Cases_on `dty`
  >~ [`ArrayT elem bound`] >- suspend "array"
  >~ [`TupleT tys`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct"
  >~ [`NoneT`] >- suspend "empty" >>
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()]
QED
Resume typed_store_rank_path_mem[word]:
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `sty = dty` by metis_tac[typedMemoryCopyTheory.typed_copy_word_widening] >> gvs[] >>
  `type_memory_size dtv = 32` by metis_tac[word_type_sizes] >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_word_straight >> strip_tac >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (fs[] >> decide_tac) >>
  drule_all normalize_word_window_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ _ _ _`)) >>
  gvs[venom_state_component_equality, lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume typed_store_rank_path_mem[empty]:
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
    comp_return_def, evaluate_type_def, value_has_type_def] >>
  qexistsl_tac [`0`, `s`] >> simp[cj 1 gas_path_mem_rules,
    val_in_memory_def, venom_state_component_equality]
QED
Resume typed_store_rank_path_mem[bytes]:
  qpat_x_assum `!m. m < n ==> _` kall_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_store_size stv v <= type_memory_size stv /\
   val_store_size dtv v <= type_memory_size dtv /\
   val_footprint dtv v <= val_store_size dtv v` by
    metis_tac[val_store_size_le, val_footprint_le_store_size] >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `32 + 32 * word_size len < dimword(:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   val_footprint dtv v <= 32 + 32 * word_size len` by decide_tac >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[typedCopyAgreementTheory.compile_store_memory_typed_bytes] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule buffer_store_bytestring_shape >> simp[same_blocks_def]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_bytestring_window_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ _ _ _`)) >>
  gvs[venom_state_component_equality, lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume typed_store_rank_path_mem[array]:
  drule typed_copy_array_source >> strip_tac >>
  qpat_x_assum `sty = _` SUBST_ALL_TAC >>
  drule typed_copy_array_widening >> disch_then (assume_tac o CONJUNCT2) >>
  Cases_on `bound`
  >~ [`Fixed cap`] >- suspend "fixed_array" >>
  suspend "dynamic_array"
QED
Resume typed_store_rank_path_mem[fixed_array]:
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
Resume typed_store_rank_path_mem[fixed_bulk]:
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
  >- (`F` suffices_by simp[] >>
      qpat_x_assum `cap * type_memory_size tv' = 0` mp_tac >>
      qpat_x_assum `0 < cap` mp_tac >>
      qpat_x_assum `0 < type_slot_size tv'` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[type_memory_size_slots]) >>
  Cases_on `cap * type_memory_size tv'` >- fs[] >>
  qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac[compile_copy_memory_def] >> strip_tac >>
  drule emit_mcopy_run >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mcopy_mem_ok >>
     disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
     disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
     disch_then irule >> simp[eval_operand_def] >> metis_tac[]) >>
  suspend "fixed_bulk_finish"
QED
Resume typed_store_rank_path_mem[fixed_bulk_finish]:
  `sb.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    fs[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all typed_copy_window_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ _ _ _`)) >>
  `typed_copy_state_frame sa (w2n dw)
    (type_memory_size (ArrayTV tv' (Fixed cap))) s
    ((mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[typed_copy_mcopy_state_frame] >>
  `val_in_memory (ArrayTV tv' (Fixed cap)) v (w2n dw)
    (mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[] >> metis_tac[val_footprint_le]) >>
  `~(mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_halted /\
   (mcopy (w2n dw) (w2n sw) (type_memory_size (ArrayTV tv' (Fixed cap))) s).vs_current_bb = s.vs_current_bb` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def, same_blocks_def] >>
  metis_tac[ADD_COMM]
QED
Resume typed_store_rank_path_mem[fixed_slow]:
  cheat
QED
Resume typed_store_rank_path_mem[dynamic_array]:
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
  suspend "dynamic_slow"
QED
Resume typed_store_rank_path_mem[dynamic_equal]:
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
  `w2n (sw+32w) = w2n sw+32 /\ w2n (dw+32w) = w2n dw+32 /\
   LENGTH l * type_memory_bytes ce elem < dimword(:256) /\
   w2n sw+32 <= s.vs_alloca_next /\ w2n dw+32 <= s.vs_alloca_next /\
   w2n (sw+32w)+LENGTH l*type_memory_bytes ce elem <= s.vs_alloca_next /\
   w2n (dw+32w)+LENGTH l*type_memory_bytes ce elem <= s.vs_alloca_next` by
    (`w2n sw+32 < dimword(:256) /\ w2n dw+32 < dimword(:256) /\
        LENGTH l * type_memory_bytes ce elem < dimword(:256) /\
        w2n sw+32+LENGTH l*type_memory_bytes ce elem <= s.vs_alloca_next /\
        w2n dw+32+LENGTH l*type_memory_bytes ce elem <= s.vs_alloca_next`
       suffices_by (strip_tac >> simp[w2n_add_2] >> gvs[]) >>
     gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all typedNormalizeDynarrayTheory.typed_dynarray_equal_compiler_run >> strip_tac >>
  drule typedNormalizeDynarrayTheory.typed_dynarray_equal_shape >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all typed_copy_window_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  suspend "dynamic_equal_finish"
QED
Resume typed_store_rank_path_mem[dynamic_equal_finish]:
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_in_memory (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l))
    (w2n sw) s.vs_memory /\
   val_wf (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l))` by
    (conj_tac >- metis_tac[dynarray_in_memory_capacity_irrelevant] >>
     fs[typed_copy_dynarray_wf]) >>
  `val_in_memory (ArrayTV tv (Dynamic (LENGTH l))) (ArrayV (DynArrayV l))
    (w2n dw) u.vs_memory` by
    (irule valueCopyTheory.val_in_memory_relocate >> conj_tac >- simp[] >>
     qexistsl_tac [`w2n sw`, `32+LENGTH l*type_memory_size tv`, `s.vs_memory`] >>
     simp[val_footprint_def, type_memory_size_def] >>
     pure_rewrite_tac[Q.SPECL [`LENGTH l*type_memory_size tv`, `32`] ADD_COMM] >>
     irule typedNormalizeDynarrayTheory.typed_dynarray_equal_window >> simp[] >>
     qexists_tac `type_memory_size (ArrayTV tv (Dynamic n''))` >>
     simp[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >>
     gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ _ _ _`)) >> simp[] >>
  conj_tac >- metis_tac[dynarray_in_memory_capacity_irrelevant] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `gas_path_mem _ _ _ _ _` kall_tac >>
      qpat_x_assum `emitted_insts sa sb = _` kall_tac >>
      asm_rewrite_tac[] >> irule typedNormalizeDynarrayTheory.typed_dynarray_equal_exterior >>
      gns[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` kall_tac >>
  qpat_x_assum `emitted_insts sa sb = _` kall_tac >>
  conj_tac
  >- (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED
Resume typed_store_rank_path_mem[dynamic_slow]:
  cheat
QED
Resume typed_store_rank_path_mem[tuple]:
  cheat
QED
Resume typed_store_rank_path_mem[struct]:
  cheat
QED
Finalise typed_store_rank_path_mem
