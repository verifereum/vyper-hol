Theory typedCopyRankMemory
Ancestors
  typedCopyStructMemory typedCopyTupleMemory typedCopySarrayMemory typedCopyDynarrayMemory
  abiValueEncoding valueCopyBytes typedCopyPrimitiveMemory typedMemoryCopy
  compileEnv context exprLowering emitHelper valueEncoding loweringPosts
  vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping words list finite_map arithmetic

Theorem typed_copy_rank_entry_mem[local]:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
      frag_exec_mem ctx sa sb (\u. u = s)
        (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
             typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  Cases_on `is_bytestring_type dty` >- suspend "bytes" >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db` >- suspend "fixed" >> suspend "dynamic")
  >~ [`TupleT dtys`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct" >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  rpt strip_tac >> qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  irule typed_copy_empty_frag_mem >> simp[val_in_memory_def]
QED

Resume typed_copy_rank_entry_mem[word]:
  drule_all typed_copy_word_widening >> strip_tac >> gvs[] >> rpt strip_tac >>
  `type_memory_size dtv = 32` by metis_tac[abi_word_type_size] >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[exprSimPropsTheory.val_in_memory_word] >>
  irule typed_copy_word_frag_mem >> simp[ADD_COMM] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`sw`, `tenv`] >> simp[]
QED

Resume typed_copy_rank_entry_mem[bytes]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  drule_all typed_copy_bytestring_source >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. stv = BaseTV (StringT cap))` by metis_tac[bytestring_type_value] >>
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[bytestring_type_value] >>
  gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
  (irule typed_copy_bytestring_frag_exact_mem >>
   (conj_tac >- first_assum ACCEPT_TAC) >>
   goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
   FIRST [rename1 `StringV str` >> qexistsl_tac [`STRLEN str`, `sw`],
          rename1 `BytesV bs` >> qexistsl_tac [`LENGTH bs`, `sw`]] >>
   gvs[val_in_memory_def, val_footprint_def, type_memory_size_def] >>
   qmatch_goalsub_abbrev_tac `word_size len <= word_size capacity` >>
   `word_size len <= word_size capacity` by
     (irule exprSimHypsTheory.word_size_monotone >> simp[Abbr `len`]) >>
   `word_size len <= word_size cap` by
     (irule exprSimHypsTheory.word_size_monotone >> simp[]) >>
   qspec_then `len` assume_tac exprSimPropsTheory.le_word_size_mul >> decide_tac)
QED

Resume typed_copy_rank_entry_mem[fixed]:
  ho_match_mp_tac typed_copy_sarray_entry_mem >> simp[] >> qexists_tac `tenv` >> simp[] >>
  (conj_tac >- metis_tac[]) >> ntac 5 gen_tac >> ntac 2 strip_tac >>
  qpat_x_assum `!k. k < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]
QED

Resume typed_copy_rank_entry_mem[dynamic]:
  ho_match_mp_tac typed_copy_dynarray_entry_mem >> simp[] >> qexists_tac `tenv` >> simp[] >>
  (conj_tac >- metis_tac[]) >> ntac 5 gen_tac >> ntac 2 strip_tac >>
  qpat_x_assum `!k. k < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]
QED

Resume typed_copy_rank_entry_mem[tuple]:
  ho_match_mp_tac typed_copy_tuple_entry_mem >> simp[] >> qexists_tac `tenv` >> simp[] >>
  (conj_tac >- metis_tac[]) >> ntac 5 gen_tac >> ntac 2 strip_tac >>
  qpat_x_assum `!k. k < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]
QED

Resume typed_copy_rank_entry_mem[struct]:
  ho_match_mp_tac typed_copy_struct_entry_mem >> simp[] >> qexists_tac `tenv` >> simp[] >>
  (conj_tac >- metis_tac[]) >> ntac 5 gen_tac >> ntac 2 strip_tac >>
  qpat_x_assum `!k. k < _ ==> _`
    (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
  simp[] >> disch_then ho_match_mp_tac >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]
QED

Finalise typed_copy_rank_entry_mem

Theorem compile_store_memory_typed_frag_mem:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
           typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  irule typed_copy_rank_entry_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`, `tenv`] >> simp[] >> metis_tac[]
QED
