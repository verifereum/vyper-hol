Theory stmtSimCustomErrorMemTypedCopy
Ancestors
  stmtSimCustomErrorMemCopyInterface stmtSimCustomErrorMemCopyFields
  stmtSimCustomErrorMemCopyLoop stmtSimCustomErrorMemCopyDynamic
  placeTypedCopyRecursivePath placeStoreStorage typedCopyDomain
  context compileEnv valueEncoding valueEncodingProps vyperTyping
  vyperTypeExprSoundness vyperTypeABI exprSimProps loweringPosts
  words list rich_list finite_map arithmetic typedMemoryCopy vyperValue
  valueEncodingDefs vyperTypeSystem vyperTypeArgFits loweringStateRelDefs
  venomState venomInst venomExecSemantics fragGasMode placeTypedCopyPath

Theorem typed_copy_checked_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_checked_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_checked_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (drule typed_copy_tuple_widening >>
     gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
     metis_tac[place_store_tuple_children_widen]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `typed_copy_checked_entries cenv ctx dtys stys tvs' tvs l` by
    (irule typed_copy_checked_entries_from_semantics >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- gvs[val_wf_def]) >>
     (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
     qexists_tac `tenv` >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[member_rank_lt_tuple]) >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  irule typed_copy_tuple_checked >> simp[] >>
  (conj_tac >- gvs[val_wf_def]) >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexists_tac `tvs` >> gvs[val_wf_def]
QED

Theorem typed_copy_checked_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_checked_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_checked_entry cenv ctx (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typed_copy_default_widening] >>
  `!i. i < cap ==> typed_copy_checked_entry cenv ctx de se tv' tv
      (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once type_rank_def] >>
     `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule typed_copy_sparse_lookup_wf >> qexists_tac `cap` >> fs[val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[default_value_well_typed, cj 1 evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  gvs[type_memory_size_def] >> irule typed_copy_sarray_checked_path >> simp[] >>
  (conj_tac >- gvs[value_has_type_def]) >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw`, `tenv`] >> gvs[type_memory_size_def, value_has_type_def]
QED

Theorem typed_copy_checked_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_checked_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_checked_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH l ==> typed_copy_checked_entry cenv ctx de se tv' tv (EL i l)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once type_rank_def] >>
     gvs[typed_copy_dynarray_wf, all_have_type_EVERY, EVERY_EL]) >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_dynarray_checked_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`scap`, `tv`, `sw`] >>
  gvs[typed_copy_dynarray_wf] >> strip_tac >> gvs[]
QED

Theorem typed_copy_checked_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_checked_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_checked_entry cenv ctx (StructT name) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >> drule OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[typed_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    metis_tac[place_store_tuple_children_widen] >>
  `typed_copy_checked_entries cenv ctx (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) tvs tvs vs` by
    (irule typed_copy_checked_entries_from_semantics >> simp[] >>
     qexists_tac `tenv` >> gvs[evaluate_types_OPT_MMAP] >>
     (conj_tac >- metis_tac[]) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
     qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
     fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all member_rank_lt_struct >> simp[type_rank_def, nsid_to_string_def]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    suspend "bytes" >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  suspend "run"
QED

Resume typed_copy_checked_struct_entry[bytes]:
  (conj_tac >- metis_tac[]) >>
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  qpat_x_assum `OPT_MMAP _ (MAP (FST o SND) fields) = SOME tvs` mp_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  qpat_x_assum `!ty tv. evaluate_type tenv ty = SOME tv ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qid_spec_tac `tvs` >> Induct_on `fields` >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]
QED

Resume typed_copy_checked_struct_entry[run]:
  markerLib.RESUME_TAC >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `tvs` >>
     Induct_on `args` >> Cases_on `tvs` >> simp[type_memory_size_def]) >>
  gvs[type_memory_size_def, val_in_memory_def, typed_copy_fields_tuple_zip] >>
  irule typed_copy_struct_checked >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexists_tac `sw` >> simp[get_struct_fields_def]
QED

Finalise typed_copy_checked_struct_entry

Theorem typed_copy_checked_rank_entry:
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
    typed_copy_checked_entry cenv ctx dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- (irule typed_copy_checked_word_entry >> simp[] >> qexists_tac `tenv` >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- (irule typed_copy_checked_bytestring_entry >> simp[] >>
      (conj_tac >- metis_tac[typed_copy_bytestring_source]) >>
      qexists_tac `tenv` >> simp[]) >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule typed_copy_checked_sarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >> rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
      irule typed_copy_checked_dynarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >~ [`TupleT dtys`]
  >- (irule typed_copy_checked_tuple_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (irule typed_copy_checked_struct_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  simp[typed_copy_checked_entry_def] >> rpt strip_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  qexists_tac `s` >> simp[val_in_memory_def, type_memory_size_def,
    typed_copy_state_frame_refl, gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules]
QED

Theorem compile_store_memory_typed_forward_run_mem:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_checked_entry cenv ctx dty sty dtv stv v` by
    (irule typed_copy_checked_rank_entry >> simp[] >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  irule typed_copy_checked_entry_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`] >> simp[]
QED
