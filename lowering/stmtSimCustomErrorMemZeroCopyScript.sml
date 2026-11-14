Theory stmtSimCustomErrorMemZeroCopy
Ancestors
  stmtSimCustomErrorMemTypedCopy stmtSimCustomErrorMemZeroFields
  stmtSimCustomErrorMemZeroArray annassignRelayoutPost
  placeTypedCopyRecursivePath placeStoreStorage typedCopyDomain
  context compileEnv valueEncoding valueEncodingProps vyperTyping
  vyperTypeExprSoundness vyperTypeABI exprSimProps loweringPosts
  words list rich_list finite_map arithmetic typedMemoryCopy vyperValue
  valueEncodingDefs vyperTypeSystem vyperTypeArgFits loweringStateRelDefs
  venomState venomInst venomExecSemantics fragGasMode placeTypedCopyPath
  fragGasPathMem

Theorem typed_copy_zero_fields_from_semantics[local]:
  !cenv tenv ctx dtys stys dtvs stvs vs dst src sa sb s dw sw func.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    type_memory_size_list dtvs = 0 /\ type_memory_size_list stvs = 0 /\
    (!dty sty dtv stv v. MEM dty dtys /\
      type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
      evaluate_type tenv dty = SOME dtv /\ value_has_type stv v /\
      value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
      type_memory_size stv = 0 /\ type_memory_size dtv = 0 ==>
      !func dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory /\
        w2n dw < dimword (:256) /\ w2n dw <= s.vs_alloca_next /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        alloca_inv s /\ alloca_history func s /\
        ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
        s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        ?t. gas_marked_path T ctx func s 0 (OK t) /\
            val_in_memory dtv v (w2n dw) t.vs_memory /\
            typed_copy_state_frame sa (w2n dw) 0 s t /\
            ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next) /\
    compile_typed_copy_fields cenv dst src dtys stys 0 0 sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw) s.vs_memory /\
    w2n dw < dimword (:256) /\ w2n dw <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        tuple_in_memory vs dtvs (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 0 s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
   LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs` by
    metis_tac[OPT_MMAP_LENGTH, values_have_types_length] >>
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!tys tvs. OPT_MMAP (evaluate_type tenv) tys = SOME tvs /\
      type_memory_size_list tvs = 0 ==>
      EVERY (\(ty,tv). type_memory_bytes cenv ty = type_memory_size tv /\
                       type_memory_size tv = 0) (ZIP (tys,tvs))` by
    (qpat_x_assum `!ty tv. _` mp_tac >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     Induct >> qx_gen_tac `tvals` >> Cases_on `tvals` >>
     simp[OPT_MMAP_def, AllCaseEqs(), type_memory_size_def] >>
     rpt strip_tac >> gvs[type_memory_size_def] >> metis_tac[]) >>
  suspend "semantics"
QED

Resume typed_copy_zero_fields_from_semantics[semantics]:
  `EVERY (\(dty,sty,dtv,stv,v).
     type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
     evaluate_type tenv dty = SOME dtv /\ value_has_type stv v /\
     value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
     type_memory_size stv = 0 /\ type_memory_size dtv = 0)
     (ZIP (dtys,ZIP (stys,ZIP (dtvs,ZIP (stvs,vs)))))` by
    (qpat_x_assum `LIST_REL _ stys dtys` mp_tac >>
     qpat_x_assum `OPT_MMAP _ dtys = _` mp_tac >>
     qpat_x_assum `OPT_MMAP _ stys = _` mp_tac >>
     qpat_x_assum `values_have_types stvs vs` mp_tac >>
     qpat_x_assum `values_have_types dtvs vs` mp_tac >>
     qpat_x_assum `tuple_val_wf vs stvs` mp_tac >>
     qpat_x_assum `tuple_val_wf vs dtvs` mp_tac >>
     qpat_x_assum `type_memory_size_list stvs = 0` mp_tac >>
     qpat_x_assum `type_memory_size_list dtvs = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     map_every qid_spec_tac [`vs`, `stvs`, `dtvs`, `stys`, `dtys`] >>
     Induct >> rpt gen_tac >> Cases_on `stys` >> Cases_on `dtvs` >>
     Cases_on `stvs` >> Cases_on `vs` >>
     simp[OPT_MMAP_def, AllCaseEqs(), value_has_type_def,
         val_wf_def, type_memory_size_def] >> rpt strip_tac >> gvs[] >>
     first_x_assum irule >> simp[]) >>
  irule typed_copy_zero_fields_checked >> simp[] >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `stvs` >> simp[] >>
  (rpt gen_tac >> disch_tac >>
      `type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
       evaluate_type tenv dty = SOME dtv /\ value_has_type stv v /\
       value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
       type_memory_size stv = 0 /\ type_memory_size dtv = 0` by
        (fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
      `MEM dty dtys` by
        (qpat_x_assum `MEM _ (ZIP _)` mp_tac >>
         simp[MEM_ZIP, LENGTH_ZIP] >> strip_tac >>
         simp[MEM_EL] >> metis_tac[]) >>
      qpat_x_assum `!dty sty dtv stv v. _`
        (qspecl_then [`dty`, `sty`, `dtv`, `stv`, `v`] mp_tac) >>
      simp[]) >>
  metis_tac[]
QED

Finalise typed_copy_zero_fields_from_semantics

Theorem typed_copy_zero_rank_run[local]:
  !n cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    type_rank cenv.ce_struct_fields dty = n /\
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
    type_memory_size stv = 0 /\ type_memory_size dtv = 0 /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n dw < dimword (:256) /\ w2n dw <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 0 s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `dty`
  >~ [`BaseT bt`] >- suspend "base"
  >~ [`ArrayT de bd`] >- suspend "array"
  >~ [`TupleT ts`] >- suspend "tuple"
  >~ [`StructT name`] >- suspend "struct"
  >~ [`FlagT name`] >- gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  gvs[evaluate_type_def, Once compile_store_memory_typed_def,
      is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
      compile_copy_memory_def, comp_return_def] >>
  qexists_tac `s` >> simp[val_in_memory_def, typed_copy_state_frame_refl,
    gas_marked_path_def, gas_path_mem_rules]
QED

Resume typed_copy_zero_rank_run[base]:
  Cases_on `bt` >>
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Resume typed_copy_zero_rank_run[array]:
  Cases_on `bd`
  >- suspend "fixed" >>
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Resume typed_copy_zero_rank_run[fixed]:
  qpat_x_assum `!m. m < _ ==> _` (mk_asm "ih") >>
  drule_all typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb' = Fixed n'` by
    (drule typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  rename1 `ArrayTV tv' (Fixed n')` >>
  `n' < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed n')) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `n' <= n' * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typed_copy_default_widening] >>
  suspend "fixed_run"
QED

Resume typed_copy_zero_rank_run[fixed_run]:
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  gvs[type_memory_size_def] >>
  `!i. i < n' ==> val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v) /\
     val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (gen_tac >> strip_tac >> conj_tac
     >- (irule typed_copy_sparse_lookup_wf >> qexists_tac `n'` >> fs[val_wf_def]) >>
     asm_rewrite_tac[] >> irule typed_copy_sparse_lookup_wf >>
     qexists_tac `n'` >> fs[val_wf_def]) >>
  suspend "fixed_child"
QED

Resume typed_copy_zero_rank_run[fixed_child]:
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       (!i. i < n' ==> val_in_memory tv'
         (case ALOOKUP l i of NONE => default_value tv | SOME v => v)
         (w2n dw + i * type_memory_size tv') t.vs_memory) /\
       typed_copy_state_frame sa (w2n dw) 0 s t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule (BETA_RULE (Q.INST [`f` |-> `\i. case ALOOKUP l i of NONE => default_value tv | SOME v => v`]
       (SPEC_ALL typed_copy_zero_sarray_checked_path))) >> simp[] >>
     goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`tv`, `sw`, `tenv`] >> simp[] >>
     (conj_tac >- suspend "fixed_ih") >>
     gvs[externalReturnBufferlessNormalizeTheory.return_zero_wf_memory]) >>
  qexists_tac `t` >> simp[] >>
  irule externalReturnBufferlessNormalizeTheory.return_zero_wf_memory >>
  simp[type_memory_size_def]
QED

Resume typed_copy_zero_rank_run[fixed_ih]:
  rpt strip_tac >>
  `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by metis_tac[] >>
  `value_has_type tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[default_value_well_typed, cj 1 evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by metis_tac[] >>
  `value_has_type tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[default_value_well_typed, cj 1 evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  asm "ih" (qspec_then `type_rank cenv.ce_struct_fields de` mp_tac) >>
  simp[Once type_rank_def] >> disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw'`, `tenv`] >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  Cases_on `ALOOKUP l i` >> gvs[]
QED

Resume typed_copy_zero_rank_run[tuple]:
  qpat_x_assum `!m. m < _ ==> _` (mk_asm "ih") >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys ts` by
    (drule typed_copy_tuple_widening >>
     gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
     metis_tac[place_store_tuple_children_widen]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[type_memory_size_def, val_wf_def, val_in_memory_def] >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule typed_copy_zero_fields_from_semantics >> simp[] >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  asm "ih" (qspec_then `type_rank cenv.ce_struct_fields dty` mp_tac) >>
  (impl_tac >- metis_tac[member_rank_lt_tuple]) >>
  disch_then irule >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw'`, `tenv`] >> simp[] >> metis_tac[]
QED

Resume typed_copy_zero_rank_run[struct]:
  qpat_x_assum `!m. m < _ ==> _` (mk_asm "ih") >>
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
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `tvs` >>
     Induct_on `args` >> Cases_on `tvs` >> simp[type_memory_size_def]) >>
  gvs[type_memory_size_def, val_in_memory_def, typed_copy_fields_tuple_zip] >>
  suspend "struct_run"
QED

Resume typed_copy_zero_rank_run[struct_run]:
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    suspend "struct_bytes" >>
  `compile_struct_typed_copy cenv dst src fields fields 0 0 =
    compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) 0 0` by
    (irule placeMemoryTypedBaseTheory.typed_memory_struct_copy_fields >>
     fs[EVERY_MEM]) >>
  gvs[] >>
  irule typed_copy_zero_fields_from_semantics >> simp[] >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  asm "ih" (qspec_then `type_rank cenv.ce_struct_fields dty` mp_tac) >>
  (impl_tac >- suspend "struct_rank") >>
  disch_then irule >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw'`, `tenv`] >> simp[] >> metis_tac[]
QED

Resume typed_copy_zero_rank_run[struct_bytes]:
  (conj_tac >- metis_tac[]) >>
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by simp[] >>
  qpat_x_assum `OPT_MMAP _ (MAP (FST o SND) fields) = SOME tvs` mp_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  qpat_x_assum `!ty tv. evaluate_type tenv ty = SOME tv ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qid_spec_tac `tvs` >> Induct_on `fields` >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[OPT_MMAP_def, AllCaseEqs()] >> rpt strip_tac >> metis_tac[]
QED

Resume typed_copy_zero_rank_run[struct_rank]:
  `MEM dty (MAP (FST o SND) fields)` by metis_tac[] >>
  qpat_x_assum `MEM dty (MAP SND args)` kall_tac >>
  fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  `MEM (y0,dty,y2) (get_struct_fields cenv.ce_struct_fields
      (nsid_to_string name))` by simp[get_struct_fields_def] >>
  drule_all member_rank_lt_struct >> simp[type_rank_def, nsid_to_string_def]
QED

Finalise typed_copy_zero_rank_run


Theorem compile_store_memory_typed_zero_run_mem:
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
    type_memory_size stv = 0 /\ type_memory_size dtv = 0 /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 0 s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> irule typed_copy_zero_rank_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`stv`, `sw`, `tenv`] >> simp[] >> metis_tac[]
QED
