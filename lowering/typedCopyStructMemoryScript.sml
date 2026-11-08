(* Joint memory execution for struct copies. *)
Theory typedCopyStructMemory
Ancestors
  typedCopyTupleMemory typedCopySemanticIndex typedMemoryCopy valueEncodingTyping typedCopyDomain
  context compileEnv emitHelper exprLoweringProps exprSimTuple
  exprSimAttributeFields vyperTypeABI vyperTypeSystem vyperTypeArgFits
  vyperValue vyperTyping venomExecSemantics venomState valueEncoding words list arithmetic

Theorem typed_copy_struct_entry_mem:
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
      !dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst cd src cs sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        val_in_memory cst cv (w2n sw) s.vs_memory /\
        w2n sw + type_memory_size cst < dimword (:256) /\
        w2n dw + type_memory_size cdt < dimword (:256) /\
        (w2n sw + type_memory_size cst <= w2n dw \/
         w2n dw + type_memory_size cdt <= w2n sw) /\
        w2n sw + type_memory_size cst <= s.vs_alloca_next /\
        w2n dw + type_memory_size cdt <= s.vs_alloca_next ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. val_in_memory cdt cv (w2n dw) t.vs_memory /\
               typed_copy_state_frame sa (w2n dw) (type_memory_size cdt) s t) (\r. F)) ==>
    !dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst (StructT name) src sty sa = ((),sb) /\
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
  rpt gen_tac >> strip_tac >>
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    metis_tac[typed_copy_struct_values, LENGTH_MAP] >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule typed_copy_tuple_children_widen >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    ((conj_tac >- metis_tac[]) >>
     irule typed_copy_struct_field_bytes >> qexistsl_tac [`tenv`, `tvs`] >>
     simp[] >>
     (conj_tac >- (rpt strip_tac >> irule typed_copy_memory_size >>
       qexists_tac `tenv` >> simp[] >> metis_tac[])) >> metis_tac[]) >>
  suspend "execution"
QED

Resume typed_copy_struct_entry_mem[execution]:
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `compile_struct_typed_copy cenv dst src fields fields 0 0 =
   compile_typed_copy_fields cenv dst src
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
    (drule_all typed_copy_struct_suffix_producer >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    typed_copy_tuple_frag_mem >>
  disch_then (qspecl_then [`ctx`, `tvs`, `tvs`, `vs`] mp_tac) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  simp[type_memory_size_def, val_in_memory_def,
       valueEncodingTypingTheory.type_memory_size_fields_zip, typed_copy_fields_tuple_zip] >>
  (impl_tac >- suspend "indexed") >> simp[]
QED

Resume typed_copy_struct_entry_mem[indexed]:
  markerLib.RESUME_TAC >>
  (conj_tac >- suspend "children" >>
   gvs[type_memory_size_def, val_in_memory_def,
       valueEncodingTypingTheory.type_memory_size_fields_zip,
       typed_copy_fields_tuple_zip])
QED

Resume typed_copy_struct_entry_mem[children]:
  markerLib.RESUME_TAC >> (gen_tac >> strip_tac >>
  `i < LENGTH (MAP SND args)` by simp[] >>
  drule_all typed_copy_semantic_index >> strip_tac >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  `MEM (EL i (MAP SND args)) (MAP (FST o SND) fields)` by
    metis_tac[EL_MEM] >>
  `type_rank cenv.ce_struct_fields (EL i (MAP SND args)) <
   type_rank cenv.ce_struct_fields (StructT name)` by
    (qpat_x_assum `MEM _ (MAP (FST o SND) fields)` mp_tac >>
     simp[MEM_MAP] >> strip_tac >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,EL i (MAP SND args),y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all member_rank_lt_struct >>
     simp[type_rank_def, nsid_to_string_def]) >>
  qpat_x_assum `!cd cs cdt cst cv. _` (drule_then assume_tac) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `EL i tvs` >> qexists_tac `sw'` >> simp[])
QED

Finalise typed_copy_struct_entry_mem
