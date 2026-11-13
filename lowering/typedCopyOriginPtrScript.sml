(*
 * The joint (gas-origin and pointer-ghost) path of a typed memory copy
 * between two pointer variables: the joint lift of placeTypedCopyRecursivePath's
 * compile_store_memory_typed_forward_run.
 *
 * TOP-LEVEL:
 *   compile_store_memory_typed_origin_ptr_path
 *   typed_copy_origin_ptr_rank_entry -- the rank induction over the kinds
 *)
Theory typedCopyOriginPtr
Ancestors
  typedCopyOriginPtrWord typedCopyOriginPtrBytes typedCopyOriginPtrFields
  typedCopyOriginPtrSArray typedCopyOriginPtrDynArray typedCopyOriginPtrBase
  placeTypedCopyRecursivePath fragGasOriginPtr fragGasOriginPtrDead bodyPtrDefs ptrDiscipline
  typedMemoryCopy compileEnv context typedCopyDomain vyperTypeSystem vyperTypeArgFits vyperValue vyperTyping valueEncoding valueEncodingDefs

Theorem typed_copy_origin_ptr_rank_entry:
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
    typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- (irule typed_copy_origin_ptr_word_entry >> simp[] >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (irule typed_copy_origin_ptr_bytestring_entry >> simp[] >>
      qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule typed_copy_origin_ptr_sarray_entry >> simp[] >>
          qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >> rpt strip_tac >>
          qpat_x_assum `!k. k < _ ==> _`
            (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
          simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >>
          simp[] >> metis_tac[]) >>
      irule typed_copy_origin_ptr_dynarray_entry >> simp[] >>
      qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >>
      simp[] >> metis_tac[])
  >~ [`TupleT dtys`]
  >- (irule typed_copy_origin_ptr_tuple_entry >> simp[] >>
      qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >>
      simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (irule typed_copy_origin_ptr_struct_entry >> simp[] >>
      qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> _`
        (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
      simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >>
      simp[] >> metis_tac[]) >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  simp[typed_copy_origin_ptr_entry_def] >> rpt strip_tac >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
      comp_return_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[val_in_memory_def, type_memory_size_def, typed_copy_state_frame_refl,
       gas_origin_ptr_path_rules]
QED

Theorem compile_store_memory_typed_origin_ptr_path:
  compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v` by
    (irule typed_copy_origin_ptr_rank_entry >> simp[] >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `typed_copy_origin_ptr_entry _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [typed_copy_origin_ptr_entry_def]) >>
  disch_then (qspecl_then [`lo`,`explicit`,`func`,`PG`,`xd`,`xs`,
    `sa`,`sb`,`s`,`G`,`tn`,`dw`,`sw`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  first_assum ACCEPT_TAC
QED
