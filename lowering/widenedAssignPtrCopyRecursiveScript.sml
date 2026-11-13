(* Rank closure of counted pointer-safe typed copying. *)
Theory widenedAssignPtrCopyRecursive
Ancestors
  widenedAssignPtrCopyPrimitive widenedAssignPtrCopyFields
  widenedAssignPtrCopyStaticArray widenedAssignPtrCopyDynamicArray
  placeTypedCopyRecursivePath typedCopyDomain typedMemoryCopy
  valueEncodingDefs valueEncoding valueEncodingProps vyperTyping
  vyperTypeSystem vyperTypeArgFits vyperTypeExprSoundness vyperValue context compileEnv
  bodyPtrDefs ptrDiscipline fragGasPathPtr fragExec
  words finite_map pred_set list arithmetic venomState venomExecSemantics abiValueEncoding

Theorem widened_assign_typed_store_counted_ptr:
  !cenv tenv ctx D PG dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
    !a b dst src dw sw fn G tn s.
      compile_store_memory_typed cenv dst dty src sty a = ((),b) /\
      (!x. dst = Var x ==> not_fresh_at a x) /\
      (!x. src = Var x ==> not_fresh_at a x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      op_taint tn dst = {} /\ op_taint tn src = {} /\
      (0 < type_memory_size dtv ==>
        ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size dtv)) /\
      (0 < type_memory_size stv ==>
        ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      (w2n dw + type_memory_size dtv <= w2n sw \/
       w2n sw + type_memory_size stv <= w2n dw) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n sw) m) /\
      fn_has_code a b fn /\ 
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      ?G' tn' t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
        (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n dw) m) /\
        typed_copy_state_frame a (w2n dw) (type_memory_size dtv) s t /\
        (!x. not_fresh_at a x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
        tn'.t_imm = tn.t_imm /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
          (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  ntac 5 gen_tac >> measureInduct_on `type_rank cenv.ce_struct_fields dty` >>
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def,
          AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (ho_match_mp_tac widened_assign_typed_sarray_counted >> simp[] >>
          qexists_tac `tenv` >> simp[] >> (conj_tac >- metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          qpat_x_assum `!y. type_rank _ y < _ ==> _` (qspec_then `cd` mp_tac) >> simp[] >>
          disch_then assume_tac >> strip_tac >>
          first_x_assum ho_match_mp_tac >> simp[] >> metis_tac[])
      >> ho_match_mp_tac widened_assign_typed_dynarray_counted >> simp[] >>
          qexists_tac `tenv` >> simp[] >> (conj_tac >- metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          qpat_x_assum `!y. type_rank _ y < _ ==> _` (qspec_then `cd` mp_tac) >> simp[] >>
          disch_then assume_tac >> strip_tac >>
          first_x_assum ho_match_mp_tac >> simp[] >> metis_tac[])
  >~ [`TupleT dtys`]
  >- (ho_match_mp_tac widened_assign_typed_fields_counted >> simp[] >>
          qexists_tac `tenv` >> simp[] >> (conj_tac >- metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          qpat_x_assum `!y. type_rank _ y < _ ==> _` (qspec_then `cd` mp_tac) >> simp[] >>
          disch_then assume_tac >> strip_tac >>
          first_x_assum ho_match_mp_tac >> simp[] >> metis_tac[])
  >~ [`StructT name`]
  >- (ho_match_mp_tac widened_assign_typed_fields_counted >> simp[] >>
          qexists_tac `tenv` >> simp[] >> (conj_tac >- metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          qpat_x_assum `!y. type_rank _ y < _ ==> _` (qspec_then `cd` mp_tac) >> simp[] >>
          disch_then assume_tac >> strip_tac >>
          first_x_assum ho_match_mp_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[value_has_type_def] >> rpt gen_tac >> strip_tac >>
  `b = a` by
    gvs[Once compile_store_memory_typed_def, is_word_type_def,
        is_bytestring_type_def, type_memory_bytes_def,
        contextPropsTheory.compile_copy_memory_zero] >>
  qexistsl_tac [`G`,`tn`,`s`] >>
  simp[val_in_memory_def, typed_copy_state_frame_refl, cj 1 gas_path_ptr_rules]
QED

Resume widened_assign_typed_store_counted_ptr[word]:
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
  `type_memory_size dtv = 32` by
    metis_tac[abiValueEncodingTheory.abi_word_type_size] >>
  rpt gen_tac >> strip_tac >> gvs[eval_operand_def] >>
  drule_all widened_assign_typed_word_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`t`] >> simp[]
QED

Resume widened_assign_typed_store_counted_ptr[bytes]:
  qpat_x_assum `!y. type_rank _ y < _ ==> _` kall_tac >>
  drule_all typed_copy_bytestring_source >> strip_tac >>
  `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
      0 < type_memory_size tv` by
    (Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >>
         rw[is_bytestring_type_def, evaluate_type_def, AllCaseEqs()] >>
         simp[type_memory_size_def]) >>
     rw[evaluate_type_def, AllCaseEqs()] >> simp[type_memory_size_def]) >>
  `0 < type_memory_size stv /\ 0 < type_memory_size dtv` by metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[eval_operand_def] >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all widened_assign_typed_bytes_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`t`] >> simp[]
QED

Finalise widened_assign_typed_store_counted_ptr
