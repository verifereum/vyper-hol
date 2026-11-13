(* Declared allocation capacity is obtained from a particular field lookup,
   not from mere nonemptiness of the literal. *)
Theory bodyPtrStructLitWordCapacity
Ancestors exprSimAggregateLayout compileEnv list alist

Theorem alookup_size_sum_bound[local]:
  !fields name ty n.
  ALOOKUP fields name = SOME (ty,n) ==>
  n <= SUM (MAP (SND o SND) fields)
Proof
  Induct >> simp[] >> qx_gen_tac `h` >> PairCases_on `h` >>
  simp[] >> rpt gen_tac >> IF_CASES_TAC >> gvs[] >>
  strip_tac >> res_tac >> decide_tac
QED

Theorem word_type_arg_fits[local]:
  !ty t. is_word_type ty /\ arg_type_fits ty t ==> t = ty
Proof
  Cases >> Cases_on `t` >> rpt strip_tac >>
  gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT b1) (BaseT b2)` >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[is_word_type_def, vyperTypeSystemTheory.arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT (BytesT d1)) (BaseT (BytesT d2))` >>
  Cases_on `d1` >> gvs[is_word_type_def] >>
  Cases_on `d2` >> gvs[vyperTypeSystemTheory.arg_type_fits_def]
QED

Theorem structlit_word_field_capacity:
  expr_body_pre ce cx env (StructLit ann nsid kes) es /\
  MEM (fname,e) kes /\ is_word_type (expr_type e) ==>
  32 <= SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))
Proof
  strip_tac >> drule struct_literal_lookup_types >> strip_tac >>
  `?n. n < LENGTH kes /\ EL n kes = (fname,e)` by metis_tac[MEM_EL] >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >>
  rpt (first_x_assum (qspec_then `n` mp_tac)) >> simp[EL_MAP] >>
  rpt strip_tac >> drule alookup_size_sum_bound >>
  drule_all word_type_arg_fits >> strip_tac >> gvs[] >>
  `type_memory_bytes ce (expr_type e) = 32` by
    (qpat_x_assum `is_word_type _` mp_tac >>
     Cases_on `expr_type e` >> simp[is_word_type_def, type_memory_bytes_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_word_type_def, type_memory_bytes_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[is_word_type_def, type_memory_bytes_def]) >> simp[]
QED
