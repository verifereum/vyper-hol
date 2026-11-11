Theory bodyPtrIfExpInterpretation
Ancestors
  bodyPtrIfExpRuntimeLayout bodyPtrIfExpDefaults valueEncoding valueEncodingDefs
  vyperTypeSystem vyperTypeValues context

Theorem ifexp_elems_in_memory_transport:
  !stv dtv mem.
    type_memory_size stv = type_memory_size dtv /\
    (!v off. val_in_memory stv v off mem ==> val_in_memory dtv v off mem) ==>
    !vs off. elems_in_memory vs off stv mem ==> elems_in_memory vs off dtv mem
Proof
  rpt gen_tac >> strip_tac >> Induct >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem ifexp_kvs_in_memory_transport:
  !stv dtv mem.
    type_memory_size stv = type_memory_size dtv /\
    (!v off. val_in_memory stv v off mem ==> val_in_memory dtv v off mem) ==>
    !vs off. kvs_in_memory vs off stv mem ==> kvs_in_memory vs off dtv mem
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- simp[val_in_memory_def] >>
  Cases_on `h` >> simp[val_in_memory_def] >> metis_tac[]
QED

Theorem ifexp_array_in_memory_transport:
  !sv dv sb db.
    type_memory_size sv = type_memory_size dv /\
    default_value sv = default_value dv /\
    (!n. db = Fixed n ==> sb = Fixed n) /\
    (!v off mem. val_in_memory sv v off mem ==> val_in_memory dv v off mem) ==>
    !v off mem. val_in_memory (ArrayTV sv sb) v off mem ==>
                val_in_memory (ArrayTV dv db) v off mem
Proof
  rpt gen_tac >> strip_tac >> Cases >>
  simp[val_in_memory_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[val_in_memory_def] >> rpt strip_tac
  >- metis_tac[ifexp_elems_in_memory_transport]
  >- metis_tac[ifexp_kvs_in_memory_transport]
  >> metis_tac[]
QED

Theorem ifexp_arg_type_fits_in_memory_mutual:
  (!st dt. arg_type_fits st dt ==>
    !ce cx env es sv dv.
    expr_sim_inv ce cx env es /\ punnable ce st dt /\
    evaluate_type (get_tenv cx) st = SOME sv /\
    evaluate_type (get_tenv cx) dt = SOME dv ==>
    !v off mem. val_in_memory sv v off mem ==> val_in_memory dv v off mem) /\
  (!sts dts. arg_types_fit sts dts ==>
    !ce cx env es svs dvs.
    expr_sim_inv ce cx env es /\ punnable_list ce sts dts /\
    LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) sts svs /\
    LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) dts dvs ==>
    !vs off mem. tuple_in_memory vs svs off mem ==> tuple_in_memory vs dvs off mem)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[arg_type_fits_def, punnable_def]
  >~ [`evaluate_type _ (BaseT (StringT _)) = SOME _`]
  >- (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      Cases >> simp[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def])
  >~ [`evaluate_type _ (BaseT (BytesT (Dynamic _))) = SOME _`]
  >- (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      Cases >> simp[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def])
  >>~- ([`evaluate_type _ (ArrayT _ _) = SOME _`],
    rpt gen_tac >> strip_tac >>
    imp_res_tac evaluate_type_ArrayT_cases >> gvs[] >>
    drule_all ifexp_equal_compiler_runtime_sizes >> strip_tac >>
    drule_all (cj 1 vyperTypeArgFitsTheory.arg_type_fits_default_value) >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    irule ifexp_array_in_memory_transport >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >~ [`evaluate_type _ (TupleT _) = SOME _`]
  >- (rpt gen_tac >> strip_tac >>
      imp_res_tac evaluate_type_TupleT_cases >> gvs[] >>
      Cases >> simp[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def] >>
      metis_tac[])
  >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all ifexp_equal_compiler_runtime_sizes >> strip_tac >>
  Cases >> simp[val_in_memory_def] >> metis_tac[]
QED

Theorem ifexp_arg_type_fits_in_memory:
  !ce cx env es st dt sv dv.
    expr_sim_inv ce cx env es /\ arg_type_fits st dt /\ punnable ce st dt /\
    evaluate_type (get_tenv cx) st = SOME sv /\
    evaluate_type (get_tenv cx) dt = SOME dv ==>
    !v off mem. val_in_memory sv v off mem ==> val_in_memory dv v off mem
Proof
  metis_tac[cj 1 ifexp_arg_type_fits_in_memory_mutual]
QED

Theorem ifexp_arg_types_fit_in_memory:
  !ce cx env es sts dts svs dvs.
    expr_sim_inv ce cx env es /\ arg_types_fit sts dts /\
    punnable_list ce sts dts /\
    LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) sts svs /\
    LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) dts dvs ==>
    !vs off mem. tuple_in_memory vs svs off mem ==> tuple_in_memory vs dvs off mem
Proof
  metis_tac[cj 2 ifexp_arg_type_fits_in_memory_mutual]
QED

Theorem ifexp_type_widens_in_memory:
  !ce cx env es st dt sv dv.
    expr_sim_inv ce cx env es /\ type_widens_to (get_tenv cx) st dt /\
    punnable ce st dt /\
    evaluate_type (get_tenv cx) st = SOME sv /\
    evaluate_type (get_tenv cx) dt = SOME dv ==>
    !v off mem. val_in_memory sv v off mem ==> val_in_memory dv v off mem
Proof
  rw[type_widens_to_def]
  >- gvs[] >>
  metis_tac[ifexp_arg_type_fits_in_memory]
QED
