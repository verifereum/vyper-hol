(* Widening with no extra aggregate capacity cannot shift live layout. *)
Theory bodyPtrStructLitLayoutTransfer
Ancestors vyperTypeArgFits vyperTypeSystem vyperTypeValues valueEncoding valueEncodingDefs
  exprSimHyps list arithmetic vyperValue valueEncodingProofs

Theorem arg_type_fits_memory_size:
  (!t u tv uv.
    arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
    evaluate_type tenv u = SOME uv ==>
    type_memory_size tv <= type_memory_size uv) /\
  (!ts us tvs uvs.
    arg_types_fit ts us /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL (\u uv. evaluate_type tenv u = SOME uv) us uvs ==>
    type_memory_size_list tvs <= type_memory_size_list uvs)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def, type_memory_size_def] >>
  all_tac
  >~ [`word_size _ <= word_size _`]
  >- (irule word_size_monotone >> simp[])
  >~ [`word_size _ <= word_size _`]
  >- (irule word_size_monotone >> simp[])
  >~ [`_ * _ <= _ * _`]
  >- (irule LESS_MONO_MULT2 >> simp[])
  >~ [`_ + _ <= _ + _`]
  >- (irule LESS_EQ_LESS_EQ_MONO >> simp[] >>
      first_x_assum irule >> simp[])
  >> first_x_assum irule >> simp[]
QED

Theorem type_widens_to_memory_size:
  type_widens_to tenv t u /\ evaluate_type tenv t = SOME tv /\
  evaluate_type tenv u = SOME uv ==>
  type_memory_size tv <= type_memory_size uv
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[arg_type_fits_memory_size]
QED

Theorem elems_in_memory_equal_stride[local]:
  type_memory_size tv = type_memory_size uv /\
  (!v a. val_wf tv v /\ val_in_memory uv v a mem ==>
         val_in_memory tv v a mem) ==>
  !vs a. elems_val_wf vs tv /\ elems_in_memory vs a uv mem ==>
    elems_in_memory vs a tv mem
Proof
  strip_tac >> Induct >> simp[val_wf_def, val_in_memory_def] >>
  metis_tac[]
QED

Theorem kvs_in_memory_equal_stride[local]:
  type_memory_size tv = type_memory_size uv /\
  (!v a. val_wf tv v /\ val_in_memory uv v a mem ==>
         val_in_memory tv v a mem) ==>
  !kvs a n. kvs_val_wf kvs tv n /\ kvs_in_memory kvs a uv mem ==>
    kvs_in_memory kvs a tv mem
Proof
  strip_tac >> Induct >> simp[val_wf_def, val_in_memory_def] >>
  Cases >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem arg_type_fits_equal_size_memory:
  (!t u tv uv v a mem.
    arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
    evaluate_type tenv u = SOME uv /\
    type_memory_size uv <= type_memory_size tv /\
    val_wf tv v /\ val_in_memory uv v a mem ==>
    val_in_memory tv v a mem) /\
  (!ts us tvs uvs vs a mem.
    arg_types_fit ts us /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL (\u uv. evaluate_type tenv u = SOME uv) us uvs /\
    type_memory_size_list uvs <= type_memory_size_list tvs /\
    tuple_val_wf vs tvs /\ tuple_in_memory vs uvs a mem ==>
    tuple_in_memory vs tvs a mem)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def]
  >~ [`val_in_memory (BaseTV (StringT _)) _ _ _`]
  >- (Cases_on `v` >> gvs[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[val_in_memory_def])
  >~ [`val_in_memory (BaseTV (BytesT (Dynamic _))) _ _ _`]
  >- (Cases_on `v` >> gvs[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[val_in_memory_def])
  >~ [`val_in_memory (ArrayTV _ (Dynamic _)) _ _ _`]
  >- suspend "dynamic_array"
  >~ [`val_in_memory (ArrayTV _ (Fixed _)) _ _ _`]
  >- (`type_memory_size elem_tv' <= type_memory_size elem_tv` by
        metis_tac[arg_type_fits_memory_size] >>
      `type_memory_size elem_tv = type_memory_size elem_tv'` by
        (fs[type_memory_size_def]) >>
      `default_value elem_tv = default_value elem_tv'` by
        metis_tac[arg_type_fits_default_value] >>
      Cases_on `v` >> gvs[val_in_memory_def, val_wf_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[val_in_memory_def, val_wf_def] >> conj_tac
      >- (irule kvs_in_memory_equal_stride >>
          conj_tac >- (qexists `m` >> simp[]) >>
          qexists `elem_tv` >> simp[]) >>
      rpt strip_tac >> first_x_assum irule >>
      simp[val_wf_default_value_proof])
  >~ [`val_in_memory (TupleTV _) _ _ _`]
  >- (Cases_on `v` >> gvs[val_in_memory_def, val_wf_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[val_in_memory_def, val_wf_def, type_memory_size_def] >>
      first_x_assum irule >> simp[] >> qexists `tvs` >> simp[])
  >> `type_memory_size tv <= type_memory_size uv` by
       metis_tac[arg_type_fits_memory_size]
  >> `type_memory_size_list ys <= type_memory_size_list ys'` by
       metis_tac[arg_type_fits_memory_size]
  >> `type_memory_size tv = type_memory_size uv /\
      type_memory_size_list ys = type_memory_size_list ys'` by
       (gvs[type_memory_size_def] >> decide_tac)
  >> Cases_on `vs` >> gvs[val_wf_def, val_in_memory_def]
  >> first_x_assum irule >> simp[] >> qexists `ys'` >> simp[]
QED

(* evaluate_type requires positive array bounds.  Thus the zero-bound
   branches mentioned by the abstract product argument are unreachable here. *)
Resume arg_type_fits_equal_size_memory[dynamic_array]:
  `type_memory_size elem_tv' <= type_memory_size elem_tv` by
    metis_tac[arg_type_fits_memory_size] >>
  `n * type_memory_size elem_tv <= m * type_memory_size elem_tv` by
    (irule LESS_MONO_MULT2 >> simp[]) >>
  `type_memory_size elem_tv = type_memory_size elem_tv'` by
    (gvs[type_memory_size_def] >>
     `n * type_memory_size elem_tv <= n * type_memory_size elem_tv'` by
       (irule LESS_EQ_TRANS >> qexists `m * type_memory_size elem_tv` >>
        simp[]) >> fs[]) >>
  Cases_on `v` >> gvs[val_in_memory_def, val_wf_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[val_in_memory_def, val_wf_def] >>
  irule elems_in_memory_equal_stride >> simp[] >> qexists `elem_tv` >> simp[]
QED
Finalise arg_type_fits_equal_size_memory

Theorem type_widens_to_equal_size_memory:
  type_widens_to tenv t u /\ evaluate_type tenv t = SOME tv /\
  evaluate_type tenv u = SOME uv /\
  type_memory_size uv <= type_memory_size tv /\
  val_wf tv v /\ val_in_memory uv v a mem ==>
  val_in_memory tv v a mem
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[arg_type_fits_equal_size_memory]
QED

Theorem type_widens_to_equal_size_robust_memory:
  type_widens_to tenv t u /\ evaluate_type tenv t = SOME tv /\
  evaluate_type tenv u = SOME uv /\
  type_memory_size uv <= type_memory_size tv /\ val_wf tv v /\
  (!mem. mem_agree_outside taint m mem ==> val_in_memory uv v a mem) ==>
  !mem. mem_agree_outside taint m mem ==> val_in_memory tv v a mem
Proof
  metis_tac[type_widens_to_equal_size_memory]
QED
