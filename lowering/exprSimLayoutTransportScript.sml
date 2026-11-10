Theory exprSimLayoutTransport
Ancestors
  loweringPosts
  exprSimProps vyperTypeSystem vyperValue valueEncoding valueEncodingDefs vyperTypeArgFits
  vyperTypeValues context compileEnv valueTypingMemoryProps

Theorem expr_val_rel_nonword_transport[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ ~is_word_type dst /\
  (!b mem. val_in_memory sv v b mem ==> val_in_memory dv v b mem) /\
  expr_val_rel cx src v op s ==>
  expr_val_rel cx dst v op s
Proof
  simp[expr_val_rel_def] >> metis_tac[]
QED

Theorem expr_val_at_nonword_transport[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ ~is_word_type dst /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  expr_val_own cenv cx src sa sb es v op s ==>
  expr_val_at cenv cx dst sa sb es v op s
Proof
  strip_tac >> fs[expr_val_at_def, expr_val_own_def] >>
  first_x_assum (qspec_then `sv` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `w` >> simp[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem evaluated_layout_size:
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  evaluate_type tenv src = SOME sv /\
  evaluate_type tenv dst = SOME dv /\
  type_memory_bytes cenv src = type_memory_bytes cenv dst ==>
  type_memory_size sv = type_memory_size dv
Proof
  metis_tac[]
QED

Theorem compatible_base_memory:
  arg_type_fits (BaseT src) (BaseT dst) /\
  evaluate_type tenv (BaseT src) = SOME sv /\
  evaluate_type tenv (BaseT dst) = SOME dv ==>
  (val_in_memory sv v b mem <=> val_in_memory dv v b mem)
Proof
  Cases_on `src` >> Cases_on `dst` >>
  simp[arg_type_fits_def] >> rpt strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), arg_type_fits_def] >>
  Cases_on `v` >> simp[val_in_memory_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def]
QED

Theorem elems_memory_transport[local]:
  type_memory_size sv = type_memory_size dv /\
  (!v b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem) ==>
  !vs b mem. elems_in_memory vs b sv mem <=> elems_in_memory vs b dv mem
Proof
  strip_tac >> Induct >> simp[val_in_memory_def]
QED

Theorem kvs_memory_transport[local]:
  type_memory_size sv = type_memory_size dv /\
  (!v b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem) ==>
  !vs b mem. kvs_in_memory vs b sv mem <=> kvs_in_memory vs b dv mem
Proof
  strip_tac >> Induct >> simp[val_in_memory_def] >>
  Cases >> simp[val_in_memory_def]
QED

Theorem array_memory_transport[local]:
  type_memory_size sv = type_memory_size dv /\
  default_value sv = default_value dv /\
  (!v b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem) /\
  (!n. (sb = Fixed n <=> db = Fixed n)) ==>
  !v b mem. val_in_memory (ArrayTV sv sb) v b mem <=>
            val_in_memory (ArrayTV dv db) v b mem
Proof
  strip_tac >> Cases >> simp[val_in_memory_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def] >>
  metis_tac[elems_memory_transport, kvs_memory_transport]
QED

Theorem compatible_layout_memory:
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) ==>
  (!src dst sv dv.
    arg_type_fits src dst /\ punnable cenv src dst /\
    evaluate_type tenv src = SOME sv /\ evaluate_type tenv dst = SOME dv ==>
    !v b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem) /\
  (!ts us tvs uvs.
    arg_types_fit ts us /\ punnable_list cenv ts us /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us uvs ==>
    !vs b mem. tuple_in_memory vs tvs b mem <=> tuple_in_memory vs uvs b mem)
Proof
  strip_tac >> ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def] >> gvs[]
  >>~- ([`evaluate_type tenv (BaseT _) = SOME _`],
     irule compatible_base_memory >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[arg_type_fits_def])
  >>~- ([`evaluate_type tenv (ArrayT _ _) = SOME _`],
     imp_res_tac evaluate_type_ArrayT_cases >>
     gvs[punnable_def] >> irule array_memory_transport >>
     simp[] >> metis_tac[evaluated_layout_size, arg_type_fits_default_value])
  >~ [`evaluate_type tenv (TupleT _) = SOME _`]
  >- (imp_res_tac evaluate_type_TupleT_cases >> gvs[punnable_def] >>
      Cases_on `v` >> simp[val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def])
  >> gvs[punnable_def] >>
  `type_memory_size tv = type_memory_size tv'` by
    metis_tac[evaluated_layout_size] >>
  Cases_on `vs` >> simp[val_in_memory_def] >> metis_tac[]
QED

Theorem compatible_word_type:
  arg_type_fits src dst ==> (is_word_type src <=> is_word_type dst)
Proof
  Cases_on `src` >> Cases_on `dst` >> simp[arg_type_fits_def, is_word_type_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def, is_word_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT sb)) (BaseT (BytesT db))` >>
  Cases_on `sb` >> Cases_on `db` >> gvs[arg_type_fits_def, is_word_type_def]
QED

Theorem compatible_footprint:
  arg_type_fits src dst /\ evaluate_type tenv src = SOME sv /\
  evaluate_type tenv dst = SOME dv /\ type_memory_size sv = type_memory_size dv ==>
  val_footprint sv v = val_footprint dv v
Proof
  Cases_on `src` >> Cases_on `dst` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> gvs[]
  >~ [`evaluate_type tenv (BaseT _) = SOME _`]
  >- (Cases_on `b` >> Cases_on `b'` >> gvs[arg_type_fits_def] >>
      gvs[evaluate_type_def, AllCaseEqs(), arg_type_fits_def] >>
      Cases_on `v` >> simp[val_footprint_def])
  >> imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >> gvs[] >>
  Cases_on `v` >> simp[val_footprint_def]
QED

Theorem expr_val_rel_layout_transport:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  same_memory_layout cenv src dst /\ arg_type_fits src dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ ~is_word_type dst /\
  expr_val_rel cx src v op s ==>
  expr_val_rel cx dst v op s
Proof
  strip_tac >> irule expr_val_rel_nonword_transport >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  fs[same_memory_layout_def] >>
  metis_tac[compatible_word_type, compatible_layout_memory]
QED

Theorem expr_val_at_layout_transport:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  same_memory_layout cenv src dst /\ arg_type_fits src dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ ~is_word_type dst /\
  value_has_type dv v /\ expr_val_own cenv cx src sa sb es v op s ==>
  expr_val_at cenv cx dst sa sb es v op s
Proof
  strip_tac >> irule expr_val_at_nonword_transport >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `type_memory_size sv = type_memory_size dv` by
    (fs[same_memory_layout_def] >> metis_tac[evaluated_layout_size]) >>
  qexistsl_tac [`dv`, `sv`] >> simp[] >>
  rpt conj_tac
  >- metis_tac[compatible_word_type]
  >- metis_tac[compatible_footprint]
  >> metis_tac[value_has_type_memory_wf]
QED
