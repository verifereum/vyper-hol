(* Semantic source boundary for direct immutable array iterators. *)
Theory whitelistForIterImmSource
Ancestors
  bodySimDeclCases exprSimTopLevelImmutable exprSimCopy exprSimHypsDefs
  vyperInterpreter vyperState vyperValueOperation vyperTypeEnv
  valueEncodingProps valueEncodingTyping vyperAST vyperTypeInvariants
  vyperTyping vyperValue list finite_map
Libs
  monadsyntax

Theorem eval_iterator_immutable_array:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name name ts = NONE /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (atv, ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME atv ==>
  !gs. eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name)))
         (es with gas_obs := gs) =
       (INL (array_elements atv av), es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[lookup_global_def, read_result_def, read_place_def,
       get_immutables_def, get_address_immutables_def,
       evaluate_subscripts_def, lift_option_type_def, lift_sum_def,
       bind_def, return_def, expr_type_def, extract_elements_def]
QED

Theorem immutable_array_source_ready:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) ==>
  ?off ts imms atv av.
    src = cenv.ce_module /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name name ts = NONE /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) name = SOME (atv, ArrayV av) /\
    evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME atv /\
    value_has_type atv (ArrayV av) /\ well_formed_type_value atv /\
    off + type_memory_size atv < dimword (:256) /\
    (!gs. eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name)))
            (es with gas_obs := gs) =
          (INL (array_elements atv av), es with gas_obs := gs))
Proof
  strip_tac >>
  `env_consistent env cx es /\ state_well_typed es` by fs[expr_sim_inv_def] >>
  `env_context_consistent env cx` by fs[env_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
  drule_all env_consistent_bare_global_ready_src >> strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target`
  >- gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `FLOOKUP (get_source_immutables src imms) name = SOME pair` >>
  PairCases_on `pair` >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME pair0` by
    (fs[env_consistent_def, env_immutables_consistent_def] >> metis_tac[]) >>
  `value_has_type pair0 pair1 /\ well_formed_type_value pair0` by
    (fs[state_well_typed_def, listTheory.EVERY_MEM] >>
     `MEM (cx.txn.target, imms) es.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
     first_x_assum drule >> simp[] >>
     simp[imms_well_typed_def] >> strip_tac >>
     Cases_on `ALOOKUP imms src` >> gvs[get_source_immutables_def] >>
     metis_tac[]) >>
  `?tv. pair0 = ArrayTV tv bd` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >>
  `?av. pair1 = ArrayV av` by
    (Cases_on `bd` >> Cases_on `pair1` >> fs[value_has_type_def]) >>
  gvs[] >>
  `src = cenv.ce_module /\
   ?off. FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
         off + type_memory_size (ArrayTV tv bd) < dimword (:256)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  qexists_tac `off` >> simp[] >>
  irule eval_iterator_immutable_array >> metis_tac[]
QED
