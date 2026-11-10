(* Ordered suffix with success-only compiler openness. *)
Theory tuplePlaceSuffixOpen
Ancestors
  tuplePlaceHeadOpen tuplePlaceHeadGas tuplePlaceSource tuplePlaceHead tuplePlaceSuffixCode
  stmtSimForRounds tupleTargetStoreProps vyperInterpreter vyperState
  stmtLowering compileEnv fragGasMode fragGasPath exprSimHypsDefs
  vyperTypeDefaults list rich_list

Theorem tuple_place_suffix_run_open:
  !ctx func cenv cx env tops gs tys ltys tvs ltvs vs elems w lo.
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt)) gs /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ fn_inst_ids_distinct func ==>
  !i es sp sf s0.
    i <= LENGTH tys /\ expr_sim_inv cenv cx env es /\ ~block_is_terminated sp /\
    tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
    compile_tuple_store_all cenv (DROP i ltys) (DROP i gs) (DROP i elems) sp = ((),sf) /\
    fn_has_code sp sf func ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (assign_tuple_target_list cx (DROP i gs) (DROP i vs)) (es,s0)
      (\res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
        tuple_place_head ctx func cenv cx ff lo sf tys ltys ltvs vs elems w (LENGTH tys) t /\
        (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
        (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
          FLOOKUP t.vs_allocas id = SOME entry) /\
        alloca_frame cenv es sp s0 cenv ff t)
      (\res ff r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH ltys = LENGTH tys /\ LENGTH ltvs = LENGTH tys` by
    metis_tac[tuple_place_type_facts] >>
  `LENGTH gs = LENGTH tys` by fs[LIST_REL_EL_EQN] >>
  gen_tac >> measureInduct_on `LENGTH tys - i` >>
  rpt gen_tac >> strip_tac >>
  `LENGTH elems = LENGTH tys /\ LENGTH vs = LENGTH tys` by
    fs[tuple_place_head_def, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  Cases_on `i = LENGTH tys`
  >- (gvs[] >>
      `DROP (LENGTH tys) ltys = [] /\ DROP (LENGTH tys) gs = [] /\
       DROP (LENGTH tys) elems = [] /\ DROP (LENGTH tys) vs = []` by simp[] >>
      fs[DROP_LENGTH_TOO_LONG, Once compile_tuple_store_all_def,
         compileEnvTheory.comp_return_def] >>
      simp[DROP_LENGTH_TOO_LONG, Once evaluate_def] >>
      irule gas_outcome_return_path >>
      qexists `s0` >> simp[] >>
      conj_tac >- (irule stmtSimDefsTheory.alloca_frame_same >> simp[]) >>
      fs[tuple_place_head_def, gas_marked_path_def] >>
      metis_tac[gas_path_rules]) >>
  `i < LENGTH tys` by decide_tac >>
  `?bt. EL i gs = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt)` by
    fs[EVERY_EL] >>
  `well_typed_target env bt (EL i tys)` by
    (fs[LIST_REL_EL_EQN] >>
     qpat_x_assum `!n. n < LENGTH tys ==> well_typed_atarget _ _ _`
       (qspec_then `i` mp_tac) >>
     simp[vyperTypeSystemTheory.well_typed_atarget_def]) >>
  drule_all tuple_place_target_ready >> strip_tac >>
  drule_all tuple_place_suffix_code_parts >> strip_tac >>
  `DROP i gs = BaseTarget bt :: DROP (SUC i) gs` by simp[DROP_CONS_EL] >>
  `DROP i vs = EL i vs :: DROP (SUC i) vs` by simp[DROP_CONS_EL] >>
  asm_rewrite_tac[Once evaluate_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  irule (SRULE [ignore_bind_def] tuple_place_head_gas_continuation_open) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  simp[] >> qexistsl [`sb`,`env`] >>
  `local_ptrs_reserved cenv sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `sp` >> fs[tuple_place_head_def]) >>
  fs[LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!y. _ ==> _` (qspec_then `SUC i` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`ff with gas_obs := []`,`sb`,`sf`,`t`] mp_tac) >>
  `tuple_place_head ctx func cenv cx (ff with gas_obs := []) lo sb
    tys ltys ltvs vs elems w (SUC i) t` by
    (qpat_x_assum `tuple_place_head _ _ _ _ ff _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[tuple_place_head_def, tuplePlacePrefixCertTheory.tuple_place_snapshot_def,
          exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  simp[] >> disch_tac >>
  irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (irule stmtSimDefsTheory.alloca_frame_trans >>
      qexistsl [`cenv`, `ff`, `t`, `sb`] >>
      simp[stmtSimDefsTheory.alloca_frame_gas_obs] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sb x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED
