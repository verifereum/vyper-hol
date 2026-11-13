(* Gas adapter for an already-loaded direct immutable tuple target. *)
Theory tupleAssignImmutableDeployHead
Ancestors
  tupleAssignImmutableDeployStep tuplePlaceHeadOpen

Theorem tuple_immutable_head_gas_continuation_open:
  tuple_place_head ctx func ce cx es lo sp tys ltys ltvs vs elems w i s0 /\
  ~block_is_terminated sp /\ body_inv tops ctx ce cx /\ cx.in_deploy /\
  expr_sim_inv ce cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  well_typed_target env (TopLevelNameTarget (src,id)) (EL i tys) /\
  call_evaluation_safe cx (int_calls_target (TopLevelNameTarget (src,id))) /\
  compile_get_target_ptr compile_expr ce (TopLevelNameTarget (src,id)) sp = (place,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> ce.ce_target CapMcopy) /\
  type_alloc_ok ce (TupleT tys) /\ i < LENGTH tys /\
  (let dst = FST place; loc_opt = FST (SND place); dst_ty_opt = SND (SND place);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc ce.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value ce dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes ce dty)) sa) = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\ local_ptrs_reserved ce sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  (!ff t. ~block_is_terminated sb /\ expr_sim_inv ce cx env ff /\
    tuple_place_head ctx func ce cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    alloca_frame ce es sp s0 ce ff t ==>
    gas_outcome F (cx_tops cx) (ctx,func) next (ff with gas_obs := [],t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx (TopLevelNameTarget (src,id)))
      (\p. ignore_bind (write_place cx p (EL i vs)) next)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `ity = EL i tys` by
    (drule_all immutableAssignMetadataTheory.immutable_assign_bare_global >> strip_tac >>
     fs[vyperTypeSystemTheory.well_typed_target_def,
        vyperTypeSystemTheory.well_typed_expr_def, AllCaseEqs()] >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  `evaluate_type (get_tenv cx) ity = SOME (EL i tvs) /\
   evaluate_type (get_tenv cx) (EL i ltys) = SOME (EL i ltvs) /\
   type_widens_to (get_tenv cx) (EL i ltys) ity` by metis_tac[] >>
  `value_has_type (EL i ltvs) (EL i vs)` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def,
        vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> gvs[]) >>
  `well_typed_target env (TopLevelNameTarget (src,id)) ity` by simp[] >>
  drule_all tupleAssignImmutableDeploySourceTheory.tuple_immutable_source_write >>
  strip_tac >>
  drule_all tuple_immutable_loaded_head_step >> strip_tac >>
  `gas_marked_exec F (ctx,func)
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0) [] (INL (ImmutablePlace src id [])) es (OK s0)` by
    (simp[gasSummaryTheory.gas_marked_exec_def] >> conj_tac
     >- (gen_tac >>
         irule immutableAssignMetadataTheory.immutable_target_place_state >>
         simp[] >>
         qexistsl [`ce`, `ctx`, `env`, `ity`, `tops`] >>
         simp[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     simp[fragGasModeTheory.gas_marked_path_def] >>
     irule (cj 1 fragGasPathTheory.gas_path_rules) >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  irule tuplePlaceHeadGasTheory.tuple_place_gas_outcome_prefix >>
  goal_assum (drule_at Any) >>
  BETA_TAC >>
  irule tuplePlaceHeadGasTheory.tuple_place_write_gas_prefix >>
  qexistsl [`ff with gas_obs := []`, `q`] >>
  conj_tac >- metis_tac[tuplePlaceSourceGasTheory.tuple_place_write_gas_obs] >>
  simp[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED
