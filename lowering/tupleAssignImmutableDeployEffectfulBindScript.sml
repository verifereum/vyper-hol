(* Target evaluation is composed with a store at its actual endpoint. *)
Theory tupleAssignImmutableDeployEffectfulBind
Ancestors
  tuplePlaceHeadOpen tuplePlaceSourceHead stmtSimDefs tuplePlaceHeadGas
  tuplePlaceTargetGas targetPlaceSimCases gasSummary fragGasMode fragGasPath
  tuplePlaceOpen tuplePlacePointerReady

Theorem tuple_effectful_head_bind_conditional:
  (!ee s p dst dw loc ff.
    tuple_place_head ctx func cenv cx ee lo sa tys ltys ltvs vs elems w i s /\
    assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
      type_memory_size (EL j tvs)+64 < dimword (:256) /\
      type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
    (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
    type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
    (if is_word_type (EL i ltys) then
       compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) (SOME loc)
     else compile_assign_value cenv dst loc (EL i elems) (is_word_type (EL i tys)) NONE
       (EL i tys) (EL i ltys) (type_memory_bytes cenv (EL i tys))) sa = ((),sb) /\
    eval_operand dst s = SOME dw /\
    place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    write_place cx p (EL i vs) ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (loc = LocMemory /\ ~EVERY is_word_type ltys ==>
      w2n w + type_memory_size_list ltvs <= w2n dw \/
      w2n dw + type_memory_size (EL i tvs) <= w2n w) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
      alloca_frame cenv ee sa s cenv ff t) /\
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  ~block_is_terminated sp /\ target_pre cenv cx env bt es /\
  target_sim ctx func cenv cx env bt es /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\ ~immutable_root cx bt /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  fn_has_code sp sa func /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sp.cs_next_var <= sa.cs_next_var /\
  (!marks p mid s.
    gas_marked_exec F (ctx,func) (eval_target_place cx bt)
      (es,s0) marks (INL p) mid (OK s) /\
    target_post ctx func cenv cx es sp sa s0 (mid with gas_obs := [])
      (PlaceR p) (Type (EL i tys)) r s ==>
    tuple_place_head ctx func cenv cx (mid with gas_obs := []) lo sa
      tys ltys ltvs vs elems w i s /\
    MAP FDOM mid.scopes = MAP FDOM es.scopes /\
    (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (!dw loc. eval_operand (FST r) s = SOME dw /\
      FST (SND r) = SOME loc /\ loc = LocMemory /\ ~EVERY is_word_type ltys ==>
      w2n w + type_memory_size_list ltvs <= w2n dw \/
      w2n dw + type_memory_size (EL i tvs) <= w2n w)) /\
  (!ff t. ~block_is_terminated sb /\ expr_sim_inv cenv cx env ff /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==> lookup_var x t = SOME v) /\
    (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv es sp s0 cenv ff t ==>
    gas_outcome F (cx_tops cx) (ctx,func) next (ff with gas_obs := [],t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt)
      (\p. ignore_bind (write_place cx p (EL i vs)) next)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es` by fs[targetPlaceSimTheory.target_pre_def] >>
  `target_indices_pre cenv cx env bt` by fs[targetPlaceSimTheory.target_pre_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (drule_all tuple_place_target_gas_admissible >> simp[]) >>
  `type_place_target env bt = SOME (Type (EL i tys))` by
    fs[vyperTypeSystemTheory.well_typed_target_def] >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
    (\res ee t. ?p. res = INL p /\
      target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r t /\
      t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (irule target_place_sim >> simp[] >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >> metis_tac[]) >>
  irule tuple_place_gas_outcome_bind_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (rpt strip_tac >> Cases_on `res` >>
    gvs[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  suspend "endpoint"
QED

Resume tuple_effectful_head_bind_conditional[endpoint]:
  rename1 `gas_marked_exec _ _ _ _ marks (INL p) mid (OK s)` >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `target_pre cenv cx env bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `value_has_type (EL i ltvs) (EL i vs)` by
    fs[tuplePlaceHeadTheory.tuple_place_head_def,
       vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (irule tuple_place_destination_value_typed >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\ storage_place_region cx p` by
    (drule_all tuple_place_source_target_endpoint >> simp[]) >>
  Cases_on `write_place cx p (EL i vs) (mid with gas_obs := [])` >>
  rename1 `write_place _ _ _ _ = (res,ff)` >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) s` by
    fs[loweringPostsTheory.target_post_def] >>
  `res = INL ()` by (irule tuplePlaceWriteOutcomeTheory.tuple_place_source_write_success >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> gvs[] >>
  `expr_sim_inv cenv cx env ff` by
    (irule tuple_place_source_write_endpoint >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!marks p mid s. _`
    (qspecl_then [`marks`, `p`, `mid`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "store"
QED

Resume tuple_effectful_head_bind_conditional[store]:
  `SND (SND r) = SOME (ValPT (EL i tys)) /\
   ?loc. FST (SND r) = SOME loc` by
    metis_tac[tuple_place_success_descriptor_probe] >>
  `?dw. eval_operand (FST r) s = SOME dw /\
    place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys)) /\
    (!x. FST r = Var x ==> not_fresh_at sa x)` by
    fs[loweringPostsTheory.target_post_def] >>
  `arg_type_fits (EL i ltys) (EL i tys)` by
    (drule_all tuple_place_index_fit >> simp[]) >>
  `is_word_type (EL i ltys) ==> is_word_type (EL i tys)` by
    metis_tac[tuple_place_word_fit_probe] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    alloca_frame cenv (mid with gas_obs := []) sa s cenv ff t` by
    (qpat_x_assum `!ee s p dst dw loc ff. _` irule >>
     qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> qexists `FST r` >> simp[] >>
     gvs[]) >>
  suspend "join"
QED

Resume tuple_effectful_head_bind_conditional[join]:
  `sp.cs_next_id <= sa.cs_next_id` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `alloca_frame cenv es sp s0 cenv (mid with gas_obs := []) s` by
    (simp[stmtSimDefsTheory.alloca_frame_gas_obs] >>
     irule target_post_alloca_frame >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def]) >>
  `alloca_frame cenv es sp s0 cenv ff t` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     fs[loweringPostsTheory.target_post_def]) >>
  `~block_is_terminated sb` by
    (irule (SRULE [LET_THM] tuple_place_success_store_open) >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_get_target_ptr _ _ _ _ = _` (irule_at Any) >>
     simp[] >> qexistsl [`EL i ltys`, `EL i elems`] >>
     gvs[SRULE [LET_THM] tuple_place_success_store_open]) >>
  irule tuple_place_write_gas_prefix >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.target_post_def] >> strip_tac >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Finalise tuple_effectful_head_bind_conditional
