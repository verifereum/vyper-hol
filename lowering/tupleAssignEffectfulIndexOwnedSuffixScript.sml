(* Effectful tuple suffixes with an explicitly owned RHS snapshot. *)
Theory tupleAssignEffectfulIndexOwnedSuffix
Ancestors
  tupleAssignEffectfulIndexOwnedPointer tupleAssignEffectfulIndexOwnedStore
  tuplePlaceHeadOpen tuplePlaceSuffixOpen tuplePlaceSourceHead
  bodySim exprSimHypsDefs vyperEvalExprPreservesScopesDom
  tuplePlaceHead tuplePlaceHeadGas tuplePlaceSource tuplePlaceSourceGas
  tuplePlacePointerReady gasSummary tuplePlaceWriteOutcome

Theorem tuple_effectful_store_normalize[local]:
  FST (SND r) = SOME loc /\ SND (SND r) = SOME (ValPT dty) /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  (is_word_type sty <=> is_word_type dty) ==>
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       l = case loc_opt of SOME l => l | NONE => LocMemory;
       dt = case dst_ty_opt of SOME (ValPT t) => t | _ => sty;
       arr = case dt of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
         | _ => NONE
   in (if is_word_type sty then
        if is_word_type dt then compile_store_at_loc cenv.ce_imm_alloca dst el loc_opt
        else emit_void INVALID []
      else compile_assign_value cenv dst l el (is_word_type dt) NONE dt sty arr
        (type_memory_bytes cenv dt)) sa) =
  (if is_word_type sty then
     emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
       [FST r;el]
   else compile_assign_value cenv (FST r) loc el (is_word_type dty) NONE dty sty
     (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
       | _ => NONE) (type_memory_bytes cenv dty)) sa
Proof
  rpt strip_tac >> Cases_on `is_word_type sty` >>
  fs[stmtLoweringTheory.compile_store_at_loc_def]
QED

Theorem tuple_effectful_owned_marked_step[local]:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      aid < sp.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)) /\
  target_pre cenv cx env bt es /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\ ~immutable_root cx bt /\
  gas_marked_exec F (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) mid (OK s) /\
  target_post ctx func cenv cx es sp sa s0 (mid with gas_obs := [])
    (PlaceR p) (Type (EL i tys)) r s /\
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
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys;
       arr = case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
         | _ => NONE
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) arr (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ff t. write_place cx p (EL i vs) (mid with gas_obs := []) = (INL (),ff) /\
    expr_sim_inv cenv cx env ff /\
    gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
      ?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
        aid < sb.cs_next_id /\ b <= w2n w /\
        w2n w + type_memory_size_list ltvs <= b+sz /\
        (!n lb lsz. local_region cenv ff.scopes t n lb lsz ==>
          b+sz <= lb \/ lb+lsz <= b)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv es sp s0 cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec _ _ _ (es,s0) marks _ _ _` >>
  `eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL p,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `target_pre cenv cx env bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  `value_has_type (EL i ltvs) (EL i vs)` by
    fs[tuple_place_head_def, vyperTypeDefaultsTheory.values_have_types_LIST_REL,
       listTheory.LIST_REL_EL_EQN] >>
  `value_has_type (EL i tvs) (EL i vs)` by
    (irule tuple_place_destination_value_typed >> metis_tac[]) >>
  Cases_on `write_place cx p (EL i vs) (mid with gas_obs := [])` >>
  rename1 `write_place _ _ _ _ = (res,ff)` >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) s` by
    fs[loweringPostsTheory.target_post_def] >>
  `res = INL ()` by (irule tuple_place_source_write_success >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  `expr_sim_inv cenv cx env ff` by
    (irule tuple_place_source_write_endpoint >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule tuple_place_target_base_inversion >> strip_tac >>
  `tuple_place_head ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    lo sp tys ltys ltvs vs elems w i s0` by simp[] >>
  `target_post ctx func cenv cx
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
    sp sa s0 (mid with gas_obs := []) (PlaceR p) (Type (EL i tys)) r s` by simp[] >>
  Q.SUBGOAL_THEN
   `EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
    ?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      aid < sp.cs_next_id /\ b <= w2n w /\
      w2n w + type_memory_size_list ltvs <= b+sz /\
      (!n lb lsz. local_region cenv
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).scopes s0 n lb lsz ==>
        b+sz <= lb \/ lb+lsz <= b)` assume_tac >-
    (qpat_assum `EVERY _ _ \/ _` mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  drule_all tuple_effectful_owned_pointer_head >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := []) /\ storage_place_region cx p` by
    (drule_all tuple_place_source_target_endpoint >> simp[]) >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id (mid with gas_obs := []).scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `(?dw. eval_operand (FST r) s = SOME dw /\
     place_ptr_rel cenv cx s (PlaceR p) dw (FST (SND r)) (Type (EL i tys))) /\
   SND (SND r) = SOME (ValPT (EL i tys)) /\
   (!x. FST r = Var x ==> not_fresh_at sa x)` by
    fs[loweringPostsTheory.target_post_def, exprLoweringTheory.value_type_place_def] >>
  Q.SUBGOAL_THEN
   `?loc. FST (SND r) = SOME loc /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)`
    (qx_choose_then `loc` (map_every assume_tac o CONJUNCTS)) >-
    (drule tuplePlaceOpenTheory.tuple_place_success_descriptor_probe >> simp[]) >>
  drule_all tuple_place_index_fit >> strip_tac >>
  `place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type (EL i tys))` by
    (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all tuple_effectful_store_normalize >>
  disch_then (qspecl_then [`sa`,`EL i elems`,`cenv`] (fn th =>
    qpat_x_assum `(let dst = _ in _) = _` (assume_tac o REWRITE_RULE [th]))) >>
  Q.SUBGOAL_THEN
   `?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (EVERY is_word_type ltys \/ type_memory_size_list ltvs = 0 \/
      ?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
        aid < sb.cs_next_id /\ b <= w2n w /\
        w2n w + type_memory_size_list ltvs <= b+sz /\
        (!n lb lsz. local_region cenv ff.scopes t n lb lsz ==>
          b+sz <= lb \/ lb+lsz <= b)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    alloca_frame cenv (mid with gas_obs := []) sa s cenv ff t`
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >-
    (irule tuple_effectful_owned_store_head >>
     qpat_assum `tuple_place_head _ _ _ _ (mid with gas_obs := []) _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ (mid with gas_obs := [])` (irule_at Any) >>
     simp[] >> qexistsl [`NONE`,`loc`,`dw`,`FST r`] >> simp[] >>
     qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
     Cases_on `is_word_type (EL i tys)` >> simp[]) >>
  qexistsl [`ff`,`t`] >> asm_rewrite_tac[] >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  qexistsl [`cenv`,`mid with gas_obs := []`,`s`,`sa`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- fs[loweringPostsTheory.target_post_def] >>
      qpat_assum `target_post _ _ _ _ es _ _ _ _ _ _ _ _`
        (mp_then Any mp_tac stmtSimDefsTheory.target_post_alloca_frame) >>
      (impl_tac >- (conj_tac
          >- fs[tuple_place_head_def] >>
          conj_tac >- fs[tuple_place_head_def] >>
          drule eval_base_place_preserves_scopes_dom >> simp[])) >>
      simp[]) >>
  metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr,
    exprLoweringPropsTheory.ci_mono_def, pairTheory.SND]
QED
