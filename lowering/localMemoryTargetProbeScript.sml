(* Runtime resources exported by a joint local-memory target endpoint. *)
Theory localMemoryTargetProbe
Ancestors
  bodyFullTargetDefs bodyPtrDefs loweringPosts exprLoweringProps
  loweringStateRelDefs compileEnv exprSimProps bodyMemoryDefs
  assignBasePtrOffset vyperState vyperLookup venomState ptrDiscipline
  exprSimHypsDefs vyperTypeEnv vyperTypeInvariants
  words finite_map arithmetic

Theorem local_memory_entry_types:
  expr_sim_inv cenv cx env es0 /\ FLOOKUP env.var_types id = SOME ty /\
  es.scopes = es0.scopes /\ lookup_scopes id es.scopes = SOME entry ==>
  cenv.ce_var_type id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >>
  `env_consistent env cx es0 /\ state_well_typed es0 /\
   env.type_defs = get_tenv cx /\ cenv.ce_var_type id = SOME ty` by
    (fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
     metis_tac[]) >>
  `lookup_scopes id es0.scopes = SOME entry` by metis_tac[] >>
  drule_all env_consistent_lookup_var_type >> strip_tac >> gvs[] >>
  `EVERY scope_well_typed es0.scopes` by fs[state_well_typed_def] >>
  drule_all scope_well_typed_lookup_scopes >> simp[]
QED

Theorem memory_target_store_resources:
  target_post H ctx func cenv cx origin sa sb s0 es
    (PlaceR (MemoryPlace id path)) (Type ty) (Var xd,SOME LocMemory,ann) s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path))
    (Var xd,SOME LocMemory,ann) G tn s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  (!t0. cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  ?p cap bw dw k tv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    lookup_var p s = SOME bw /\ lookup_var xd s = SOME dw /\
    mem_path_offset entry.type path = SOME (k,tv) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    w2n dw = w2n bw+k /\
    type_memory_size entry.type <= cap /\
    w2n bw+cap <= s.vs_alloca_next /\
    w2n dw+type_memory_size tv <= s.vs_alloca_next /\
    w2n dw+type_memory_size tv < dimword (:256) /\
    ptr_covers G tn xd s (type_memory_size tv) /\
    local_region cenv es.scopes s id (w2n bw) cap /\ not_fresh_at sb xd
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   ?dw. lookup_var xd s = SOME dw /\
     place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) dw
       (SOME LocMemory) (Type ty)` by
    fs[target_post_def,eval_operand_def] >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def,NoAsms] >> strip_tac >>
  `tv0 = entry.type` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `type_memory_size entry.type <= sz /\ w2n b+sz <= s.vs_alloca_next` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`id`,`entry`,`p`,`sz`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt,stmt_state_rel_def] >>
  `w2n b+k < dimword (:256) /\ k < dimword (:256)` by decide_tac >>
  `w2n (b+n2w k) = w2n b+k` by
    (`w2n (b+n2w k) = w2n b+w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[] >> decide_tac) >>
  `ptr_covers G tn p s sz` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `op_taint tn (Var xd) = {} /\ FLOOKUP G xd = FLOOKUP G p` by
    fs[target_ptr_ok_def,op_prov_def] >>
  `ptr_covers G tn xd s (type_memory_size tv)` by
    (qpat_assum `ptr_covers G tn p s sz`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_covers_def]) >>
     disch_then (qx_choosel_then [`rootw`,`site`,`sitecap`] strip_assume_tac) >>
     `rootw = b` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `rootw = b` SUBST_ALL_TAC >>
     simp[ptr_covers_def] >>
     qexistsl_tac [`site`,`sitecap`] >> simp[] >> decide_tac) >>
  `not_fresh_at sb xd` by fs[target_post_def] >>
  simp[local_region_def] >> decide_tac
QED
