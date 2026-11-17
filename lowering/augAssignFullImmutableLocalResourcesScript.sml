(* Live local resources survive a declared immutable word replacement.
   Immutable declaration separation covers borrowed as well as owned locals. *)
Theory augAssignFullImmutableLocalResources
Ancestors
  stateRelProj wordLoadStorePtr bodyPtrDefs exprLoweringProps
  loweringStateRelDefs venomState finite_map pred_set words

Theorem augassign_immutable_store_local_resources:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_size tv = 32 /\
  es'.scopes = es.scopes /\
  u = (mstore off w s with vs_inst_idx := pc) /\
  tn' = (tn with t_mem := tn.t_mem DIFF {q | off <= q /\ q < off + 32}) ==>
  !name entry p sz.
    lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !v mem. lookup_var p s = SOME v /\
      mem_agree_outside tn'.t_mem u.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n v) mem
Proof
  strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `immutable_decl_sep cenv cx es.scopes s.vs_vars s.vs_allocas
     s.vs_alloca_next` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     simp[Once stmt_state_rel_def, immutable_alloca_sep_def]) >>
  qpat_x_assum `immutable_decl_sep _ _ _ _ _ _` mp_tac >>
  rewrite_tac[immutable_decl_sep_alt] >> strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz /\
   !v mem. lookup_var p s = SOME v /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n v) mem` by metis_tac[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name (w2n v) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n v + sz <= off \/ off + 32 <= w2n v` by
    metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  gvs[] >>
  drule mstore_local_robust >>
  simp[] >>
  metis_tac[]
QED
