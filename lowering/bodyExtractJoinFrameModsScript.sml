(* Join the prepared Extract32 source and forced offset at one horizon. *)
Theory bodyExtractJoinFrameMods
Ancestors
  bodyFullPostsMods bodyFullExtract32JoinFrame wordArgsPtr exprSimWordArgs
  loweringPosts loweringStateRelDefs bodyPtrDefs bodyFullShadowBodyInv
  vyperAST venomState finite_map list

Theorem extract32_join_frame_mods:
  stmt_state_rel H ctx func cenv cx es s0 /\
  expr_post_mods H ctx func cenv cx src es sa sn s0 mid v src_op u /\
  expr_post_mods H ctx func cenv cx off mid sn sq u ee w off_op t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sn G1 tn1 u G2 tn2 /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id ==>
  stmt_state_rel H ctx func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 t /\
  (~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) ==>
    pure_frame cenv func es sa s0 t) /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[expr_post_mods_def] >> strip_tac >>
  conj_tac
  >- (qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  conj_tac
  >- (qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  conj_tac
  >- (irule extract32_join_wb_frame >>
      qpat_assum `expr_post _ _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[]) >>
  conj_tac
  >- (strip_tac >> irule (SIMP_RULE (srw_ss()) [] extract32_join_pure_frame) >>
      qpat_assum `expr_post _ _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[]) >>
  simp[] >>
  qpat_assum `expr_post _ _ _ _ _ src _ _ _ _ _ _ _ _`
    (assume_tac o MATCH_MP expr_post_frame) >>
  drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans
QED
