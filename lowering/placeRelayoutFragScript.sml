(* Outcome composition for raw-RHS, target, and widened place stores. *)
Theory placeRelayoutFrag
Ancestors
  placeRelayoutOutcome placeRelayoutGasCompose placeRelayoutCode
  stmtSimProps exprLoweringProps loweringPosts stmtSimDefs gasOutcome gasSummary
  stmtSimDeclCompose
  stmtSimAssignStorage stmtSimAugAssignPlaceMemory compileEnv freshWrites

Theorem relayout_store_stmt_post:
  vv_post ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
  target_post ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty) tr s2 /\
  sa.cs_next_var <= sv.cs_next_var /\ sv.cs_next_var <= st.cs_next_var /\
  stmt_state_rel ctx func cenv cx ff u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
  (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
  u.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf ==>
  stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ()) ff u
Proof
  strip_tac >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  fs[vv_post_def, target_post_def] >> rpt strip_tac >>
  `not_fresh_at sv x /\ not_fresh_at st x` by
    metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem place_pointer_write_gas_obs:
  place_ptr_rel cenv cx s (PlaceR p) w loc vt /\
  write_place cx p v ee = (res,ff) ==>
  !tail. write_place cx p v (ee with gas_obs := tail) =
    (res,ff with gas_obs := tail)
Proof
  Cases_on `p`
  >- (pure_rewrite_tac[vyperStateTheory.write_place_def] >>
      rpt strip_tac >>
      simp[stmtSimAssignStorageTheory.write_storage_slot_gas_obs])
  >- metis_tac[aug_place_memory_write_gas_obs] >>
  simp[place_ptr_rel_def]
QED

(* Lift a physical store outcome without changing its normal-or-exit split. *)
Theorem relayout_store_gas_outcome:
  vv_post ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
  target_post ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty) tr s2 /\
  sa.cs_next_var <= sv.cs_next_var /\ sv.cs_next_var <= st.cs_next_var /\
  ~block_is_terminated sf /\ write_place cx p v ee = (res,ff) /\
  gas_marked_path F ctx func s2 0 r /\
  ((?u. r = OK u /\ res = INL () /\
     stmt_state_rel ctx func cenv cx ff u /\
     (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
     ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
     u.vs_inst_idx = LENGTH sf.cs_current_insts) \/
   (exit_result r /\ stmt_exit RetQ ff res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (write_place cx p v) (ee,s2)
    (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. write_place cx p v (ee with gas_obs := tail) =
      (res,ff with gas_obs := tail)` by
    (irule place_pointer_write_gas_obs >>
     fs[target_post_def] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl_tac [`res`, `ff`, `r`] >>
  (conj_tac >- simp[gas_marked_exec_def]) >>
  qpat_x_assum `(?u. _) \/ _` strip_assume_tac
  >- (disj1_tac >> qexists_tac `u` >> simp[stmt_post_end_gas_obs] >>
      irule relayout_store_stmt_post >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >>
  `expr_exit res r` suffices_by simp[stmt_exit_def] >>
  Cases_on `res` >- fs[stmt_exit_def] >>
  drule vyperExprNoControlTheory.write_place_no_control >>
  fs[stmt_exit_def, vyperExprNoControlTheory.no_control_exc_def]
QED
