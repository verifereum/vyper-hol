(* Outcome composition for raw-RHS, target, and widened place stores. *)
Theory placeRelayoutFrag
Ancestors
  placeRelayoutOutcome placeRelayoutGasCompose placeRelayoutCode
  stmtSimProps exprLoweringProps loweringPosts stmtSimDefs gasOutcome gasSummary
  stmtSimDeclCompose placeRelayoutPhysicalSource exprSimIfExpWidenedCounted
  annassignRelayoutPost exprLowering context
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

Theorem widened_target_store_gas_outcome:
  vv_post ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
  compile_expr cenv (expr_type e) e sa = (vv,sv) /\
  post_value_type cenv e = sty /\ lowered_value_type cenv e = sty /\
  sty <> expr_type e /\ ~is_word_type sty /\ ~is_bytestring_type sty /\
  target_post ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s2 /\
  compile_get_target_ptr compile_expr cenv bt sv =
    ((dst,SOME loc,SOME (ValPT dty)),st) /\
  compile_assign_value cenv dst loc (vv_operand vv) (is_word_type dty)
    (vv_location vv) dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) st = ((),sf) /\
  ci_mono sa sv /\ ci_mono sv st /\
  local_ptrs_reserved cenv sv /\ local_ptrs_reserved cenv st /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sv x /\ not_fresh_at st x) /\
  (!l. vv_operand vv <> Label l) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv sty < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  cenv.ce_target CapMcopy /\ storage_place_region cx p /\
  write_place cx p v ee = (res,ff) /\ stmt_res_ok lctx res /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
  ~s2.vs_halted /\ s2.vs_current_bb = st.cs_current_bb /\
  s2.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (write_place cx p v) (ee,s2)
    (stmt_post ctx func cx lctx cenv cenv sa sf s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv e <> expr_type e /\
   ~is_word_type (post_value_type cenv e) /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv` by fs[] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` by
    (drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
     gvs[vv_location_def]) >>
  drule_all strict_widened_vv_physical_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx mid s1` by fs[vv_post_def] >>
  `MAP FDOM mid.scopes = MAP FDOM ee.scopes` by
    fs[target_post_def, locals_kept_def] >>
  `0 < type_memory_size stv` by metis_tac[strict_widening_source_positive] >>
  `sv.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= sv.cs_next_var /\
   sv.cs_next_var <= st.cs_next_var` by fs[ci_mono_def, cs_extends_def] >>
  `expr_val_own cenv cx sty sa sv mid v (vv_operand vv) s1` by metis_tac[] >>
  `sv.cs_next_id <= sv.cs_next_id` by simp[] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` by simp[] >>
  `?r. gas_marked_path F ctx func s2 0 r /\
    ((?u. r = OK u /\ res = INL () /\
       stmt_state_rel ctx func cenv cx ff u /\
       (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
       (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
          FLOOKUP u.vs_allocas aid = SOME b) /\
       ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
       u.vs_inst_idx = LENGTH sf.cs_current_insts) \/
      (exit_result r /\ stmt_exit RetQ ff res r))` by
    (irule owned_target_relayout_store_outcome >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `assign_alloc_ok _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `expr_val_own _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`compile_expr`, `env`, `vv_location vv`] >>
     fs[]) >>
  irule relayout_store_gas_outcome >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
