(* The AugAssign RHS runs only after all three source-place tests. *)
Theory bodyAugToStoreMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods augAssignFullSaved augAssignFullRhsSaved
  stmtSimAugAssignPlaceMemory gasOutcomeFullMods fragGasOriginPtr fragGasOrigin
  fragExec

Theorem augassign_reached_rhs_sim_mods:
  (!s p t s3 cur t3 s4 ptv t4.
     eval_target_place cx target s = (INL p,t) /\
     read_place cx p s3 = (INL cur,t3) /\
     place_type_value cx p s4 = (INL ptv,t4) ==>
     body_expr_full_ok_mods mods exps cx e) /\
  eval_target_place cx target entry = (INL p,mid) /\
  read_place cx p mid = (INL cur,mid) /\
  place_type_value cx p mid = (INL ptv,mid) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env mid /\
  expr_body_pre_mods mods cenv cx env e mid ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e mid
Proof
  strip_tac >>
  `body_expr_full_ok_mods mods exps cx e` by metis_tac[] >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  strip_tac >>
  qpat_x_assum `!a b c d e f g h i j k l m n. _ ==>
      expr_sim_full_mods _ _ _ _ _ _ /\ _` mp_tac >>
  metis_tac[]
QED

(* Refinement of the very same RHS execution, preserving the captured
   destination and old word.  The original outcome retains all nonnormal
   alternatives, including exemption in another module. *)
Theorem augassign_rhs_keep_operands_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R /\
  local_ptrs_reserved cenv sa /\
  (!x. FST place = Var x ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST place) s0 = SOME addr /\
  eval_operand old s0 = SOME word /\
  target_ptr_ok cenv (PlaceR p) place G0 tn0 s0 /\
  op_taint tn0 old = {} /\ op_prov G0 old = NONE ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      eval_operand (FST place) t = SOME addr /\
      eval_operand old t = SOME word /\
      target_ptr_ok cenv (PlaceR p) place G tn t /\
      op_taint tn old = {} /\ op_prov G old = NONE) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (disj1_tac >> qexists_tac `t` >> gvs[] >>
          `t.vs_labels = s0.vs_labels` by
            metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                      aug_place_marked_path_labels] >>
          drule_all_then strip_assume_tac augassign_saved_rhs_frame >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
