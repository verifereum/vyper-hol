(* The second ECAdd point is read and used at the same reached cut. *)
Theory bodyECAddSecondPointMods
Ancestors
  bodyFullPostsMods bodyMemEcArithOperands bodyPtrPrecompileBuiltinsBoundary
  exprOperandVar exprLoweringProps loweringPosts stateRelProj vyperStorageFootprint
  vyperTypeExprSoundness

Theorem ecadd_second_point_at_cut_mods:
  expr_type e2 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  post_value_type cenv e2 = expr_type e2 /\
  lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
  local_ptrs_reserved cenv s1 /\
  value_runtime_typed env (expr_type e2) v2 /\
  storage_trace_domain cx st0 es2.storage_trace /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2) ==>
  ?q w lq. y = Var q /\ lookup_var q t2 = SOME w /\ not_fresh_at s2 q /\
    expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lq s2 es2 v2 (Var q) t2 /\
    expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 (Var q) t2 /\
    ptr_covers G2 tn2 q t2 64 /\
    w2n w + 64 < dimword (:256) /\ w2n w + 64 <= t2.vs_alloca_next /\
    (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn2.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `storage_trace_domain _ _ _`
    (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
  qpat_assum `post_value_type _ _ = _` (fn post_ty =>
    qpat_assum `expr_type _ = _` (fn ann_ty =>
      rule_assum_tac (PURE_REWRITE_RULE [post_ty,ann_ty]))) >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2` by
    fs[value_runtime_typed_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
  qpat_assum `expr_val_rel _ _ _ y t2`
    (qx_choose_then `w` (assume_tac o CONJUNCT1) o REWRITE_RULE [expr_val_rel_def]) >>
  drule_all_then strip_assume_tac ec_point_read_ready >>
  `w2n w + 64 <= t2.vs_alloca_next` by
    (irule ec_point_read_capacity >>
     qpat_assum `expr_store_bound _ _ v2 _ t2` (irule_at Any) >> simp[]) >>
  `t2.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  drule_all_then assume_tac compile_lower_value_var >>
  qpat_x_assum `y = Var _` SUBST_ALL_TAC >>
  rename1 `ptr_covers G2 tn2 q t2 64` >>
  qexistsl_tac [`q`,`w`,`s1`] >> fs[venomStateTheory.eval_operand_def] >> decide_tac
QED
