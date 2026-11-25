(* An evaluated membership needle survives the reached array operand. *)
Theory bodyMembershipNeedleAtRhsMods
Ancestors
  bodyFullPostsMods bodyPtrDefs exprBodyPreProps exprBodyPreTypingProps
  exprSimSource exprWordOperand exprSimBopInLiteralWord loweringPosts
  ptrDiscipline venomState vyperTypeInvariants vyperTypeSystem

Theorem membership_needle_at_rhs_mods:
  is_word_type (expr_type e1) /\
  expr_body_pre_mods mods cenv cx env e1 es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME et /\
  expr_post_mods H1 ctx func cenv cx e1 es sa s1 s0 mid needle x t /\
  ptr_val_ok cx (post_value_type cenv e1) needle x G1 tn1 t /\
  vv_post_mods H2 ctx func cenv cx e2 mid s1 sm t fin tv vv u /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 ==>
  eval_operand x u = SOME (typed_val_to_w256 et needle) /\
  op_prov G2 x = NONE /\ op_taint tn2 x = {}
Proof
  strip_tac >>
  `eval_operand x t = SOME (typed_val_to_w256 et needle)` by
    (irule literal_word_post_operand >>
     qhdtm_assum `expr_post_mods`
       (irule_at Any o CONJUNCT1 o REWRITE_RULE [expr_post_mods_def]) >> simp[]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    fs[ptr_val_ok_def,post_value_type_word] >>
  `(!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
     `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
       (simp[well_formed_type_def] >> rpt strip_tac >>
        drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
     drule_all_then strip_assume_tac lower_value_word_shape >> simp[]) >>
  Cases_on `x` >> fs[eval_operand_def,op_prov_def]
  >- simp[op_taint_def] >>
  rename1 `not_fresh_at s1 z` >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  conj_tac
  >- (qpat_assum `!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> _`
        irule >> simp[]) >>
  qhdtm_x_assum `ghost_kept_at`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!z. not_fresh_at s1 z ==> FLOOKUP G2 z = _ /\ _`
    (qspec_then `z` mp_tac) >> simp[]
QED
