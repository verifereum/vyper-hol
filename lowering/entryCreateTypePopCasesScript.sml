(* A bound builtin is compiled without a fetch. Preserve the nil endpoint
   from the full-value producer when packaging the scoped VV outcome. *)
Theory entryCreateTypePopCases
Ancestors
  entryCreateCompositeFocus entryCreateFocusSpec bodyFullTypeBuiltinWords
  bodyFullEmptyLeafData exprSimFullBundleProps s1PrefixDefs gasExplicitSites

Theorem create_type_builtin_literal_vv_case:
  expr_body_pre ce cx env (TypeBuiltin ann tb typ args) es /\
  is_word_type ann /\
  (!tail. eval_expr cx (TypeBuiltin ann tb typ args) (es with gas_obs := tail) =
          (INL (Value v),es with gas_obs := tail)) /\
  (!sa. compile_expr ce ty (TypeBuiltin ann tb typ args) sa = (StackValue ann (Lit w),sa)) /\
  (!rt. evaluate_type (get_tenv cx) ann = SOME rt ==> typed_val_to_w256 rt v = w) ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (TypeBuiltin ann tb typ args) es /\
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty (TypeBuiltin ann tb typ args) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (TypeBuiltin ann tb typ args)) (es,s0)
Proof
  strip_tac >> conj_tac
  >- (rw[expr_vv_sim_scoped_def] >>
      `expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc)
        ce cx ty (TypeBuiltin ann tb typ args) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0)` by
        (fs[expr_vv_sim_full_pre_def,expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def] >>
         first_assum ACCEPT_TAC) >>
      drule_all type_builtin_literal_vv_nil >> strip_tac >> gvs[] >>
      irule scoped_operand_pure >>
      fs[expr_vv_sim_full_hypotheses_def,create_operand_at_def] >>
      qexistsl_tac [`es`,`INL (Value v)`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
          [expr_vv_sim_full_post_def,expr_sim_full_endpoint_def])) >>
      qpat_assum `!sa. compile_expr ce ty _ sa = _` (qspec_then `sa` assume_tac) >>
      gvs[create_operand_vv_post_def,contextTheory.vv_location_def]) >>
  rw[expr_vv_sim_full_pre_def] >>
  qpat_assum `!sa. compile_expr ce ty _ sa = _` (qspec_then `sa` assume_tac) >>
  gvs[create_operand_cut_def] >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  metis_tac[create_operand_empty_scope]
QED

Theorem create_type_builtin_bound_vv_case:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  expr_body_pre ce cx env (TypeBuiltin ann tb typ args) es ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (TypeBuiltin ann tb typ args) es /\
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty (TypeBuiltin ann tb typ args) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (TypeBuiltin ann tb typ args)) (es,s0)
Proof
  strip_tac >> drule_all type_builtin_bound_literal >> strip_tac >>
  irule create_type_builtin_literal_vv_case >> metis_tac[]
QED
