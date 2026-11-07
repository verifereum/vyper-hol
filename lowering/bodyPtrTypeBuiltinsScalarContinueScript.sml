(* Shared word-source Convert continuation interfaces. *)
Theory bodyPtrTypeBuiltinsScalarContinue
Ancestors bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsUintContinue
  exprSimConvert exprSimHyps exprSimDefs exprSimProps exprSimWordArgs
  exprLowering exprLoweringProps compileEnv loweringPosts bodyPtrDefs
  fragGasPathPtr ptrDiscipline vyperAST vyperValue valueEncoding venomState

Theorem scalar_identity_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~is_bytestring_type (expr_type e) /\
  (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
   | _ => mk_convert_op (expr_type e) typ) = ConvIdentity /\
  compile_type_convert x ConvIdentity s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  sa.cs_next_var <= s1.cs_next_var /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) typ v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx typ v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  drule_all scalar_source_body_word_types >> strip_tac >>
  `?tout. evaluate_type (get_tenv cx) typ = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  drule_all scalar_identity_semantic_packet >> strip_tac >>
  qpat_x_assum `ann = typ` SUBST_ALL_TAC >>
  gvs[compile_type_convert_def, comp_return_def] >>
  `eval_operand op t0 = SOME (typed_val_to_w256 tout v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `expr_post ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa s1 s0 (ee with gas_obs := []) v op t0` by
    (irule scalar_suffix_expr_post >> simp[expr_type_def] >>
     conj_tac >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`op`] >>
     simp[] >> fs[expr_post_def]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`,`ee`,`G`,`tn`,`OK t0`] >>
  fs[ptr_val_ok_def] >> simp[gas_path_ptr_rules]
QED
