Theory convertScalarBridge
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  convertScalarDispatch convertScalarSim convertScalarTyping
  exprSimHypsDefs exprSimSource exprSimHyps exprLowering compileEnv vyperAST vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness

Theorem scalar_operand_typed_frag:
  !ctx func cenv cx env ann t e1 es v es1.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
    ~is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    ~int_convert_pair (expr_type e1) t /\
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v,es1) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
      unop_frag ctx func cenv cx
        (\x. compile_type_convert x
          (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                   | _ => mk_convert_op (expr_type e1) t))
        (typed_val_to_w256 tv v) ann (convert_result cx (expr_type e1) t v) es1
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_scalar_convert >> strip_tac >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  irule scalar_typed_dispatch >> simp[] >> metis_tac[]
QED
