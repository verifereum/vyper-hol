(* Scalar conversion boundaries for the body memory leaf. *)
Theory bodyMemTbConvertScalarBranch
Ancestors
  bodyMemTbConvertScalarDispatch bodyMemTbConvertIntegerDispatch
  bodyMemTbConvertCompose convertScalarBridge exprSimMemoryStack
  convertScalarTyping convertScalarDispatch convertScalarProps exprSimConvert
  exprSimHyps exprSimHypsDefs exprSimSource compileEnv
  vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness

Theorem scalar_word_dispatch_mem[local]:
  !ctx func cenv cx env es1 src t tv v.
    valid_conversion src t /\
    ~is_bytestring_type src /\ ~is_bytestring_type t /\
    evaluate_type (get_tenv cx) src = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op src t))
      (typed_val_to_w256 tv v) t (convert_result cx src t v) es1
Proof
  rpt strip_tac >>
  Cases_on `int_convert_pair src t`
  >- (`!name. t <> FlagT name` by gvs[int_convert_pair_def] >>
      Cases_on `t` >> gvs[] >> irule integer_typed_dispatch_mem >> simp[]) >>
  Cases_on `src = BaseT (BytesT (Fixed 0)) /\
    ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)`
  >- (gvs[] >> simp[] >> irule scalar_fixed_typed_dispatch_mem >> simp[]) >>
  irule scalar_typed_dispatch_mem >> simp[] >> metis_tac[]
QED

Theorem scalar_operand_typed_frag_mem[local]:
  !ctx func cenv cx env ann t e1 es v es1.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
    ~is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v,es1) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
      unop_frag_mem ctx func cenv cx
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
  irule scalar_word_dispatch_mem >> simp[] >> metis_tac[]
QED

Theorem scalar_convert_branch_sim_mem[local]:
  !ctx func cenv cx env ty ann t e1 es.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
    ~is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es ==>
    expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_scalar_convert >> strip_tac >>
  `is_word_type (expr_type e1) /\ is_word_type t` by
    (Cases_on `int_convert_pair (expr_type e1) t`
     >- gvs[int_convert_pair_def, is_word_type_def] >>
     drule_all scalar_conversion_word_types >> simp[]) >> gvs[] >>
  irule compile_convert_frag_sim_mem >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[]) >>
  qexists_tac `\x. compile_type_convert x
    (case ann of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
               | _ => mk_convert_op (expr_type e1) ann)` >>
  rpt conj_tac
  >~ [`lower_value _ _ _ _ _ = _`] >- metis_tac[lower_value_convert]
  >~ [`unop_frag_mem _ _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
      irule scalar_operand_typed_frag_mem >> simp[] >>
      qexists_tac `env` >>
      metis_tac[expr_body_pre_gas_obs]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `int_convert_pair (expr_type e1) ann`
  >- (`!name. ann <> FlagT name` by gvs[int_convert_pair_def] >>
      Cases_on `ann` >> gvs[] >>
      irule (INST_TYPE [``:'a`` |-> ``:operand``] straight_fresh_extends) >>
      goal_assum (drule_at Any) >> simp[straight_fresh_convert_pair]) >>
  drule_all scalar_dispatch_extends >> simp[]
QED

Theorem scalar_convert_branch_mem:
  !ctx func cenv cx env ty ann t e1 es.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
    ~is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es ==>
    expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es /\
    expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es` by
    (irule scalar_convert_branch_sim_mem >> metis_tac[]) >> simp[] >>
  drule expr_body_pre_scalar_convert >> strip_tac >> gvs[] >>
  `is_word_type ann` by
    (Cases_on `int_convert_pair (expr_type e1) ann`
     >- gvs[int_convert_pair_def, is_word_type_def] >>
     drule_all scalar_conversion_word_types >> simp[]) >>
  irule body_expr_vv_sim_mem_stack_word >>
  simp[vyperASTTheory.expr_type_def, compile_convert_stack] >>
  metis_tac[eval_expr_type_builtin_value]
QED
