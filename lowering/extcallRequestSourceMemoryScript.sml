(* Operand facts from the frozen external-call body precondition. *)
Theory extcallRequestSourceMemory
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprSimDefs
  supportedExprTraverse allocLimits allocLimitsProps
  tuplePlaceZero typedCopyCompatibility
  vyperTypeSystem vyperTypeArgFits vyperTypeCallGraph vyperTypeInvariants
  exprLowering loweringPosts vyperAST vyperState compileEnv list rich_list

Theorem extcall_source_shape:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt) es ==>
  ?addr rest. args = addr::rest /\ ann = rt /\ dflt = NONE /\
    expr_type addr = BaseT AddressT /\
    LENGTH rest = LENGTH ats + LENGTH opts /\ ext_call_opts_ok stat opts /\
    EVERY (assignable_type env.type_defs) ats /\
    arg_types_fit (MAP expr_type (TAKE (LENGTH ats) rest)) ats /\
    MAP expr_type (DROP (LENGTH ats) rest) = MAP (ext_call_kw_type rt) opts /\
    EVERY (\e. ~expr_has_effect e) rest
Proof
  strip_tac >>
  `~supported_expr_exists call_operands_effect_root
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt)` by
    fs[expr_body_pre_def] >>
  `EVERY (\e. ~expr_has_effect e) (DROP 1 args)` by
    (drule_all call_operands_effect_extcall_tail >> simp[]) >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def,Once well_typed_expr_def] >> strip_tac >>
  Cases_on `args` >> gvs[]
QED

Theorem extcall_operand_body_pre:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip sig opts) args dflt) es /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  expr_body_pre ce cx env e ee
Proof
  PairCases_on `sig` >>
  rw[expr_body_pre_def,well_typed_expr_def,int_calls_expr_def,
     byte_widths_expr_def,alloc_limits_expr_def,
     supported_expr_exists_def,supported_exprs_exists_every,EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[expr_has_evm_run_thm,EXISTS_MEM,int_calls_expr_def,
      supported_expr_exists_def]
  >~ [`well_typed_expr _ _`] >-
    (irule exprSimSourceTheory.well_typed_exprs_member >>
     qexists_tac `args` >> simp[]) >>
  metis_tac[well_typed_exprs_member,byte_widths_exprs_mem,
            alloc_limits_exprs_mem,call_evaluation_safe_exprs_mem]
QED

Theorem extcall_positional_layout_positive:
  expr_body_pre ce cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::rest) dflt) es /\
  i < LENGTH ats /\
  evaluate_type (get_tenv cx) (lowered_value_type ce (EL i rest)) = SOME tv ==>
  0 < type_memory_size tv
Proof
  strip_tac >> drule extcall_source_shape >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `LENGTH ats <= LENGTH rest /\ i < LENGTH rest` by decide_tac >>
  `MEM (EL i rest) (addr::rest)` by simp[EL_MEM] >>
  `expr_body_pre ce cx env (EL i rest) es` by
    metis_tac[extcall_operand_body_pre] >>
  `arg_type_fits (lowered_value_type ce (EL i rest)) (expr_type (EL i rest))` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `assignable_type (get_tenv cx) (EL i ats) /\
   arg_type_fits (expr_type (EL i rest)) (EL i ats)` by
    (fs[arg_types_fit_LIST_REL,LIST_REL_EL_EQN,EVERY_EL,EL_MAP,EL_TAKE] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`dty` |-> `EL i ats`,
                  `sty` |-> `lowered_value_type ce (EL i rest)`,
                  `stv` |-> `tv`,
                  `tenv` |-> `get_tenv cx`]
    (SPEC_ALL tuple_place_assignable_source_positive)) >>
  (impl_tac >- (simp[] >> metis_tac[arg_type_fits_trans])) >> simp[]
QED
