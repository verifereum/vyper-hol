(* Immutable literal-load resources at the joint target endpoint. *)
Theory augAssignFullLoadImmutableResources
Ancestors
  bodyImmutableAugAssignFacts bodyFullToplevelCtorSourceLayout
  bodyFullToplevelCtorSourceFrame bodyPtrDefs stateRelProj
  assignTuplePtrLoadStep exprSimHypsDefs stmtSimAugAssignPlace
  exprLoweringProps loweringPosts valueEncodingProps memoryValueEncoding
  ptrSafeRun ptrDiscipline contextCodegenRel codegenRel
  venomExecSemantics venomInstProofs venomInst venomState
  supportedDecls supportedTypes supportedExprTraverse
  vyperTypeEnv vyperTypeSystem vyperTypeCallGraph allocLimits
  vyperState compileEnv finite_map words pred_set list arithmetic

val load_steps = LIST_CONJ (List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``SLOAD``, ``TLOAD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs));

Theorem augassign_immutable_load_resources:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s)
  ==>
  ?off tv cur.
    src = cenv.ce_module /\ cenv.ce_is_ctor /\ ty = ity /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv cur /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es) /\
    mload off s = typed_val_to_w256 tv cur /\
    eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
    w2n ((n2w off):bytes32) = off /\
    op_taint tn (Lit (n2w off)) = {} /\
    off + 32 <= lo /\ off + 32 <= s.vs_alloca_next /\
    (!j. off <= j /\ j < off + 32 ==> j NOTIN tn.t_mem) /\
    (!iid out. ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst iid MLOAD [Lit (n2w off)] [out]) s)
Proof
  strip_tac >>
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >>
  `well_formed_type env.type_defs ty /\ ty <> NoneT` by
    (drule aug_place_typing >> strip_tac >>
     metis_tac[assignable_type_well_formed, assignable_type_not_NoneT]) >>
  `expr_body_pre cenv cx env (TopLevelName ty (cenv.ce_module,id)) es` by
    suspend "pre" >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  drule_all toplevel_ctor_source_layout >> strip_tac >>
  drule_all toplevel_ctor_source_frame >> strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  drule_all robust_typed_word_clean >> strip_tac >>
  qexistsl_tac [`off`, `tv`, `v`] >>
  suspend "finish"
QED

Resume augassign_immutable_load_resources[pre]:
  FAIL_TAC "synthetic expression precondition"
QED

Resume augassign_immutable_load_resources[finish]:
  FAIL_TAC "resources finish"
QED

Finalise augassign_immutable_load_resources
