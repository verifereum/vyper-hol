(* Source-layout-equality preparation for the joint aggregate declaration. *)
Theory bodyFullAnnAssignOther
Ancestors
  bodySimFull bodyFullPreds bodyFullAllocaFresh bodyFullUnwrap
  annassignRelayoutSource memoryLocalRhsProps exprSimHyps exprSimHypsDefs
  stmtSimDeclTypedCode stmtSimDeclSourceSeparation externalNormalizePremises
  exprOperandVar bodyPtrDefs exprSimMemDefs loweringPosts
  vyperTypeValues vyperTypeInvariants vyperTypeExprSoundness valueTypingMemoryProps
  compileEnv exprLowering stmtLowering vyperInterpreter vyperState
  vyperValue vyperAST finite_map list
Libs monadsyntax

Theorem annassign_other_typed_layout:
  expr_body_pre ce cx env e es /\ env.type_defs = get_tenv cx /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  ~is_word_type typ /\ ~is_bytestring_type typ /\ expr_type e <> typ /\
  lowered_value_type ce e = expr_type e /\
  type_memory_bytes ce typ < 2 ** 64 ==>
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  post_value_type ce e = expr_type e /\
  type_memory_bytes ce (expr_type e) = type_memory_size stv /\
  type_memory_bytes ce typ = type_memory_size dtv /\
  0 < type_memory_size stv /\
  type_memory_size stv <= type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[normalize_return_source_kinds] >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  `type_widens_to (get_tenv cx) (expr_type e) typ` by metis_tac[] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  simp[post_value_type_lowered] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `value_runtime_typed env (expr_type e) v /\ value_runtime_typed env typ v` by
    metis_tac[memory_rhs_read_annotation_typed, memory_rhs_read_destination_typed] >>
  `value_has_type stv v /\ value_has_type dtv v` by
    gvs[value_runtime_typed_def] >>
  simp[value_has_type_memory_wf] >>
  metis_tac[normalize_nonbytes_footprint]
QED
