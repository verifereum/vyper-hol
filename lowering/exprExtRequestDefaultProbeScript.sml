(* Runtime typing at the actual effect-free default expression. *)
Theory exprExtRequestDefaultProbe
Ancestors
  exprExtRequestTyping memoryLocalRhsProps valueTypingMemoryProps
  valueCopyBytes exprSimHypsDefs exprSimHyps allocLimits exprLowering vyperAST
  compileEnv valueCopy loweringPosts exprLoweringProps

Theorem extrequest_default_runtime_types:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  type_widens_to env.type_defs (expr_type e) ret /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL d, ee) ==>
  ?dtv rtv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv /\
    value_has_type dtv d /\ val_wf dtv d /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size dtv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    value_has_type rtv d /\ val_wf rtv d
Proof
  strip_tac >>
  `!a f args df. e = Call a (IntCall f) args df ==>
      lowered_value_type cenv e = expr_type e` by
    metis_tac[extrequest_effect_free_not_call] >>
  drule_all memory_rhs_read_lowered_typed_unwidened >> strip_tac >>
  drule_all memory_rhs_read_destination_typed >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  dxrule_all memory_rhs_runtime_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  metis_tac[value_has_type_memory_wf]
QED

(* No arbitrary bytes-bound subtyping is used: the actual expression
   supplies typing at the lowered bound, then the existing layout transfer
   changes only the bound of a bytes/string representation. *)
Theorem extrequest_default_lowered_memory:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL d, ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_in_memory tv d off mem ==>
  ?dtv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv /\
    value_has_type dtv d /\ val_wf dtv d /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size dtv /\
    val_in_memory dtv d off mem
Proof
  strip_tac >>
  `!a f args df. e = Call a (IntCall f) args df ==>
      lowered_value_type cenv e = expr_type e` by
    metis_tac[extrequest_effect_free_not_call] >>
  drule_all memory_rhs_read_lowered_typed_unwidened >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  `well_typed_expr env e` by gvs[expr_body_pre_def] >>
  drule_all extrequest_lowered_type_compatible >>
  disch_then (qspec_then `cenv` strip_assume_tac)
  >- (gvs[] >> metis_tac[value_has_type_memory_wf]) >>
  qexists_tac `tv'` >> simp[value_has_type_memory_wf] >>
  irule bytestring_val_in_memory_transfer >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem extrequest_default_lowered_alloc_bound:
  !cenv e. alloc_limits_expr cenv e /\ ~expr_has_effect e /\
    ~is_word_type (lowered_value_type cenv e) ==>
    type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >>
  gvs[lowered_value_type_def, expr_type_def, alloc_limits_expr_def,
      type_alloc_ok_def]
  >- (Cases_on `t` >> Cases_on `l` >>
      gvs[lowered_value_type_def, expr_type_def, alloc_limits_expr_def,
          type_alloc_ok_def, literal_alloc_ok_def] >>
      Cases_on `b` >>
      gvs[lowered_value_type_def, expr_type_def, type_memory_bytes_def,
          is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
           gvs[lowered_value_type_def, expr_type_def, type_memory_bytes_def,
               is_word_type_def]) >>
      gvs[vfmConstantsTheory.word_size_def])
  >- (rename1 `Builtin rt bi es` >> Cases_on `bi` >>
      gvs[lowered_value_type_def, expr_type_def] >>
      gvs[concat_buffer_type_def, AllCaseEqs(), type_memory_bytes_def,
        concat_alloc_size_def, vfmConstantsTheory.word_size_def,
        listTheory.MAP_MAP_o] >>
      Cases_on `rt` >> gvs[type_memory_bytes_def,
        vfmConstantsTheory.word_size_def] >>
      Cases_on `b` >> gvs[type_memory_bytes_def,
        vfmConstantsTheory.word_size_def])
  >- (rename1 `TypeBuiltin rt tb at es` >> Cases_on `tb` >>
      gvs[lowered_value_type_def, expr_type_def, alloc_limits_expr_def,
          type_alloc_ok_def] >> Cases_on `o'` >>
      gvs[type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  metis_tac[extrequest_effect_free_not_call]
QED

Theorem extrequest_default_copy_capacity:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~is_word_type (lowered_value_type cenv e) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv ==>
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >>
  `alloc_limits_expr cenv e` by gvs[expr_body_pre_def] >>
  drule_all extrequest_default_lowered_alloc_bound >>
  simp[wordsTheory.dimword_def] >> decide_tac
QED

(* The store consumes the unwrap result at the annotation type, not an
   assumed representation at the lowered type. Compiler-only execution
   supplies the code/evaluation/freshness premises at this boundary. *)
Theorem extrequest_default_store_consumer:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type cenv e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL d, ee) /\
  expr_val_rel cx (expr_type e) d src s /\
  compile_store_memory cenv src dst (lowered_value_type cenv e)
    (lowered_value_type cenv e) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw ==>
  ?tv t. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    value_has_type tv d /\ val_wf tv d /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    val_in_memory tv d (w2n dw) t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all memory_rhs_read_annotation_typed >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `val_in_memory tv d (w2n w) s.vs_memory` by metis_tac[] >>
  drule_all extrequest_default_lowered_memory >> strip_tac >>
  drule_all extrequest_default_copy_capacity >> strip_tac >>
  `(if is_word_type (lowered_value_type cenv e)
    then w = typed_val_to_w256 dtv d
    else val_in_memory dtv d (w2n w) s.vs_memory)` by simp[] >>
  drule_all compile_store_memory_run_size_bound_with_capacity >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  gvs[venomStateTheory.venom_state_component_equality]
QED
