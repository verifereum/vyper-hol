(* Only the ordinary Slice branch directly evaluates all three expressions. *)
Theory bodySliceOrdinaryOperandPreMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimSliceSource exprSimHypsDefs
  supportedExprTraverse allocLimits exprLowering exprSimSource
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperContext vyperInterpreter vyperAST list

Triviality slice_ordinary_child_pre:
  ~is_extcode src /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) [src;start;len]) es /\
  MEM e [src;start;len] /\ expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  strip_tac >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def, EVERY_APPEND,
       supported_expr_exists_def, expr_has_evm_run_thm,
       DISJ_IMP_THM, FORALL_AND_THM] >>
  strip_tac >>
  qpat_x_assum `MEM e _` strip_assume_tac >> gvs[] >>
  (conj_tac
   >- (irule well_typed_exprs_member >> goal_assum (drule_at Any) >> simp[])) >>
  qpat_x_assum `call_evaluation_safe cx _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

Theorem slice_ordinary_operands_pre_mods:
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
    case code_slice_source (Slice n) args of
      NONE => body_exprs_full_ok_mods mods exps cx args
    | SOME (code_ty,addr) =>
        body_exprs_full_ok_mods mods exps cx (TL args) /\
        (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
          body_exprs_full_ok_mods mods exps cx [addr])) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es /\
  code_slice_source (Slice n) args = NONE ==>
  ?src start len. args = [src;start;len] /\
    expr_type start = BaseT (UintT 256) /\
    expr_type len = BaseT (UintT 256) /\
    slice_operands_ok (Slice n) [src;start;len] /\
    ((ann = BaseT (BytesT (Dynamic n)) /\ ?bd. expr_type src = BaseT (BytesT bd)) \/
     (ann = BaseT (StringT n) /\ ?m. expr_type src = BaseT (StringT m))) /\
    ~is_extcode src /\ ~is_self_code src /\
    body_exprs_full_ok_mods mods exps cx args /\
    (!e mid. MEM e args /\ expr_sim_inv_mods mods cenv cx env mid ==>
      expr_body_pre_mods mods cenv cx env e mid)
Proof
  strip_tac >>
  drule_then (strip_assume_tac o MATCH_MP slice_typed_args)
    expr_body_pre_mods_well_typed >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  `~is_extcode src` by
    (qpat_assum `code_slice_source (Slice n) [src;start;len] = NONE` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_extcode_ind >> simp[is_extcode_def]) >>
  `~is_self_code src` by
    (qpat_assum `~is_extcode src` mp_tac >>
     qid_spec_tac `src` >> ho_match_mp_tac is_self_code_ind >>
     simp[is_self_code_def,is_extcode_def]) >>
  `body_exprs_full_ok_mods mods exps cx [src;start;len]` by
    fs[builtin_args_length_ok_def] >>
  `!e mid. MEM e [src;start;len] /\ expr_sim_inv_mods mods cenv cx env mid ==>
    expr_body_pre_mods mods cenv cx env e mid` by
    (rpt gen_tac >> disch_tac >> irule slice_ordinary_child_pre >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` (irule_at Any) >>
     strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`src`,`start`,`len`] >> simp[]
QED
