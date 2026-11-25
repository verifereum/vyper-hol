(* Linked Attribute cuts, retaining the real and shadow boundaries. *)
Theory bodyFullAttributeMods
Ancestors
  exprSimAttribute exprSimUnwrap fragExec bodyFullShared
  gasShadowCompile gasShadowState gasShadow vyperStorageTrace
  bodyFullPostsMods exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeExprSoundness gasContext exprSimDefs bodyPtrAttributeSource
  vyperInterpreter vyperState context bodyWriteSubscriptSourceMods
Libs monadsyntax

Theorem attribute_paired_cut_mods:
  compile_expr cenv ty (Attribute ann obj fld) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Attribute ann obj fld))
    sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?bvv sm shm p.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    emit_op ADD [vv_operand bvv;
      Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))] sm = (p,sb) /\
    vv = LocatedValue ann (mk_ptr p (vv_loc bvv)) /\
    gas_shadow_state sm shm /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (Attribute _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_attribute) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_attribute o SRULE [gas_shadow_expr_def]) >>
  `gas_shadow_compiles (compile_expr cenv ty obj)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
      Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_assum `compile_expr cenv ty obj sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `emit_op ADD _ _ = (_,shb)` (assume_tac o MATCH_MP attr_extends) >>
  qpat_assum `emit_op ADD _ _ = (_,sb)` (assume_tac o MATCH_MP attr_extends) >>
  `fn_has_code sa st1 func /\ fn_has_code st1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha st1' shadow_func /\ fn_has_code st1' shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_x_assum `bvv' = bvv` SUBST_ALL_TAC >>
  qpat_x_assum `vv = LocatedValue ann (mk_ptr p' _)` kall_tac >>
  qexistsl_tac [`bvv`,`st1`,`st1'`,`p`] >> asm_rewrite_tac[]
QED

(* Attribute cannot introduce a successful map result at its struct base.
   A failed base propagates the very same exception through the selection. *)
Theorem attribute_operand_admissible_mods:
  expr_body_pre_mods mods cenv cx env obj es /\
  gas_admissible (eval_expr cx (Attribute ann obj fld)) expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res`
  >- (rename1 `eval_expr cx obj _ = (INL raw,ee)` >>
      `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs)` by simp[] >>
      drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
      qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`es with gas_obs := gs`,`INL raw`,`ee`] mp_tac) >>
      Cases_on `raw` >> fs[runtime_consistent_def,
        expr_vv_res_ok_def,vyperTypeInvariantsTheory.eval_result_typed_def]) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[attr_source, bind_def]
QED

Theorem attribute_vv_holds_read_operand_mods:
  vv_holds_mods cenv cx ty tv vv ee t ==>
  ?v w. read_result cx tv ee = (INL v,ee) /\
        eval_operand (vv_operand vv) t = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def,vv_operand_def]
  >- (strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >> rpt strip_tac >>
      drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]
QED
