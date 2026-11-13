(* The attribute read over the finite-horizon joint judgments: the base's
   value judgment, then one ADD of the field offset, with the source GAS
   marks, memory posts and pointer ghosts on one witness at (DF H, lo).
   The value judgment comes from the vv one by bodyFullOfVV.
 *
 * TOP-LEVEL:
 *   attribute_vv_sim_full -- the vv judgment of e.fld from that of e
 *   attribute_expr_full_ok -- body_expr_full_ok of e.fld from that of e
 *)
Theory bodyFullAttribute
Ancestors
  bodyFullAttributeAdd bodyFullAttributeFields bodyPtrAttributeSelection
  bodyAttributeMemory gasOutcomeFullCompose exprSimHyps exprLoweringProps
  bodyFullOfVV bodyFullPreds bodySimFull exprSimAttribute exprSimHypsDefs gasShadow
  gasShadowState gasShadowCompile emitHelperProps fragExec exprSimUnwrap
  loweringPosts compileEnv valueEncoding vyperTyping
  vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

Theorem attribute_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >> drule attr_pre_base >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (drule_all attr_post_value_type >> simp[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  cheat
QED

(* Unverified continuation sketch from the first alan run (its shadow
   step leaves 2 goals on the ported gasShadowCompile):
  `?shadow_sm. compile_expr cenv ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (cj 1 gas_shadow_compile_expr |> Q.SPECL [`cenv`, `ty`, `obj`, `T`]) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >>
     simp[] >> strip_tac >>
     Cases_on `compile_expr cenv ty (gas_shadow_expr obj) shadow_sa` >> gvs[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (drule compile_expr_extends >> strip_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Attribute _ _ _)) _ = _`
       mp_tac >> simp[gas_shadow_expr_def] >>
     disch_then (strip_assume_tac o MATCH_MP compile_expr_attribute) >>
     gvs[] >> drule attr_extends >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
*)

Theorem attribute_expr_full_ok:
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  cheat
QED
