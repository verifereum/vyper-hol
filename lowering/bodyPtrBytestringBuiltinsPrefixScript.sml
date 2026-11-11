Theory bodyPtrBytestringBuiltinsPrefix
Ancestors
  exprSimWordArgs exprLoweringProps loweringPosts wordArgsPtr
  exprSimCalldataSlice fragGasPathPtr vyperInterpreter
Libs monadsyntax

(* The source execution premise is essential: expr_post contains only
   target-side representation and frame facts, not source scope domains. *)
Theorem operand_prefix_transport_inputs:
  lower_value compile_expr cenv cty e sa = (x,sm) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v x t /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,ee) ==>
  wb_frame cenv es ee sa s0 t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  drule expr_post_frame >> strip_tac >>
  drule forced_eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem operand_prefix_frame_inputs:
  lower_value compile_expr cenv cty e sa = (x,sm) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v x t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  wb_frame cenv es ee sa s0 t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  drule expr_post_frame >> simp[]
QED

Theorem forced_operand_outcome_scopes:
  gas_outcome_ptr D tops (ctx,func) PG
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) P E ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn t. P res ee G tn t /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes) E
Proof
  rw[gas_outcome_ptr_def] >> qexists_tac `marks`
  >- (disj1_tac >>
  fs[gas_summary_ptr_at_def] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     drule (PURE_REWRITE_RULE [ETA_THM]
       forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED
