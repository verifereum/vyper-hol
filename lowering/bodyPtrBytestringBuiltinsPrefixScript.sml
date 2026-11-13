Theory bodyPtrBytestringBuiltinsPrefix
Ancestors
  exprSimWordArgs exprLoweringProps loweringPosts wordArgsPtr
  exprSimCalldataSlice fragGasPathPtr gasOutcomeMarkedPtr gasSummaryComposePtr vyperInterpreter
Libs monadsyntax

(* The source execution premise is essential: expr_post contains only
   target-side representation and frame facts, not source scope domains. *)
Theorem operand_prefix_transport_inputs:
  lower_value compile_expr cenv cty e sa = (x,sm) /\
  expr_post H ctx func cenv cx e es sa sm s0 ee v x t /\
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
  expr_post H ctx func cenv cx e es sa sm s0 ee v x t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  wb_frame cenv es ee sa s0 t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  drule expr_post_frame >> simp[]
QED

Theorem forced_operand_outcome_scopes:
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) P E ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. P H res ee G tn t /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes) E
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  qexists_tac `P` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> simp[] >>
  fs[gas_marked_exec_ptr_def] >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule (PURE_REWRITE_RULE [ETA_THM]
    forced_eval_expr_preserves_scopes_dom) >> simp[]
QED
