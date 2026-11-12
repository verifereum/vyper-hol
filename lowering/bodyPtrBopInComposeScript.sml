Theory bodyPtrBopInCompose
Ancestors bodyPtrBopInWordBoundary wordArgsPtr bodyPtrDefs bodyPtrPreds
  exprSimOperands exprSimWordArgs gasSummaryComposePtr gasSummary
  vyperInterpreter vyperState compileEnv finite_map loweringPosts exprBopSimProps

(* This is the old operand's interface after the next lower_value has run.
   Its semantic relation and ghost facts are kept together for consumers. *)
Theorem membership_word_operand_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post ctx func cenv cx e2 es1 s1 s2 t es2 v2 y u /\
  ptr_val_ok cx (expr_type e1) v1 x G1 tn1 t /\
  is_word_type (expr_type e1) /\
  ghost_kept cenv es1 s1 G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  (?w. eval_operand x t = SOME w /\ eval_operand x u = SOME w) /\
  ptr_val_ok cx (expr_type e1) v1 x G2 tn2 u
Proof
  strip_tac >> conj_tac >- (drule_all expr_post_operand_word >> simp[]) >>
  drule_all membership_word_result_kept >> simp[ptr_val_ok_def]
QED

(* A successful marked head supplies exactly the conditional tail judgment
   and scope-domain stability needed by the recursive operand consumer. *)
Theorem membership_marked_head_tail:
  body_exprs_ptr_ok cx (e::args) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    marks (INL v) mid G tn r ==>
  body_exprs_ptr_ok cx args /\ MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  conj_tac
  >- (irule body_exprs_ptr_ok_tail >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
    forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem membership_vv_word_operand_kept:
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv u /\
  ptr_val_ok cx t v op G0 tn0 s0 /\ is_word_type t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op u = SOME w /\ ptr_val_ok cx t v op G tn u
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      gvs[vv_post_def] >> metis_tac[]) >>
  drule_all membership_word_result_kept >> simp[ptr_val_ok_def]
QED

(* A second operand may denote an array place.  Retain its entire caller
   post P (including location coverage and cursor) while framing the needle. *)
Theorem membership_vv_outcome_word_kept:
  ptr_val_ok cx wt v op G0 tn0 s0 /\ is_word_type wt /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w /\
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn u. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s0 ee tv vv u /\
       ghost_kept cenv es sa G0 tn0 s0 G tn /\ P res ee G tn u) R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn u. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s0 ee tv vv u /\
       ghost_kept cenv es sa G0 tn0 s0 G tn /\ P res ee G tn u /\
       eval_operand op u = SOME w /\ ptr_val_ok cx wt v op G tn u) R
Proof
  strip_tac >> irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_all membership_vv_word_operand_kept >> simp[]) >>
  simp[]
QED
