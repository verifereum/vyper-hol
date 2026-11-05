Theory bodyIntCallJointInduction
Ancestors
  supportedExprs exprSimHypsDefs exprSimOperators exprSimSource exprSimHyps

(* The predicates quantify all entry/compiler/resource parameters themselves.
   Place fallback is same-expression recursion, not a smaller pure child. *)
Theorem joint_supported_induction:
  !Pe Pl Pf Pp.
  (!tops ty n. Pe tops (Name ty n)) /\
  (!tops ty l. Pe tops (Literal ty l)) /\
  (!tops ty id. supported_pure_expr tops (TopLevelName ty id) ==>
     Pe tops (TopLevelName ty id)) /\
  (!tops ty c a b. supported_pure_expr tops (IfExp ty c a b) /\
     Pe tops c /\ Pe tops a /\ Pe tops b ==> Pe tops (IfExp ty c a b)) /\
  (!tops ty id fs. supported_pure_expr tops (StructLit ty id fs) /\
     Pf tops fs ==> Pe tops (StructLit ty id fs)) /\
  (!tops ty b k. supported_pure_expr tops (Subscript ty b k) /\
     Pp tops b /\ Pe tops k ==> Pe tops (Subscript ty b k)) /\
  (!tops ty b f. supported_pure_expr tops (Attribute ty b f) /\
     Pp tops b ==> Pe tops (Attribute ty b f)) /\
  (!tops ty blt es. supported_pure_expr tops (Builtin ty blt es) /\
     Pl tops es ==> Pe tops (Builtin ty blt es)) /\
  (!tops ty blt t es. supported_pure_expr tops (TypeBuiltin ty blt t es) /\
     Pl tops es ==> Pe tops (TypeBuiltin ty blt t es)) /\
  (!tops. Pl tops []) /\
  (!tops e es. supported_pure_expr tops e /\ supported_pure_exprs tops es /\
     Pe tops e /\ Pl tops es ==> Pl tops (e::es)) /\
  (!tops. Pf tops []) /\
  (!tops n e fs. supported_pure_expr tops e /\ supported_pure_fields tops fs /\
     Pe tops e /\ Pf tops fs ==> Pf tops ((n,e)::fs)) /\
  (!tops ty n. supported_place_expr tops (Name ty n) ==> Pp tops (Name ty n)) /\
  (!tops ty id. supported_place_expr tops (TopLevelName ty id) ==>
     Pp tops (TopLevelName ty id)) /\
  (!tops ty b k. supported_place_expr tops (Subscript ty b k) /\
     Pp tops b /\ Pe tops k ==> Pp tops (Subscript ty b k)) /\
  (!tops ty b f. supported_place_expr tops (Attribute ty b f) /\
     Pp tops b ==> Pp tops (Attribute ty b f)) /\
  (!tops e. supported_pure_expr tops e /\ Pe tops e ==> Pp tops e) ==>
  (!tops e. supported_pure_expr tops e ==> Pe tops e) /\
  (!tops es. supported_pure_exprs tops es ==> Pl tops es) /\
  (!tops fs. supported_pure_fields tops fs ==> Pf tops fs) /\
  (!tops e. supported_place_expr tops e ==> Pp tops e)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def] >> rpt strip_tac >> metis_tac[]
QED

(* The recursive producer can be invoked at any invariant intermediate
   state, not merely at the source state of the parent expression. *)
Theorem joint_builtin_child_entry:
  expr_sim_pre ce cx env (Builtin ty blt args) es /\
  supported_pure_expr (cx_tops cx) (Builtin ty blt args) /\
  MEM e args /\ expr_sim_inv ce cx env ee ==>
  expr_sim_pre ce cx env e ee /\ supported_pure_expr (cx_tops cx) e /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok ee
Proof
  strip_tac >>
  `expr_sim_pre ce cx env e ee` by
    (drule_all expr_sim_pre_builtin_arg >> simp[]) >>
  `supported_pure_expr (cx_tops cx) e` by
    (gvs[supported_pure_expr_def, supported_pure_exprs_every] >>
     metis_tac[listTheory.EVERY_MEM]) >>
  simp[] >> metis_tac[expr_body_pre_vv_gas_admissible, expr_sim_pre_body_pre]
QED

Theorem joint_ifexp_child_entries:
  expr_sim_pre ce cx env (IfExp ty c a b) es /\
  supported_pure_expr (cx_tops cx) (IfExp ty c a b) /\
  expr_sim_inv ce cx env ee ==>
  (expr_sim_pre ce cx env c es /\
   supported_pure_expr (cx_tops cx) c /\
   gas_admissible (eval_expr cx c) expr_vv_res_ok es) /\
  (!e. (e = a \/ e = b) ==>
    expr_sim_pre ce cx env e ee /\ supported_pure_expr (cx_tops cx) e /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ee)
Proof
  strip_tac >> drule expr_sim_pre_ifexp >> strip_tac >>
  gvs[supported_pure_expr_def] >>
  metis_tac[expr_body_pre_vv_gas_admissible, expr_sim_pre_body_pre]
QED

(* INTERFACE CHECKPOINT -- obligations deliberately NOT asserted here.

   MakeArray:
   exprLowering's compile_builtin_dispatch allocates before calling
   compile_make_tuple/compile_make_array. compile_make_tuple calls
   cfn ce (expr_type e) e, then unwrap_value/store, then recurses on es.
   joint_builtin_child_entry supplies the child pre/support/admissibility
   at any ee satisfying expr_sim_inv. Thus no additional child typing
   premise is needed for MakeArray. The source evaluates eval_exprs,
   not eval_expr_results followed by read_results. The remaining counted
   join must compose each eval_expr with its read_result and tail, while
   preserving the parent buffer and hs on the SAME witness.

   IfExp:
   joint_ifexp_child_entries supplies the raw condition and both potential
   selected-arm entries, universally in the intermediate invariant ee.
   compile_expr lowers the condition at BoolT, compiles arms at the caller's
   requested ty (not necessarily expr_type arm), then compile_ifexp_arm.
   Source: bind (eval_expr cx c) (\tv.
     bind (switch_BoolV cx tv (eval_expr cx a) (eval_expr cx b))
          (conditional_result cx)).
   Needed: a counted source-bind/selected-arm rule for this computation,
   transporting the raw child's ordinary resource post AND exemption branch.
   gas_summary_bind is exported, but states gas_summary, not gas_outcome
   or gas_summary_at; it does not itself transport gas_exempt_cert.
   joint_audit_induction is conditional on real family implementations;
   it does not supply this join or compile_ifexp_arm's memory copy frame.
   compile_ifexp_arm_unwrap and ifexp_emit_mcopy_run are local to
   exprSimIfExp and must NOT be copied.

   Nested Subscript:
   supported_pure_expr tops (Subscript ty b k) gives supported_place_expr
   tops b and supported_pure_expr tops k, not supported_pure_expr tops b.
   Actual compiler callback is cfn ce ty b, with parent requested ty;
   for MapPT it lowers k at expr_type k, for general ValPT at ty, while
   tuple/struct literal indices have no compiler callback. Source still
   evaluates b, then k, then read_result k, then select_result.
   Missing interface (not claimed as a true implication):
     expr_sim_pre ce cx env (Subscript ty b k) es /\
     supported_pure_expr (cx_tops cx) (Subscript ty b k)
       ==> an appropriate PLACE producer precondition for b at es,
   followed by key expr_sim_pre at its actual invariant endpoint.
   A mapping base may be typed by type_place_expr and return HashMapRef;
   expr_sim_pre requires well_typed_expr and expr_vv_res_ok excludes this
   result. Hence simply instantiating Pe on b is not a valid solution.
   Pp needs a distinct typed result/admissibility/value relation interface.
   The local tuple_pre_base in exprSimTuple covers only TupleT, is not an
   export, and has not been copied. Source gas admissibility of the outer
   expression alone does NOT establish raw base expr_vv_res_ok.

   No public producer premise, protected definition or shared theorem was
   changed to hide these gaps. This is a bounded interface audit, not the
   universal resource producer or the internal-call proof.
*)
