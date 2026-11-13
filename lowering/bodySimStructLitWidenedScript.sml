(*
 * The body simulation of S1: a struct literal with an element whose value
 * the lowering lays out differently from its type, for bodySimExprCases'
 * body_structlit_case.
 *
 * HELD for the posts-interface wave: its proof needs expr_post/vv_post to
 * describe a widened internal call's value at its lowered type
 * (post_value_type), which base 18f70e04a does not have.  The proof on that
 * interface is harvested on bot/opus/seq-1012-{ifexp-arm,aggr-elem}; it
 * lands with the interface after the sixteen frozen branches merge.  Not
 * open work here.
 *
 * TOP-LEVEL:
 *   body_struct_lit_widened_call_elem — that case
 *)

Theory bodySimStructLitWidened
Ancestors
  exprSimSource exprSimStructLitBodyCounted
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* An aggregate literal with an element whose value the lowering lays out
   differently from the element's type: an internal call whose callee's
   return type the call's type widens.  As for body_ifexp_widened_call_arm,
   describing that value at its lowered type is the internal-call
   simulation's work (body_intcall_case). *)
Theorem body_struct_lit_widened_call_elem:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt strip_tac >>
  `!xs. body_exprs_ok cx xs ==> exprs_case F ctx func cenv cx xs` by
    (Induct >> rw[body_exprs_ok_def, exprs_case_def] >>
     gvs[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >>
     metis_tac[]) >>
  `exprs_case F ctx func cenv cx (MAP SND kes)` by metis_tac[] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  drule_all compile_struct_lit_body_case >>
  disch_then (qspecl_then [`v7`, `(src_id_opt,id)`] mp_tac) >>
  simp[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

