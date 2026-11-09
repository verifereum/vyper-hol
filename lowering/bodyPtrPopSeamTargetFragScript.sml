(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): the pointer twin of S1's
 * pop_target_frag_of_sim (exprSimPopNestedBase), through
 * targetPlaceSimCases' target_place_sim: the base place's judgment gives
 * the place's, eval_target_place being eval_base_place then get_place.
 *
 * TOP-LEVEL:
 *   pop_target_frag_ptr_of_sim
 *)
Theory bodyPtrPopSeamTargetFrag
Ancestors
  bodyPtrPopTargetDefs bodyPtrDefs fragGasPathPtr targetPlaceSimCases
  vyperInterpreter vyperState bodyPtrPopTargetFragTransport

(* Hints, not part of the statement:
   - S1's proof is targetPlaceSimCases' target_place_sim: rewrite
     eval_target_place to bind (eval_base_place cx bt) get_place, take
     target_sim at vt = Type ty, and follow its counted path; get_place
     adds no Venom step, and gas_admissible's target_place_res_ok rules
     out an INL result that is not a PlaceR.
   - The counted-path combinators are fragGasPathPtr's and
     gasSummaryComposePtr's (gas_summary_ptr_at_def, gas_outcome_ptr_zero,
     gas_outcome_ptr_lo_def); the exempt branch is gasExemptCert's
     gas_exempt_cert_error_result, as in target_place_sim. *)
Theorem pop_target_frag_ptr_of_sim:
  !d ctx PG func cenv cx env bt es.
    target_sim_ptr d ctx PG func cenv cx env bt es ==>
    pop_target_frag_ptr d ctx PG func cenv cx env bt es
Proof
  rw[pop_target_frag_ptr_def, eval_target_place_as_bind] >>
  drule get_place_base_admissible >> strip_tac >>
  ho_match_mp_tac gas_outcome_ptr_get_place >> simp[] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[target_sim_ptr_def] >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sb`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  simp[]
QED
