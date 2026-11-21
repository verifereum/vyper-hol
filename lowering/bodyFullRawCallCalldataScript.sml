(*
 * raw_call with calldata over the finite-horizon joint judgment.
 * Its lowering emits a DALLOCA into the function.
 *
 * TOP-LEVEL:
 *   raw_call_calldata_expr_full_ok -- the raw_call-with-calldata case
 *)
Theory bodyFullRawCallCalldata
Ancestors
  bodyFullPreds bodySimFull rawCallCalldataDalloca exprSimHypsDefs fragExec
  ptrDiscipline exprLowering vyperTypeSystem vyperAST list

val _ = Parse.hide "body";

(* Its proof before it was admitted, kept as the repo asks. That proof derived a
   contradiction from the gate's no-DALLOCA invariant (body_inv_no_dalloca),
   which the widened gate no longer gives:

       rw[body_expr_full_ok_def] >>
       drule body_inv_no_dalloca >> strip_tac >>
       `es <> []` by (strip_tac >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
       rw[expr_sim_full_def, expr_vv_sim_full_def] >>
       `EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)`
         suffices_by (strip_tac >> gvs[ctx_has_dalloca_def, EXISTS_MEM] >>
                      metis_tac[])
       >- (qpat_assum `lower_value _ _ _ (Call _ _ _ _) sa = _`
             (strip_assume_tac o MATCH_MP lower_value_compile_expr_split) >>
           `fn_has_code sa sm func` by
             (qspecl_then [`sa`, `sm`, `sb`, `func`] mp_tac fn_has_code_split >>
              fs[]) >>
           drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
       drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
*)
(* GATE_ADMISSION: missing case, raw_call with msg.data body simulation; owner: dalloca sweep *)
Theorem raw_call_calldata_expr_full_ok:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED
