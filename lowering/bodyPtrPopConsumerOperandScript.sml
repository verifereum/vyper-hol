Theory bodyPtrPopConsumerOperand
Ancestors
  bodyPtrPopRootCase bodyPtrPopConsumerCut bodyPtrSubscript
  exprSimPtrLiteral bodyPtrPreds exprSimSource exprSimDefs exprSimHyps exprSimHypsDefs
  vyperTypeCallGraph vyperAST

Theorem pop_literal_body_ptr[local]:
  !cx ann l. body_expr_ptr_ok cx (Literal ann l)
Proof
  rw[body_expr_ptr_ok_def] >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    fs[expr_sim_pre_body, int_calls_expr_def] >>
  metis_tac[literal_expr_sim_ptr]
QED

(* The reference ConsumerCut operand now has an independent universal
   producer, not an assumption of this Pop task's target theorem. *)
Theorem pop_reference_index_ptr:
  !cx a0 a1 a2 it nid.
    body_expr_ptr_ok cx
      (Subscript a2
        (Subscript a1 (Pop a0 (TopLevelNameTarget nid)) (Literal it (IntL 0)))
        (Literal it (IntL 0)))
Proof
  rpt gen_tac >> irule subscript_expr_ptr_ok >>
  simp[pop_literal_body_ptr] >>
  irule subscript_expr_ptr_ok >>
  simp[pop_literal_body_ptr, body_pop_root_ptr_ok]
QED

(* This discharges only the index-body-judgment row of ConsumerCut's
   normal-cut ledger.  It does not discharge body_inv, expr_body_pre,
   fn_has_code or the outer Pop compiler equation.  At the cut, the exact
   remaining interface is still raw header agreement plus a local
   pop_region_taint_ok observer at the SAVED slot after index execution
   (ConsumerCut lines 66-76).  Neither the universal root producer nor the
   subscript producer exports preservation of an arbitrary saved region.
   ghost_kept protects old variable provenance/taint and memory, not raw
   storage headers.  The source-support exclusion therefore still cannot
   be promoted to compiled-containment exclusion. *)
