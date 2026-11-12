(* Raw gas accounting for arithmetic and control instructions. *)
Theory asmNonCallCheapGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmOperation

Theorem step_inst_fixed_arithmetic_gas_budget:
  MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; AddMod; MulMod;
          SignExtend; LT; GT; SLT; SGT; Eq; IsZero; And; Or; XOr;
          Not; Byte; ShL; ShR; SAR; CLZ] /\
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  8 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_inst op es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  simp[listTheory.MEM] >> strip_tac >> gvs[step_inst_def]
  >>~- ([`step_monop _ _ es = (r,s')`],
        drule step_monop_gas_budget >>
        disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac)
  >>~- ([`step_modop _ _ es = (r,s')`],
        drule step_modop_gas_budget >>
        disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac) >>
  drule step_binop_gas_budget >>
  disch_then (qspecl_then [`c`,`rb`,`rest`,`B`] mp_tac) >>
        simp[static_gas_def] >> decide_tac
QED
