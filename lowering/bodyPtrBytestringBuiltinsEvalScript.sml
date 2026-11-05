Theory bodyPtrBytestringBuiltinsEval
Ancestors
  bodyPtrBytestringBuiltinsUnary fragGasPathPtr

Theorem gas_outcome_ptr_eval_evidence:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) P E ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. P res ee G tn t /\
      ?marks ee0. ee = ee0 with gas_obs := [] /\
        !tail. source
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (res,ee0 with gas_obs := tail)) E
Proof
  rw[gas_outcome_ptr_def, gas_summary_ptr_at_def] >> metis_tac[]
QED
