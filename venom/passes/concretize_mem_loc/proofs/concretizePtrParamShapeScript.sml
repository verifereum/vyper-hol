Theory concretizePtrParamShape
Ancestors venomWfProps
  concretizePtrParamSupport o1PassContract venomWf removeUnusedSsaProofs list

Theorem o1_ctx_shape_instructions_wf:
  o1_ctx_shape ctx ==>
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def,
       venomInstTheory.fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
