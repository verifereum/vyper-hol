Theory bodyPtrPopContextContainment
Ancestors
  bodyPtrPopGlobalContainment venomInst list

Theorem pop_global_lookup_no_invoke:
  !name fn.
    venomInst$lookup_function name pop_global_runtime_context.ctx_functions = SOME fn ==>
    EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts fn)
Proof
  rpt strip_tac >> drule venomInstTheory.lookup_function_MEM >>
  mp_tac pop_global_context_no_invoke >>
  simp[EVERY_MEM] >> metis_tac[]
QED
