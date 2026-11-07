Theory bodyPtrStructLitRawChild
Ancestors bodyPtrStructLitAllocationBridge exprOperandVar freshWrites
  exprLoweringProps compileEnv context allocationPtr loweringHalt
  venomState venomExecSemantics venomInst finite_map

Theorem structlit_alloc_buffer_reserved:
  compile_alloc_buffer N sa = (buf,sb) /\ local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  local_ptrs_reserved ce sb /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sb p)
Proof
  strip_tac >> qspecl_then [`N`, `sa`] mp_tac ci_mono_compile_alloc_buffer >>
  simp[] >> strip_tac >>
  conj_tac >- (irule compiler_ci_mono_reserved >> metis_tac[]) >>
  fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem structlit_alloc_buffer_halted:
  compile_alloc_buffer N sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\ N < dimword (:256) ==>
  (u with vs_inst_idx := k).vs_halted = s.vs_halted
Proof
  strip_tac >> drule structlit_alloc_buffer_base_step >>
  disch_then (qspec_then `s` assume_tac) >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `N` mp_tac) >>
      simp[] >> disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
      gvs[update_var_def]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  gvs[step_inst_base_def, mk_inst_def, exec_alloca_def, update_var_def]
QED
