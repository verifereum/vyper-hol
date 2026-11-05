Theory exprPtrUnwrapAllocated
Ancestors
  exprPtrUnwrapAllocation exprPtrUnwrapAllocationFrame exprPtrUnwrapInputFacts
  fragGasPathPtr ptrDiscipline bodyPtrDefs exprLoweringProps bufferAllocationExecution
  venomInst venomState arithmetic

(* Execute the actual emitted allocation, with all projections at the
   same raw and advanced endpoint. No independent ordinary run is chosen. *)
Theorem unwrap_alloc_path_covered:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?out u H tm.
    buf.buf_operand = Var out /\ buf.buf_size = nb /\
    u = update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id nb) /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
    H = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u /\
    tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers H tm out (u with vs_inst_idx := SUC s.vs_inst_idx) nb
Proof
  strip_tac >> drule_all unwrap_alloc_code_prefix >> strip_tac >>
  `allocas_from 0 s` by simp[unwrap_allocas_from_zero] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all unwrap_alloc_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  drule_all unwrap_alloc_output_coverage >>
  disch_then (qspecl_then [`tn`, `SUC s.vs_inst_idx`, `PG`, `G`] assume_tac) >>
  gvs[]
QED
