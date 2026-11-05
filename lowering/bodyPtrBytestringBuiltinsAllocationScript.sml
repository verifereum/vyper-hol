Theory bodyPtrBytestringBuiltinsAllocation
Ancestors
  allocationPtr fragExecPtr fragGasSeqPtr ghostPcTransportPtr
  bodyPtrDefs ptrSafeRun venomInst venomState exprLoweringProps

Theorem alloca_counted_edge_covers:
  !D ctx func cenv cx es s id n out u PG G tn bb.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    gas_path_ptr_edge D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      out (u with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac
  >- (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
      simp[ptr_inst_ok_alloca, mk_inst_def, is_terminator_def] >>
      disch_then irule >> simp[GSYM mk_inst_def, ptr_inst_ok_alloca]) >>
  simp[] >> irule alloca_step_ptr_covers >> metis_tac[]
QED
