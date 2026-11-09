(* The counted allocation edge and its capacity post share the same actual
   step_inst_base result. Age and local separation are supplied by the existing
   literal_alloc_buffer_run compiler boundary, not inferred from provenance. *)
Theory bodyPtrMakeArrayAllocationPost
Ancestors
  bodyPtrMakeArrayAllocation allocationPtr venomState venomInst ptrDiscipline
  bodyPtrDefs

Theorem literal_alloca_ptr_capacity:
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
  strip_tac >> conj_tac
  >- (irule literal_alloca_ptr_edge >> metis_tac[]) >>
  drule_all alloca_step_ptr_covers >>
  simp[ptr_covers_def, lookup_var_def]
QED
