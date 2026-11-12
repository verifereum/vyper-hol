(* Counted allocation boundary for aggregate literals. *)
Theory bodyPtrMakeArrayAllocation
Ancestors
  allocationPtr fragExecPtr fragGasSeqPtr venomInst

Theorem literal_alloca_ptr_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit n] [out]) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit n] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  mp_tac (Q.INST [`i` |-> `mk_inst id ALLOCA [Lit n] [out]`,
                  `lo` |-> `0`] straight_line_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def, ptr_inst_ok_alloca]
QED
