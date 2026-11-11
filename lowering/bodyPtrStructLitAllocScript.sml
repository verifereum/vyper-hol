(* Counted edge for the ALLOCA emitted by compile_alloc_buffer.
   Placement and successful machine execution remain consumer premises;
   ptr_inst_ok is discharged, for fresh and reused allocation sites alike. *)
Theory bodyPtrStructLitAlloc
Ancestors fragGasSeqPtr fragExecPtr venomInst venomExecSemantics

Theorem structlit_alloca_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit n] [p]) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u)
    (step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> simp[mk_inst_def] >>
  irule (SRULE [mk_inst_def, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id ALLOCA [Lit n] [p]`]
      straight_line_ptr_edge)) >>
  simp[GSYM mk_inst_def, ptr_inst_ok_alloca] >>
  metis_tac[]
QED
