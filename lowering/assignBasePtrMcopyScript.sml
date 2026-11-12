(* A direct MCOPY needs natural range coverage, not source nonwrap.
   The successful ordinary step is supplied by the semantic continuation. *)
Theory assignBasePtrMcopy
Ancestors
  fragExecPtr fragGasSeqPtr emitHelper venomInst

Theorem assign_base_mcopy_operand_edge_ptr:
  !s fn bb id dst src count_op n tn G ctx u D PG.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\
    ptr_covers G tn src s (w2n n) /\ ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id MCOPY [Var dst; Var src; count_op] []) s = OK u ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst; Var src; count_op] []) u)
      (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MCOPY [Var dst; Var src; count_op] []) s` by
    (irule ptr_inst_ok_mcopy_operand >> simp[] >> qexists_tac `n` >> simp[]) >>
  mp_tac (Q.INST
    [`i` |-> `mk_inst id MCOPY [Var dst; Var src; count_op] []`,
     `lo` |-> `0`] straight_line_ptr_edge) >>
  simp[mk_inst_def, is_terminator_def]
QED
