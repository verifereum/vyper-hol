(* Installed counted MCOPY: payload and padding may be tainted, count may
   be zero. The safety premises concern addresses and the count only. *)
Theory bodyPtrMakeArrayBulkStep
Ancestors
  typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs
  venomInst venomExecSemantics venomState context ptrSafeRun ptrDiscipline
  memLocDefs codegenRel contextCodegenRel

Theorem mcopy_operand_ptr_path:
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK ((mcopy (w2n b) (w2n a) (w2n n) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id MCOPY [Var dst; Var src; count_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK ((mcopy (w2n b) (w2n a) (w2n n) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MCOPY [Var dst; Var src; count_op] []`,
                     `lo` |-> `0`,
                     `u` |-> `mcopy (w2n (b:256 word)) (w2n (a:256 word)) (w2n (n:256 word)) s`]
                    straight_line_ptr_edge) >>
     gvs[] >> simp[mk_inst_def, is_terminator_def, ptr_inst_ok_mcopy_operand,
                  Once step_inst_base_def, eval_operand_def] >> gvs[mk_inst_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_ptr_rules] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED
