(* Counted copies retain source taint; they do not manufacture cleanliness. *)
Theory bodyPtrStructLitCopyPath
Ancestors batchCopyRobustPtr fragGasSeqPtr fragExecPtr fragGasPathPtr
  typedCopyPtr venomInst venomExecSemantics venomState ptrDiscipline words

Theorem mcopy_operand_counted_path:
  !D ctx fn PG G tn s bb id dst src n a b.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] []) /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n < dimword(:256) /\ ptr_covers G tn src s n /\
    ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        (mcopy (w2n b) (w2n a) n s))
      (step_taint (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        s (mcopy (w2n b) (w2n a) n s) tn)
      (OK ((mcopy (w2n b) (w2n a) n s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        (mcopy (w2n b) (w2n a) n s))
      (step_taint (mk_inst id MCOPY [Var dst; Var src; Lit (n2w n)] [])
        s (mcopy (w2n b) (w2n a) n s) tn)
      (OK ((mcopy (w2n b) (w2n a) n s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_assum `get_instruction _ _ = SOME _`
       (mp_then Any mp_tac straight_line_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
     conj_tac
     >- simp[Once step_inst_base_def, mk_inst_def, eval_operand_def, w2n_n2w] >>
     conj_tac >- simp[] >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_operand) >>
     simp[eval_operand_def, op_taint_def, w2n_n2w]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED
