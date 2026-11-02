(* A straight-line helper retains its raw cursor; use the actual code
   slice to recover allocation history at its normalized landing. *)
Theory allocaHistoryFragment
Ancestors
  allocaHistory exprLoweringProps instIdxIndep venomWf venomInst venomState
  venomExecSemantics venomMemDefs venomMemProofs list arithmetic

Theorem alloca_history_run_inst_seq:
  !func bb s insts rest t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = insts ++ rest /\
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts /\
    run_inst_seq insts s = OK t ==>
    alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  cheat
QED
