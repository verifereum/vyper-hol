Theory bodyPtrPopZeroAbort
Ancestors
  bodyPtrPopCountedTransfer stmtAppendStoragePathPtr fragGasSeqPtr fragGasSeqAbort
  fragExec venomExecSemantics venomInstProofs instIdxIndep
  exprLoweringProps list rich_list

(* The Pop compiler slice's abort, with its cursor chosen before the mask. *)
Theorem pop_root_abort_counted_zero:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?j. !D lo PG G tn G' tn'.
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule pop_root_emitted_opcode_facts >> strip_tac >>
  irule run_inst_seq_abort_zero_path_ptr_uniform >> simp[] >>
  fs[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL]
QED
