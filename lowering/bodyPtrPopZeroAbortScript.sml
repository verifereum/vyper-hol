Theory bodyPtrPopZeroAbort
Ancestors
  bodyPtrPopCountedTransfer stmtAppendStoragePathPtr fragGasSeqPtr
  exprLoweringProps list rich_list

(* The generic GAS-free abort lift already lives in stmtAppendStoragePathPtr;
   this leaf only specializes it to the Pop compiler slice. *)
Theorem pop_root_abort_counted_zero:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?j. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule pop_root_emitted_opcode_facts >> strip_tac >>
  irule run_inst_seq_abort_zero_path_ptr >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[EVERY_MEM, LENGTH_NIL, FILTER_EQ_NIL]
QED
