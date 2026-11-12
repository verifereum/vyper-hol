Theory bodyPtrPopCountedTransfer
Ancestors
  bodyPtrPopSliceTransfer exprSimPopStorage fragGasSeqPtr exprLoweringProps
  fragGasPathPtr venomInst venomState list rich_list

(* This boundary keeps the real block/cursor premises, and hides the fresh
   names and nine-opcode certificate from its consumers. *)
Theorem pop_root_emitted_opcode_facts:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
  LENGTH (emitted_insts sa sb) = 9
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  Cases_on `tr` >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem pop_root_run_counted:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + 9))
Proof
  strip_tac >> drule pop_root_emitted_opcode_facts >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem pop_root_abort_counted:
  compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?n j. gas_path_ptr D 0 ctx fn PG G tn s n Gf tnf
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule pop_root_emitted_opcode_facts >> strip_tac >>
  irule run_inst_seq_abort_gas_path_ptr >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
