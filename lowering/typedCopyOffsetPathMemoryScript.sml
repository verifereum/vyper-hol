(* Reachable memory-safe byte-offset evaluation with its old-state frame. *)
Theory typedCopyOffsetPathMemory
Ancestors
  placeMemoryFieldsForward externalReturnNormalizeMem placedSequenceMemory
  typedMemoryCopy fragGasPathMem exprLoweringProps venomState
  words list rich_list arithmetic

Theorem typed_copy_offset_path_mem:
  !ptr off sa op sb s w func ctx dst len.
  compile_with_byte_offset ptr off sa = (op,sb) /\
  (!x. ptr = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr s = SOME w /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand op t = SOME (w + n2w off) /\
    t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa dst len s t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[normalize_byte_offset_mem_ok] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    gvs[FILTER_EQ_NIL] >>
  drule_all placed_sequence_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[eval_operand_def, lookup_var_def, typed_copy_state_frame_def,
      typed_copy_frame_def, venom_state_component_equality]
QED
