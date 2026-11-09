(* A reachable joint value/frame endpoint for a typed word copy. *)
Theory typedCopyWordPathMemory
Ancestors
  typedCopyPrimitiveMemory placedSequenceMemory typedMemoryCopy context compileEnv
  emitHelper exprLoweringProps fragExec venomInst venomState venomMemDefs
  valueEncoding valueEncodingProps valueCopy words list rich_list

Theorem typed_copy_word_no_gas[local]:
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  is_word_type dty ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem typed_copy_word_path_mem:
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  mem_word_at (w2n a) s.vs_memory = typed_val_to_w256 tv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  w2n a + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      typed_copy_state_frame sa (w2n d) (type_memory_size tv) s q /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_copy_word_run_seq >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_copy_word_mem_ok >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    metis_tac[typed_copy_word_no_gas] >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all placed_sequence_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `(mstore (w2n d) (mload (w2n a) s)
    (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s) s))
      with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_word_state_frame] >>
  drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
  gvs[same_blocks_def, mstore_def, write_memory_with_expansion_def, update_var_def,
      mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]
QED
