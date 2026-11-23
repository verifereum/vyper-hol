(* First-exit scope for the straight slices of buffered argument staging. *)
Theory entryStageBufferStraight
Ancestors
  entryCreateAdminSequence entryCreateKeywordStoreRun entryCreateCompletedCut
  entryCreateFocusSpec abiBufferAllocationCode context compileEnv fragExec
  abiEncoderProps exprLoweringProps venomInst venomState arithmetic rich_list list pred_set

Theorem stage_buffer_alloc_scope:
  compile_alloc_buffer n a = (buf,b) /\ fn_has_code a b fn /\
  create_operand_at a s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts a b) s = OK raw /\
  t = raw with vs_inst_idx := LENGTH b.cs_current_insts ==>
  create_expr_prefix a b explicit ctx fn s [] t /\ create_operand_at b t
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  `create_operand_full_scope a b explicit ctx fn s [] (OK t)` by
    (qpat_assum `t = raw with vs_inst_idx := _` SUBST1_TAC >>
     irule create_admin_sequence_scope >>
     simp[frag_ids_def, mk_inst_def, is_terminator_def]) >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED

Theorem stage_simple_store_layout[local]:
  compile_store_memory ce src dst dt st a = ((),b) /\
  (is_word_type dt \/ is_bytestring_type dt \/ dt = st \/
   tuple_memory_layout_eq dt st) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  Cases_on `~is_word_type dt /\ ~is_bytestring_type dt /\
            type_memory_bytes ce dt = 0`
  >- gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
         emitted_insts_def, DROP_LENGTH_NIL] >>
  `(if is_word_type dt then emit_void MSTORE [dst;src]
    else if is_bytestring_type dt then compile_store_bytestring src dst
    else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce dt))]) a = ((),b)` by
    (Cases_on `is_word_type dt` >> Cases_on `is_bytestring_type dt` >>
     gvs[compile_store_memory_def] >>
     Cases_on `type_memory_bytes ce dt` >> gvs[compile_copy_memory_def]) >>
  drule grouped_keyword_store_layout >> simp[EVERY_MEM] >> metis_tac[]
QED

(* The run is the branch's own raw MSTORE, bytestring copy or trivial
   empty-layout run; its indexed landing is also the post's state. *)
Theorem stage_buffer_simple_store_scope:
  compile_store_memory ce src dst dt st a = ((),b) /\
  (is_word_type dt \/ is_bytestring_type dt \/ dt = st \/
   tuple_memory_layout_eq dt st) /\
  fn_has_code a b fn /\ create_operand_at a s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts a b) s = OK raw /\
  t = raw with vs_inst_idx := LENGTH b.cs_current_insts ==>
  create_expr_prefix a b explicit ctx fn s [] t /\ create_operand_at b t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all stage_simple_store_layout >> strip_tac >>
  `create_operand_full_scope a b explicit ctx fn s [] (OK t)` by
    (qpat_assum `t = raw with vs_inst_idx := _` SUBST1_TAC >>
     irule create_admin_sequence_scope >> simp[]) >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED
