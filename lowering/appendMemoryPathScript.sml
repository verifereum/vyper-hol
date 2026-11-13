(* The resolved memory Append suffix accesses its array's allocated region. *)
Theory appendMemoryPath
Ancestors
  stmtSimAppendResolved allocaFootprint fragExecMem instMemFrontier
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  venomState venomInst venomExecSemantics venomMemDefs list rich_list words

Theorem append_memory_word_footprint:
  compile_dynarray_append ce bop vop 32 32 dt vt cap T MLOAD MSTORE sa = ((),sf) ==>
  same_blocks sa sf /\ inst_extends sa sf /\
  sa.cs_next_var <= sf.cs_next_var /\ ~block_is_terminated sf /\
  EVERY (\i. MEM i.inst_opcode [MLOAD; LT; ASSERT; ADD; MUL; MSTORE])
    (emitted_insts sa sf)
Proof
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  simp[mk_inst_def, block_is_terminated_def, is_terminator_def,
       LAST_CONS_cond, LAST_APPEND_NOT_NIL]
QED

val append_word_mem_step_tac =
  pure_once_rewrite_tac [run_inst_seq_mem_ok_def] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs,
    mk_inst_def, exec_read1_def, exec_pure2_def, exec_write2_def,
    below_frontier_MLOAD, below_frontier_MSTORE, below_frontier_no_ranges,
    memSafeRunTheory.inst_dload_in_section_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    bool_to_word_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
    unitTransformDefsTheory.inst_mem_below_frontier_def, contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def, codegenRelTheory.fixed_source_write_range_def, mstore_def, LET_THM];

Theorem append_memory_word_mem_ok:
  compile_dynarray_append ce bop vop 32 32 dt vt cap T MLOAD MSTORE sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME bp /\ eval_operand vop s = SOME w /\
  cap < dimword (:256) /\
  w2n bp + 32*(1+cap) <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sf) s
Proof
  strip_tac >>
  `!n. sa.cs_next_var <= n ==>
    bop <> Var (STRING #"%" (toString n)) /\
    vop <> Var (STRING #"%" (toString n))` by
    metis_tac[not_fresh_at_def] >>
  `w2n bp + 32 <= s.vs_alloca_next` by decide_tac >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  Cases_on `w2n (mload (w2n bp) s) < cap`
  >- suspend "success" >> suspend "full"
QED

Resume append_memory_word_mem_ok[full]:
  Cases_on `bop` >> Cases_on `vop` >>
  gvs[eval_operand_def, not_fresh_at_def, lookup_var_def] >>
  `cap < dimword (:256)` by decide_tac >>
  ntac 3 (pure_once_rewrite_tac [run_inst_seq_mem_ok_def] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs,
    mk_inst_def, exec_read1_def, exec_pure2_def, exec_write2_def,
    below_frontier_MLOAD, below_frontier_MSTORE, below_frontier_no_ranges,
    memSafeRunTheory.inst_dload_in_section_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    bool_to_word_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  decide_tac
QED

Resume append_memory_word_mem_ok[success]:
  `w2n (bp + 32w + mload (w2n bp) s * 32w) =
   w2n bp + 32*(1+w2n (mload (w2n bp) s))` by
    (rewrite_tac [wordsTheory.word_add_def, wordsTheory.word_mul_def] >>
     simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  Cases_on `bop` >> Cases_on `vop` >>
  gvs[eval_operand_def, not_fresh_at_def, lookup_var_def] >>
  `cap < dimword (:256)` by decide_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  append_word_mem_step_tac >>
  pure_rewrite_tac [run_inst_seq_mem_ok_last] >>
  asm_simp_tac (srw_ss()) [unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    memSafeRunTheory.inst_dload_in_section_def,
    eval_operand_def, lookup_var_def, mk_inst_def,
    finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FUPDATE_LIST_THM,
    fresh_var_neq, mstore_def, LET_THM] >> decide_tac
QED

Finalise append_memory_word_mem_ok
