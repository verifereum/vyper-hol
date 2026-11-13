(* The resolved memory Append suffix accesses its array's allocated region. *)
Theory appendMemoryPath
Ancestors
  stmtSimAppendResolved allocaFootprint fragExecMem instMemFrontier
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  venomState venomInst venomExecSemantics venomMemDefs list rich_list words
  varsExt freshWrites stateFrame finite_map ssaOperandFrame

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

Theorem append_memory_word_run_reserved:
  compile_dynarray_append ce bop vop 32 32 dt vt cap T MLOAD MSTORE sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME bp /\ eval_operand vop s = SOME w /\
  cap < dimword (:256) /\ w2n bp + 32*(1+cap) <= dimword (:256) ==>
  (cap <= w2n (mload (w2n bp) s) ==>
    ?a t. run_inst_seq (emitted_insts sa sf) s = Abort a t) /\
  (!len. len = w2n (mload (w2n bp) s) /\ len < cap ==>
    ?u. run_inst_seq (emitted_insts sa sf) s = OK u /\
      state_frame u = state_frame
        (mstore (w2n bp) (n2w (len+1))
          (mstore (w2n bp+32*(1+len)) w s)) /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==>
        lookup_var x u = SOME a))
Proof
  strip_tac >>
  drule append_memory_word_footprint >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME bp /\
   eval_operand vop (drop_fresh sa s) = SOME w` by
    (simp[eval_operand_drop_fresh] >> metis_tac[]) >>
  `mload (w2n bp) (drop_fresh sa s) = mload (w2n bp) s` by
    simp[drop_fresh_def, mload_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sf) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sf) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  conj_tac >- suspend "full" >> suspend "stored"
QED

Resume append_memory_word_run_reserved[full]:
  strip_tac >>
  `cap <= w2n (mload (w2n bp) (drop_fresh sa s))` by simp[] >>
  drule_all append_memory_word_abort >> strip_tac >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  simp[vars_ext_result_def] >> metis_tac[]
QED

Resume append_memory_word_run_reserved[stored]:
  rpt strip_tac >>
  `len = w2n (mload (w2n bp) (drop_fresh sa s)) /\
   w2n bp + 32*(1+cap) <= dimword (:256)` by simp[drop_fresh_def] >>
  drule_all append_memory_word_run >> strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sf) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >>
     asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa sf) s` >>
     simp[vars_ext_result_def]) >>
  qexists_tac `u` >> asm_rewrite_tac [] >> conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      qpat_x_assum `state_frame u = _` (fn th => pure_once_rewrite_tac [th]) >>
      qpat_x_assum `state_frame t = _` (fn th => pure_once_rewrite_tac [th]) >>
      asm_simp_tac bool_ss [] >>
      simp_tac bool_ss [drop_fresh_def, mstore_reset_vars, state_frame_vars]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[vars_ext_def, eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_SUBMAP]
QED

Finalise append_memory_word_run_reserved
