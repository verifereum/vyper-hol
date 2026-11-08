Theory bodyPtrPopCaptureStaging
Ancestors bodyPtrPopCaptureAllocation valueCopy loweringHalt
  bufferAllocationExecution venomState compileEnv

Theorem pop_alloc_buffer_operand_frame:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  eval_operand src t = eval_operand src s
Proof
  strip_tac >> drule compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[] >> Cases_on `src` >>
  simp[eval_operand_def, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[buffer_allocation_fields_def] >> metis_tac[]
QED

Theorem pop_capture_alloc_store_run:
  compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s name lo capacity /\
  lo <= capture /\ capture + extent <= lo + capacity /\
  compile_store_memory cenv src buf.buf_operand ty ty sm = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME sw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) ==>
  ?t u w. run_inst_seq (emitted_insts sa sm) s = OK t /\
    run_inst_seq (emitted_insts sm sb) t = OK u /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    mem_bytes_at capture extent u.vs_memory = mem_bytes_at capture extent s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,MAX 32 (type_memory_bytes cenv ty)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    regions_disjoint (w2n w) (MAX 32 (type_memory_bytes cenv ty)) capture extent /\
    (u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  strip_tac >>
  `MAX 32 (type_memory_bytes cenv ty) < dimword (:256)` by
    (simp[arithmeticTheory.MAX_DEF] >> wordsLib.WORD_DECIDE_TAC) >>
  drule_all pop_capture_alloc_buffer_run >> strip_tac >>
  `eval_operand src t = SOME sw` by metis_tac[pop_alloc_buffer_operand_frame] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) t.vs_memory` by metis_tac[] >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = _`
      (mp_tac o AP_TERM ``\st:venom_state. st.vs_allocas``) >> simp[]) >>
  `mem_bytes_at capture extent u.vs_memory = mem_bytes_at capture extent s.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _`
       (qspecl_then [`capture`, `extent`] mp_tac) >>
     fs[regions_disjoint_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  qexistsl_tac [`t`, `u`, `w`] >> simp[] >> metis_tac[]
QED
