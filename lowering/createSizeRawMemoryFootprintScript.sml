(* The actual post-allocation memory-to-memory snapshot segment. *)
Theory createSizeRawMemoryFootprint
Ancestors
  exprLoweringProps exprSimCopy exprSimStorageCopy exprSimBufferStore
  loweringStateRelDefs emitHelperProps emitHelper compileEnv context
  ssaOperandFrame stmtReasonMemory venomExecSemantics venomState venomInst
  valueEncodingDefs finite_map words arithmetic list rich_list

Theorem create_raw_memory_copy_frame:
  emit_op MLOAD [src] m = (len,a) /\
  emit_op ADD [len; Lit 32w] a = (cnt,c) /\
  compile_copy_memory_dynamic dst src cnt c = ((),b) /\
  copy_old_operand m src /\ copy_old_operand m dst /\
  eval_operand src y = SOME p /\ eval_operand dst y = SOME d /\
  mload (w2n p) y = n2w n /\ n + 32 < dimword (:256) /\
  run_inst_seq (emitted_insts m b) y = OK (z with vs_inst_idx := y.vs_inst_idx) ==>
  copy_static z = copy_static y /\ LENGTH y.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x y) /\
  (!off k. off+k <= w2n d \/ w2n d + (n+32) <= off ==>
     mem_bytes_at off k z.vs_memory = mem_bytes_at off k y.vs_memory)
Proof
  strip_tac >>
  `LENGTH y.vs_memory <= LENGTH z.vs_memory` by
    (drule run_inst_seq_memory_length >> simp[]) >> simp[] >>
  imp_res_tac emitted_insts_emit_op >>
  qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
  simp[compile_copy_memory_dynamic_def, emit_void_def, comp_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ y = _` mp_tac >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[] >>
  qmatch_goalsub_abbrev_tac `mk_inst _ MLOAD [_] [lv]` >>
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD [_;_] [sv]` >>
  `!x. not_fresh_at m x ==> x <> lv /\ x <> sv` by
    (simp[Abbr `lv`, Abbr `sv`, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1``]) >>
  `src <> Var lv /\ src <> Var sv /\ dst <> Var lv /\ dst <> Var sv` by
    metis_tac[copy_old_operand_def] >>
  simp[run_inst_seq_def, step_mload_eq, step_add_eq, step_mcopy_eq,
       eval_operand_update_var_avoids, eval_operand_def, lookup_var_update_var,
       word_add_n2w, w2n_n2w] >>
  qmatch_goalsub_abbrev_tac `mcopy _ _ _ u` >> strip_tac >>
  `u.vs_memory = y.vs_memory` by simp[Abbr `u`, update_var_def] >>
  conj_tac
  >- (qpat_x_assum `mcopy _ _ _ _ = _` (mp_tac o Q.AP_TERM `copy_static`) >>
      simp[copy_static_def, mcopy_def, write_memory_with_expansion_def,
           Abbr `u`, update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> lv /\ x <> sv` by metis_tac[] >>
      qpat_x_assum `mcopy _ _ _ _ = _` (mp_tac o Q.AP_TERM `lookup_var x`) >>
      simp[lookup_var_def, mcopy_vars, Abbr `u`, update_var_def, FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  qpat_x_assum `mcopy _ _ _ _ = _` (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  qpat_x_assum `u.vs_memory = y.vs_memory` (SUBST1_TAC o SYM) >>
  irule buffer_mcopy_exterior >> decide_tac
QED
