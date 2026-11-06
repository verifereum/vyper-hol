(* Arbitrary unrolled immutable copies retain the full allocation capacity. *)
Theory exprPtrCodeCopyInduction
Ancestors
  exprPtrCodeCopyIteration emittedSeqComposePtr exprSimCopy immutableCopyExecution
  context compileEnv exprLoweringProps ptrDiscipline venomState venomInst
  ptrSafeRun bodyPtrDefs words pred_set arithmetic list fragGasSeqPtr finite_map fragExec emitHelperProps entrySinkExtraction rich_list fragGasPathPtr

Theorem code_copy_taint_intervals[local]:
  (m DIFF {j | b+off <= j /\ j < b+off+32}) DIFF
    {j | b+(off+32) <= j /\ j < b+(off+32)+32*n} =
  m DIFF {j | b+off <= j /\ j < b+off+32*SUC n}
Proof
  simp[EXTENSION, MULT_SUC] >> gen_tac >> Cases_on `x IN m` >> simp[] >>
  qabbrev_tac `k = 32*n` >> decide_tac
QED

Theorem code_copy_range_ptr:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off+32*n <= capacity /\ w2n b+capacity < dimword(:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem = tn.t_mem DIFF {j | w2n b+off <= j /\ j < w2n b+off+32*n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl [`G`, `tn`, `s`] >>
      simp[copy_runtime_frame_refl, emitted_insts_def, inst_seq_ptr_def]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `immutable_copy_one F imm src (Var root) off sa = ((),sm)` >>
  `off < capacity /\ off+32 <= capacity /\ w2n b+off < dimword(:256)` by decide_tac >>
  drule_all code_copy_runtime_one_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `copy_old_operand sm src /\ not_fresh_at sm root /\
    eval_operand src t = SOME a /\ lookup_var root t = SOME b /\
    op_taint tnf src = {} /\ ptr_covers Gf tnf root t capacity` by
    (rpt conj_tac
     >- (irule copy_old_operand_mono >> metis_tac[copy_runtime_frame_def])
     >- metis_tac[]
     >- metis_tac[copy_runtime_frame_operand]
     >- fs[copy_runtime_frame_def]
     >- metis_tac[old_operand_taint_frame, copy_old_operand_def]
     >> metis_tac[]) >>
  `(off+32)+32*n <= capacity /\ w2n b+capacity < dimword(:256)` by
    (fs[MULT_SUC] >> decide_tac) >>
  qpat_x_assum `!off sa sb s G tn. _` drule_all >> strip_tac >>
  `w2n (b+n2w off) = w2n b+off` by
    (Cases_on `b` >> fs[word_add_n2w]) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >>
  reverse (rpt conj_tac)
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (pure_asm_rewrite_tac[] >> rewrite_tac[code_copy_taint_intervals] >>
      AP_TERM_TAC >> simp[EXTENSION, MULT_SUC] >> decide_tac)
  >- (irule emitted_inst_seq_ptr_uniform_compose >>
      qexistsl [`Gf`, `sm`, `t`, `tnf`] >>
      fs[copy_runtime_frame_def, inst_extends_def] >>
      drule code_copy_one_insts >> simp[EVERY_MEM] >>
      metis_tac[is_terminator_def]) >>
  metis_tac[copy_runtime_frame_trans]
QED


Theorem code_copy_range_code_cursor:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb fn /\ copy_runtime_frame sa s sb t /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by fs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[copy_runtime_frame_def, same_blocks_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all code_copy_range_counted >> simp[]
QED
