(* Arbitrary-length runtime immutable copies with actual checked ghosts. *)
Theory exprSimPtrTopLevelImmutableRun
Ancestors exprSimPtrTopLevelImmutableCopy immutableCopyExecution exprSimCopy
  exprLoweringProps emitHelperProps emitHelper compileEnv context list
  fragGasSeqPtr instSeqComposePtr fragExec venomInst venomState words
  bodyPtrDefs codegenRel

Theorem toplevel_immutable_copy_shape:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >>
  gen_tac >> disch_tac >> first_x_assum drule >>
  simp[] >> strip_tac >> gvs[is_terminator_def]
QED

Theorem toplevel_immutable_one_nonterminators:
  immutable_copy_one F imm src dst off sa = ((),sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `compile_imm_copy_to_memory F imm src dst (SUC 0) off sa = ((),sb)` by
    simp[immutable_copy_suc, comp_ignore_bind_def, comp_bind_def,
         compile_imm_copy_to_memory_def, comp_return_def] >>
  drule toplevel_immutable_copy_shape >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem toplevel_immutable_copy_frame:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off+32*n <= capacity /\ w2n b+capacity < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := pc) H tm) /\
    ptr_covers H tm root t capacity /\
    immutable_copy_ghost_frame sa s G tn sb t H tm off (32*n) b
Proof
  Induct
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def,
           immutable_copy_ghost_frame_refl]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  `off+32 <= capacity /\ w2n b+capacity < dimword (:256)` by decide_tac >>
  drule_all toplevel_immutable_one_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `immutable_copy_one F imm src (Var root) off sa = ((),sm)` >>
  rename1 `immutable_copy_ghost_frame sa s G tn sm t1 G1 tn1 off 32 b` >>
  `copy_old_operand sm src /\ not_fresh_at sm root` by
    (gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
         copy_old_operand_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand src t1 = SOME a /\ op_taint tn1 src = {}` by
    metis_tac[immutable_copy_ghost_frame_operand] >>
  `lookup_var root t1 = SOME b` by
    metis_tac[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  `(off+32)+32*n <= capacity` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  suspend "compose"
QED

Resume toplevel_immutable_copy_frame[compose]:
  `immutable_copy_ghost_frame sa s G tn sb t H tm off (32+32*n) b` by
    (irule immutable_copy_ghost_frame_trans >>
     qexistsl_tac [`G1`,`sm`,`t1`,`tn1`] >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def]) >>
  qexistsl_tac [`t`,`H`,`tm`] >>
  simp[arithmeticTheory.MULT_SUC] >> conj_tac
  >- gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  conj_tac
  >- (irule inst_seq_ptr_uniform_append >> reverse conj_tac
      >- metis_tac[toplevel_immutable_one_nonterminators] >>
      qexistsl_tac [`G1`,`t1`,`tn1`] >> simp[]) >>
  gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def]
QED

Finalise toplevel_immutable_copy_frame

Theorem toplevel_immutable_copy_counted:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> drule toplevel_immutable_copy_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem toplevel_immutable_copy_counted_frontier:
  compile_imm_copy_to_memory F imm src (Var root) n off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off+32*n <= capacity /\ w2n b+capacity < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers H tm root t capacity /\
    immutable_copy_ghost_frame sa s G tn sb t H tm off (32*n) b
Proof
  strip_tac >> drule_all toplevel_immutable_copy_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all toplevel_immutable_copy_counted >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
         emitted_insts_def, DROP_APPEND] >>
     qpat_x_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[] >> decide_tac) >>
  qexistsl_tac [`t`,`H`,`tm`] >> gvs[]
QED
