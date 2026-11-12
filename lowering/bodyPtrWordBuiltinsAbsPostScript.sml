(* Concrete dependency facts and the invariant-carrying Abs suffix. *)
Theory bodyPtrWordBuiltinsAbsPost
Ancestors bodyPtrWordBuiltinsAbsSequence bodyPtrWordBuiltinsAbsSuffix
  bodyPtrWordBuiltinsScalarSequence bodyPtrWordBuiltinsIntervalGhost
  exprLoweringProps builtinSimple compileEnv loweringStateRelDefs venomInst list pred_set
  bodyPtrDefs ptrDiscipline ptrSafeRun finite_map codegenRel fragGasSeqPtr

Theorem word_abs_emitted_shape:
  compile_builtin_abs v sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 9 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. MEM i.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
    (i.inst_opcode = ASSERT ==> ?v. i.inst_operands = [v] /\ i.inst_outputs = []) /\
    (i.inst_opcode <> ASSERT ==> ?x. i.inst_outputs = [x])) (emitted_insts sa sb)
Proof
  strip_tac >> drule word_abs_emitted_insts >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem word_abs_emitted_dependency:
  compile_builtin_abs v sa = (op,sb) ==>
  !pre i post x. emitted_insts sa sb = pre ++ i::post /\
    MEM (Var x) i.inst_operands ==>
    x IN {z | v = Var z} UNION set (FLAT (MAP (\j. j.inst_outputs) pre))
Proof
  strip_tac >> drule word_abs_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  ntac 10
    (qmatch_asmsub_rename_tac `pre ++ [i] ++ post` >>
     Cases_on `pre` >> gvs[mk_inst_def])
QED

Theorem word_abs_sequence_invariant:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  EVERY (\i. MEM i.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
    (i.inst_opcode = ASSERT ==> ?v. i.inst_operands = [v] /\ i.inst_outputs = []) /\
    (i.inst_opcode <> ASSERT ==> ?x. i.inst_outputs = [x])) xs /\
  (!pre i post x. xs = pre ++ i::post /\ MEM (Var x) i.inst_operands ==>
    x IN A UNION set (FLAT (MAP (\j. j.inst_outputs) pre))) /\
  (!i x n p sz. MEM i xs /\ MEM x i.inst_outputs /\
    FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!i x p sz. MEM i xs /\ MEM x i.inst_outputs /\ d <> NONE /\
    cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!i x p sz. MEM i xs /\ MEM x i.inst_outputs /\
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!i x p. MEM i xs /\ MEM x i.inst_outputs /\ not_fresh_at sa p ==> p <> x) /\
  ~ctx_has_dalloca ctx /\
  (!x. x IN A ==> FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
  allocas_from lo s /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sa G0 tn0 s0 G tn ==>
  ?H th. inst_seq_ptr D lo ctx fn PG G tn xs s H th /\
    (!t. run_inst_seq xs s = OK t ==>
      (!x. x IN A UNION set (FLAT (MAP (\i. i.inst_outputs) xs)) ==>
        FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
      allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
      ghost_kept cenv e0 sa G0 tn0 s0 H th)
Proof
  strip_tac >> irule (word_scalar_sequence |> Q.INST
    [`P` |-> `\B H th u.
      (!x. x IN B ==> FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
      allocas_from lo u /\ ghost_inv d cenv cx es H th u /\
      ghost_kept cenv e0 sa G0 tn0 s0 H th`] |> BETA_RULE) >> simp[] >>
  conj_tac >- simp[word_abs_allocas_index, word_interval_ghost_inv_index] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule word_abs_scalar_inst_ok >>
      gvs[EVERY_MEM] >>
      rpt strip_tac >> Cases_on `arg` >> gvs[op_prov_def, op_taint_def] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> fs[EVERY_MEM] >> conj_tac
  >- (gen_tac >> disch_tac >> irule word_abs_scalar_transfer >>
      reverse conj_tac >- metis_tac[MEM] >>
      qexists_tac `B` >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule word_abs_step_allocas >>
    qexistsl_tac [`i`, `u`] >> simp[MEM] >> metis_tac[]) >>
  conj_tac >- (irule word_abs_step_ghost_inv >> simp[MEM] >> metis_tac[]) >>
  irule word_abs_step_ghost_kept >> simp[MEM] >> metis_tac[]
QED

Theorem word_abs_outputs_fresh:
  compile_builtin_abs v sa = (op,sb) /\ sc.cs_next_var <= sa.cs_next_var ==>
  !i x p. MEM i (emitted_insts sa sb) /\ MEM x i.inst_outputs /\
    not_fresh_at sc p ==> p <> x
Proof
  strip_tac >> drule word_abs_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[MEM, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem word_abs_emitted_checked:
  compile_builtin_abs v sa = (op,sb) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ?H th. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
      ghost_kept cenv e0 sc G0 tn0 s0 H th /\
      op_prov H op = NONE /\ op_taint th op = {})
Proof
  strip_tac >> drule word_abs_emitted_shape >> strip_tac >>
  drule word_abs_emitted_dependency >> strip_tac >>
  drule word_abs_outputs_fresh >>
  disch_then (qspec_then `sc` mp_tac) >> simp[] >> strip_tac >>
  `?H th. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      (!x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb))) ==>
        FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
      allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
      ghost_kept cenv e0 sc G0 tn0 s0 H th)` by
    (irule word_abs_sequence_invariant >> simp[] >>
     fs[local_ptrs_reserved_def, EVERY_MEM] >> rpt conj_tac >>
     rpt strip_tac >> gvs[op_prov_def] >> metis_tac[]) >>
  qexistsl_tac [`H`, `th`] >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  drule word_abs_emitted_insts >> strip_tac >> gvs[] >>
  simp[op_prov_def] >> first_x_assum irule >> simp[mk_inst_def]
QED

Theorem word_abs_counted_normal_post:
  compile_builtin_abs v sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  op_prov G v = NONE /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ?H th. gas_path_ptr D lo ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + 9)) /\
    allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
    ghost_kept cenv e0 sc G0 tn0 s0 H th /\
    op_prov H op = NONE /\ op_taint th op = {}
Proof
  strip_tac >> drule_all word_abs_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all word_abs_code_prefix >> strip_tac >>
  drule word_abs_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >>
  metis_tac[]
QED

Theorem word_abs_counted_abort:
  compile_builtin_abs v sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t /\
  op_prov G v = NONE /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ?n j H th. gas_path_ptr D lo ctx fn PG G tn s n H th
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all word_abs_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all word_abs_code_prefix >> strip_tac >>
  drule word_abs_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED
