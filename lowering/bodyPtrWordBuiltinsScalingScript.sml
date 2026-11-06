(* Unsigned scaling keeps the original operand when the multiplier is one. *)
Theory bodyPtrWordBuiltinsScaling
Ancestors bodyPtrWordBuiltinsScalingSteps bodyPtrWordBuiltinsAbsPost
  bodyPtrWordBuiltinsAbsSequence bodyPtrWordBuiltinsAbsSuffix
  bodyPtrWordBuiltinsScalarSequence bodyPtrWordBuiltinsIntervalGhost
  builtinMisc builtinSimple exprSimWordBuiltins exprLoweringProps compileEnv
  emitHelper venomInst list rich_list pred_set bodyPtrDefs ptrDiscipline ptrSafeRun
  finite_map codegenRel fragGasSeqPtr venomState fragExec fragGasPathPtr

Theorem word_scale_identity:
  compile_as_wei_value_int v 1 F sa = (op,sb) ==>
  op = v /\ sb = sa /\ emitted_insts sa sb = []
Proof
  simp[compile_as_wei_value_int_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def]
QED

Theorem word_scale_emitted_insts:
  compile_as_wei_value_int v m F sa = (op,sb) /\ m <> 1 ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MUL [v; Lit (n2w m)]
      [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) Div
      [Var (STRING #"%" (toString sa.cs_next_var)); v]
      [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) EQ
      [Var (STRING #"%" (toString (sa.cs_next_var + 1))); Lit (n2w m)]
      [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) ISZERO [v]
      [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) OR
      [Var (STRING #"%" (toString (sa.cs_next_var + 2)));
       Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
      [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
      [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []] /\
  op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >>
  gvs[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, emit_void_def, fresh_id_def,
      fresh_var_def, emit_def, comp_return_def, emitted_insts_def] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem word_scale_emitted_shape:
  compile_as_wei_value_int v m F sa = (op,sb) /\ m <> 1 ==>
  LENGTH (emitted_insts sa sb) = 6 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
    (i.inst_opcode = ASSERT ==> ?v. i.inst_operands = [v] /\ i.inst_outputs = []) /\
    (i.inst_opcode <> ASSERT ==> ?x. i.inst_outputs = [x])) (emitted_insts sa sb)
Proof
  strip_tac >> drule_all word_scale_emitted_insts >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem word_scale_emitted_dependency:
  compile_as_wei_value_int v m F sa = (op,sb) /\ m <> 1 ==>
  !pre i post x. emitted_insts sa sb = pre ++ i::post /\
    MEM (Var x) i.inst_operands ==>
    x IN {z | v = Var z} UNION set (FLAT (MAP (\j. j.inst_outputs) pre))
Proof
  strip_tac >> drule_all word_scale_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  ntac 7
    (qmatch_asmsub_rename_tac `pre ++ [i] ++ post` >>
     Cases_on `pre` >> gvs[mk_inst_def])
QED

Theorem word_scale_outputs_fresh:
  compile_as_wei_value_int v m F sa = (op,sb) /\ m <> 1 /\
  sc.cs_next_var <= sa.cs_next_var ==>
  !i x p. MEM i (emitted_insts sa sb) /\ MEM x i.inst_outputs /\
    not_fresh_at sc p ==> p <> x
Proof
  strip_tac >> drule_all word_scale_emitted_insts >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[MEM, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem word_scale_sequence_checked:
  compile_as_wei_value_int v m F sa = (op,sb) /\ m <> 1 /\
  op_prov G v = NONE /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ?H th. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      (!x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb))) ==>
        FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
      allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
      ghost_kept cenv e0 sc G0 tn0 s0 H th)
Proof
  strip_tac >> drule_all word_scale_emitted_shape >> strip_tac >>
  drule word_scale_emitted_dependency >> strip_tac >>
  drule word_scale_outputs_fresh >>
  disch_then (qspec_then `sc` mp_tac) >> strip_tac >>
  irule (word_scalar_sequence |> Q.INST
    [`P` |-> `\B H th u.
      (!x. x IN B ==> FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
      allocas_from lo u /\ ghost_inv d cenv cx es H th u /\
      ghost_kept cenv e0 sc G0 tn0 s0 H th`] |> BETA_RULE) >>
  simp[] >>
  conj_tac >- simp[word_abs_allocas_index, word_interval_ghost_inv_index] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> fs[EVERY_MEM] >>
      `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by metis_tac[MEM] >>
      `(i.inst_opcode = ASSERT ==> ?v. i.inst_operands = [v] /\ i.inst_outputs = []) /\
       (i.inst_opcode <> ASSERT ==> ?x. i.inst_outputs = [x])` by metis_tac[] >>
      conj_tac
      >- (gen_tac >> disch_tac >> irule word_scale_scalar_transfer >>
          reverse conj_tac >- metis_tac[MEM] >>
          qexists_tac `B` >> simp[] >> metis_tac[MEM]) >>
      conj_tac >- (irule word_scale_step_allocas >>
        qexistsl_tac [`i`, `u`] >> simp[] >> metis_tac[]) >>
      conj_tac >- (irule word_scale_step_ghost_inv >> simp[] >>
        fs[local_ptrs_reserved_def] >> metis_tac[MEM]) >>
      irule word_scale_step_ghost_kept >> simp[] >> metis_tac[MEM]) >>
  conj_tac
  >- (rpt strip_tac >> irule word_scale_inst_ok >> gvs[EVERY_MEM] >>
      rpt strip_tac >> Cases_on `arg` >> gvs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[op_prov_def]) >>
  fs[EVERY_MEM]
QED

Theorem word_scale_emitted_checked:
  compile_as_wei_value_int v m F sa = (op,sb) /\
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
  strip_tac >> Cases_on `m = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[] >>
      qexistsl_tac [`G`, `tn`] >> simp[inst_seq_ptr_def, run_inst_seq_def]) >>
  drule_all word_scale_sequence_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `th`] >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  drule_all word_scale_emitted_insts >> strip_tac >> gvs[] >>
  simp[op_prov_def] >> first_x_assum irule >> simp[mk_inst_def]
QED

Theorem word_scale_current_block:
  compile_as_wei_value_int v m F sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  LENGTH (emitted_insts sa sb) = (if m = 1 then 0 else 6)
Proof
  strip_tac >> Cases_on `m = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[]) >>
  gvs[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
      emit_op_def, emit_void_def, fresh_id_def,
      fresh_var_def, emit_def, comp_return_def, emitted_insts_def] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem word_scale_code_prefix:
  compile_as_wei_value_int v m F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule word_scale_current_block >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem word_scale_counted_normal_post:
  compile_as_wei_value_int v m F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  op_prov G v = NONE /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ?H th. gas_path_ptr D lo ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + (if m = 1 then 0 else 6))) /\
    allocas_from lo t /\ ghost_inv d cenv cx es H th t /\
    ghost_kept cenv e0 sc G0 tn0 s0 H th /\
    op_prov H op = NONE /\ op_taint th op = {}
Proof
  strip_tac >> Cases_on `m = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >>
      gvs[run_inst_seq_def] >> qexistsl_tac [`G`, `tn`] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      asm_rewrite_tac[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  drule_all word_scale_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all word_scale_code_prefix >> strip_tac >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> metis_tac[]
QED

Theorem word_scale_counted_abort:
  compile_as_wei_value_int v m F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
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
  strip_tac >> Cases_on `m = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[run_inst_seq_def]) >>
  drule_all word_scale_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule_all word_scale_code_prefix >> strip_tac >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED
