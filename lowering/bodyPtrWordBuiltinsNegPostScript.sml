(* Normal posts eliminate the very ghosts used by the checked sequence. *)
Theory bodyPtrWordBuiltinsNegPost
Ancestors exprSimUnopProps bodyPtrWordBuiltinsNegSuffix bodyPtrWordBuiltinsArithmeticSteps
  bodyPtrWordBuiltinsIntervalGhost bodyPtrDefs fragGasSeqPtr ptrDiscipline
  venomExecSemantics venomInst venomState exprLoweringProps list finite_map

Theorem word_neg_pure2_normal_update:
  MEM opc [SGT; SUB] /\
  step_inst_base (mk_inst id opc [a;b] [x]) s = OK t ==>
  ?w. t = update_var x w s
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem word_neg_sub_normal_post:
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id SUB [Lit 0w; v] [y]] s G' tn' /\
  run_inst_seq [mk_inst id SUB [Lit 0w; v] [y]] s = OK t /\
  op_prov G v = NONE /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p. not_fresh_at sc p ==> p <> y) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv e0 sc G0 tn0 s0 G' tn' /\ op_taint tn' (Var y) = {} /\ op_prov G' (Var y) = NONE
Proof
  strip_tac >>
  Cases_on `step_inst_base (mk_inst id SUB [Lit 0w; v] [y]) s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) word_neg_pure2_normal_update >>
  simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule word_neg_output_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule word_neg_output_ghost_kept >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule word_arithmetic_output_clean >> simp[mk_inst_def]) >>
  gvs[ptrSafeRunTheory.ghost_step_def, step_prov_def, out_prov_def, set_prov_def,
      first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem word_neg_assert_sub_normal_post:
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst ia ASSERT [a] []; mk_inst ib SUB [Lit 0w; v] [y]] s G' tn' /\
  run_inst_seq [mk_inst ia ASSERT [a] []; mk_inst ib SUB [Lit 0w; v] [y]] s = OK t /\
  op_prov G v = NONE /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> y) /\
  (!p. not_fresh_at sc p ==> p <> y) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv e0 sc G0 tn0 s0 G' tn' /\ op_taint tn' (Var y) = {} /\ op_prov G' (Var y) = NONE
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[GSYM mk_inst_def] >>
  drule word_neg_assert_step >> strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once inst_seq_ptr_def, word_neg_assert_ghost_identity] >> strip_tac >>
  drule word_neg_sub_normal_post >>
  simp[word_interval_ghost_inv_index, fragExecTheory.run_inst_seq_inst_idx,
       mk_inst_def, is_terminator_def, instIdxIndepTheory.exec_result_map_def] >>
  disch_then irule >> simp[]
QED

Theorem word_neg_sequence_normal_post:
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst ia SGT [v; Lit low] [x]; mk_inst ib ASSERT [Var x] [];
     mk_inst ic SUB [Lit 0w; v] [y]] s G' tn' /\
  run_inst_seq [mk_inst ia SGT [v; Lit low] [x];
    mk_inst ib ASSERT [Var x] []; mk_inst ic SUB [Lit 0w; v] [y]] s = OK t /\
  op_prov G v = NONE /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  (!z n p sz. MEM z [x;y] /\ FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> z) /\
  (!z p sz. MEM z [x;y] /\ d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> z) /\
  (!z p sz. MEM z [x;y] /\ cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> z) /\
  (!z p. MEM z [x;y] /\ not_fresh_at sc p ==> p <> z) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv e0 sc G0 tn0 s0 G' tn' /\ op_taint tn' (Var y) = {} /\ op_prov G' (Var y) = NONE
Proof
  strip_tac >>
  Cases_on `step_inst_base (mk_inst ia SGT [v; Lit low] [x]) s` >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >> strip_tac >>
  drule_at (Pat `step_inst_base _ _ = _`) word_neg_pure2_normal_update >>
  simp[] >> disch_then (qx_choose_then `w` SUBST_ALL_TAC) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once inst_seq_ptr_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D lo ctx fn PG G1 tn1 code s1 G' tn'` >>
  `ghost_inv d cenv cx es G1 tn1 s1` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`, word_interval_ghost_inv_index] >>
     irule word_neg_output_ghost_inv >> simp[] >> metis_tac[MEM]) >>
  `ghost_kept cenv e0 sc G0 tn0 s0 G1 tn1` by
    (simp[Abbr `G1`, Abbr `tn1`] >>
     irule word_neg_output_ghost_kept >> simp[] >> metis_tac[MEM]) >>
  `op_prov G1 v = NONE` by
    (Cases_on `v` >>
     fs[op_prov_def] >>
     simp[Abbr `G1`, op_prov_def, step_prov_def, out_prov_def,
          set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  fs[Abbr `code`] >>
  drule word_neg_assert_sub_normal_post >>
  simp[Abbr `s1`, fragExecTheory.run_inst_seq_inst_idx,
       mk_inst_def, is_terminator_def, instIdxIndepTheory.exec_result_map_def,
       word_interval_ghost_inv_index] >>
  disch_then irule >> fs[word_interval_ghost_inv_index] >> metis_tac[MEM]
QED

Theorem word_neg_compiled_normal_post:
  compile_neg v ty sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  op_prov G v = NONE /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv e0 sc G0 tn0 s0 G' tn' /\ op_taint tn' op = {} /\ op_prov G' op = NONE
Proof
  strip_tac >> drule word_neg_emitted_insts >> strip_tac >>
  qpat_x_assum `compile_neg _ _ _ = _` kall_tac >>
  gvs[] >> drule word_neg_sequence_normal_post >>
  simp[] >> disch_then irule >>
  `sc.cs_next_var <= sa.cs_next_var + 1` by decide_tac >>
  fs[compileEnvTheory.local_ptrs_reserved_def, compileEnvTheory.not_fresh_at_def] >>
  metis_tac[]
QED

Theorem word_neg_counted_normal_post:
  compile_neg v ty sa = (op,sb) /\ fn_has_code sa sb fn /\
  fresh_vars_wrt sa s /\ eval_operand v s = SOME w /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G v = NONE /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv e0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  w2i (FST (type_bounds ty)) < w2i w ==>
  ?t G' tn'.
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    eval_operand op t = SOME (0w - w) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv e0 sc G0 tn0 s0 G' tn' /\ op_taint tn' op = {} /\ op_prov G' op = NONE
Proof
  strip_tac >> drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all word_neg_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule_all word_neg_compiled_normal_post >> strip_tac >>
  drule_all word_neg_code_prefix >> strip_tac >>
  drule word_neg_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >>
  metis_tac[]
QED
