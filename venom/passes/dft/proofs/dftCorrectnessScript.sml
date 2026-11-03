(*
 * DFT Pass — Correctness
 *
 * TOP-LEVEL:
 *   dft_pass_correct — DFT preserves execution semantics (pass_correct)
 *
 * Proof strategy:
 *   1. dft_fn only changes bb_instructions of each block (labels preserved)
 *   2. For each block, run_block on dft_block produces lift_result-compatible
 *      results: OK states are identical (run_insts_perm_ok), Abort/Halt have
 *      same constructor and abort type (state is T, irrelevant in EVM).
 *   3. run_function lift_result follows by induction on fuel
 *   4. pass_correct follows from lift_result bridge
 *
 * R_term = execution_equiv {} for Halt/IntRet (states identical).
 * R_abort = revert_equiv for Abort (only returndata survives EVM rollback).
 * DFT can reorder independent instructions past aborters, so variable
 * state at abort points may differ — but that state gets rolled back.
 *)

Theory dftCorrectness
Ancestors
  dftFrontEquiv dftTopoSort dftWf dftDefs dftHelpers stateEquiv stateEquivProps passSimulationDefs
  venomExecSemantics venomWf venomState finite_map venomInst
  analysisSimDefs analysisSimProofsBase dftPermSim dftCompleteness dftPipelineInvar
  dftStructural dftIdempotent venomEffects sorting
  list rich_list combin arithmetic
  venomExecProps passSimulationProofs crossBlockSimProps
  dftBlockSim passSharedProps venomInstProps
  passSharedFrame passSharedDefs relation
  dftCanonicalDep allocaRemapSSA dftContraHelpers
  pred_set pair
Libs
  wordsLib BasicProvers dep_rewrite

(* ===== Structural: dft_block preserves bb_label ===== *)

Triviality dft_block_label[simp]:
  (dft_block order bb).bb_label = bb.bb_label
Proof
  simp[dft_block_def, LET_THM]
QED

(* ===== Structural: dft_process_one preserves MAP bb_label ===== *)

Triviality map_replace_label:
  !lbl bb bbs.
    bb.bb_label = lbl ==>
    MAP (\b. b.bb_label)
        (MAP (\b. if b.bb_label = lbl then dft_block order bb else b) bbs) =
    MAP (\b. b.bb_label) bbs
Proof
  Induct_on `bbs` >> simp[] >> rpt strip_tac >> rw[]
QED

Triviality dft_process_one_labels:
  !cfg lr fn st lbl labels.
    MAP (\b. b.bb_label) st.dls_blocks = labels ==>
    MAP (\b. b.bb_label) (FST (dft_process_one cfg lr fn st lbl)).dls_blocks =
    labels
Proof
  rpt strip_tac >>
  simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  imp_res_tac lookup_block_label >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[map_replace_label]
QED

(* ===== Structural: dft_loop_step preserves MAP bb_label ===== *)

Triviality dft_loop_step_labels:
  !cfg lr fn trip labels.
    MAP (\b. b.bb_label) (FST trip).dls_blocks = labels ==>
    MAP (\b. b.bb_label) (FST (dft_loop_step cfg lr fn trip)).dls_blocks =
    labels
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >>
  strip_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`,`labels`] mp_tac
    dft_process_one_labels >>
  simp[]
QED

(* ===== Structural: dft_fn preserves MAP bb_label (FUNPOW invariant) ===== *)

Triviality funpow_dft_loop_labels:
  !n cfg lr fn trip labels.
    MAP (\b. b.bb_label) (FST trip).dls_blocks = labels ==>
    MAP (\b. b.bb_label)
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks = labels
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_labels >>
  first_x_assum irule >> simp[]
QED

Theorem dft_fn_labels_map:
  !fn. MAP (\b. b.bb_label) (dft_fn fn).fn_blocks =
       MAP (\b. b.bb_label) fn.fn_blocks
Proof
  gen_tac >> rewrite_tac[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[funpow_dft_loop_labels]
QED

(* ===== Block-level: run_block equality ===== *)

(* A block is a permutation-variant of a block in fn: same phis,
   non-pseudos are from_block (= same or flip) of the original *)
Definition block_perm_of_def:
  block_perm_of fn bb <=>
    ?bb_orig. MEM bb_orig fn.fn_blocks /\
      bb.bb_label = bb_orig.bb_label /\
      FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions /\
      EVERY (\i. from_block bb_orig.bb_instructions i)
        (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
      PERM (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
           (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions))
End


(* ===== Permutation lift_result for run_insts ===== *)

(* Non-terminator, non-INVOKE instructions never produce Halt or IntRet *)
(* run_insts on non-term/non-INVOKE/non-ext-call list can only return OK, Abort, or Error *)
(* Factor identical result-shape proofs before specializing the opcodes. *)
Triviality dft_exec_helpers_result_shape:
  (!f inst s v vals a.
    exec_pure1 f inst s <> Halt v /\ exec_pure1 f inst s <> IntRet vals v /\
    exec_pure1 f inst s <> Abort a v) /\
  (!f inst s v vals a.
    exec_pure2 f inst s <> Halt v /\ exec_pure2 f inst s <> IntRet vals v /\
    exec_pure2 f inst s <> Abort a v) /\
  (!f inst s v vals a.
    exec_pure3 f inst s <> Halt v /\ exec_pure3 f inst s <> IntRet vals v /\
    exec_pure3 f inst s <> Abort a v) /\
  (!f inst s v vals a.
    exec_read0 f inst s <> Halt v /\ exec_read0 f inst s <> IntRet vals v /\
    exec_read0 f inst s <> Abort a v) /\
  (!f inst s v vals a.
    exec_read1 f inst s <> Halt v /\ exec_read1 f inst s <> IntRet vals v /\
    exec_read1 f inst s <> Abort a v) /\
  (!f inst s v vals a.
    exec_write2 f inst s <> Halt v /\ exec_write2 f inst s <> IntRet vals v /\
    exec_write2 f inst s <> Abort a v)
Proof
  rpt conj_tac >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def, AllCaseEqs()]
QED

(* Pre-compute: non-terminator non-INVOKE opcodes never produce Halt/IntRet.
   Uses same ML pre-computation pattern as dftPermSim.per_op_no_halt_abort. *)
local
  val nt_ni_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val ni = EVAL ``^op_tm <> INVOKE``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl ni)) T end
  ) (TypeBase.constructors_of ``:opcode``);

  val nt_ni_clauses = map (fn op_tm =>
    REWRITE_CONV [step_inst_base_def, instruction_accfupds,
                  TypeBase.case_def_of ``:opcode``]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) nt_ni_ops;

  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];

  val per_op_not_halt_intret = map (fn (op_tm, clause) =>
    prove(
      ``inst.inst_opcode = ^op_tm ==>
        (!v. step_inst_base inst st <> Halt v) /\
        (!vals v. step_inst_base inst st <> IntRet vals v)``,
      strip_tac >>
      `inst with inst_opcode := ^op_tm = inst`
        by simp[instruction_component_equality] >>
      pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
      ONCE_REWRITE_TAC [clause] >>
      simp[dft_exec_helpers_result_shape] >> simp exec_helper_defs)
  ) (ListPair.zip(nt_ni_ops, nt_ni_clauses));
in
  val step_inst_base_not_halt_intret_combined = LIST_CONJ per_op_not_halt_intret;
end

Triviality step_inst_base_not_halt_intret:
  !inst s.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    (!v. step_inst_base inst s <> Halt v) /\
    (!vals v. step_inst_base inst s <> IntRet vals v)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, step_inst_base_not_halt_intret_combined]
QED

(* Abort type is determined by opcode_fail_class for non-term/non-INVOKE *)
Triviality step_inst_base_abort_type:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (opcode_fail_class inst.inst_opcode = CanRevert ==> a = Revert_abort) /\
    (opcode_fail_class inst.inst_opcode = CanExHalt ==> a = ExHalt_abort)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[opcode_fail_class_def, is_terminator_def] >>
  gvs[step_inst_base_def, AllCaseEqs()]
QED

(* Two abort_compatible non-term/non-INVOKE instructions that both abort
   produce the same abort type *)
Triviality abort_compatible_same_type:
  !i1 i2 s1 s2 a1 a2 s1' s2'.
    abort_compatible i1.inst_opcode i2.inst_opcode /\
    ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE /\
    step_inst_base i1 s1 = Abort a1 s1' /\
    step_inst_base i2 s2 = Abort a2 s2' ==>
    a1 = a2
Proof
  rpt strip_tac >>
  fs[abort_compatible_def] >> gvs[]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >> (Cases_on `opcode_fail_class i1.inst_opcode` >> gvs[]
      >- metis_tac[step_inst_nofail_not_halt_abort]
      >- (`a1 = Revert_abort` by metis_tac[step_inst_base_abort_type] >>
          `a2 = Revert_abort` by metis_tac[step_inst_base_abort_type] >> gvs[])
      >- (`a1 = ExHalt_abort` by metis_tac[step_inst_base_abort_type] >>
          `a2 = ExHalt_abort` by metis_tac[step_inst_base_abort_type] >> gvs[])
      (* AnyFail: only INVOKE, excluded *)
      >> (Cases_on `i1.inst_opcode` >>
          gvs[opcode_fail_class_def]))
QED

(* step_inst_base abort always clears returndata for non-term/ext/INVOKE *)
Triviality step_inst_base_abort_returndata:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_returndata = []
Proof
  rpt strip_tac >>
  Cases_on `opcode_fail_class inst.inst_opcode` >> gvs[]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >- ((* CanRevert — only ASSERT has this class among non-term/non-ext *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def] >>
      gvs[step_inst_base_def, AllCaseEqs(),
          revert_state_def, set_returndata_def])
  >- ((* CanExHalt — INVALID, ASSERT_UNREACHABLE, RETURNDATACOPY *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def] >>
      gvs[step_inst_base_def, AllCaseEqs(),
          halt_state_def, set_returndata_def])
  >> ((* AnyFail — only INVOKE, excluded *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def])
QED

(* Non-terminator non-ext-call aborters always set returndata = [] *)
Theorem run_insts_abort_clears_returndata:
  !fuel ctx l s a s'.
    run_insts fuel ctx l s = Abort a s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
               i.inst_opcode <> INVOKE) l ==>
    s'.vs_returndata = []
Proof
  gen_tac >> gen_tac >> Induct >> rpt strip_tac >> gvs[run_insts_def] >>
  gvs[AllCaseEqs(), step_inst_non_invoke] >>
  metis_tac[step_inst_base_abort_returndata]
QED

(* For pairwise bi_independent permutations:
   - OK case: identical result (run_insts_perm_ok)
   - Non-OK case: both have same constructor, abort types match,
     returndata = [] (revert_equiv) *)
(* If instruction x OKs on s giving sx, and y is bi_independent of x,
   then y produces the same result constructor on sx as on s.
   Specifically: if y aborts on s, y also aborts on sx with the same type;
   if y doesn't error on s, y doesn't error on sx. *)
(* Helper: MEM (Var v) ops ==> MEM v (operand_vars ops) *)
Theorem MEM_operand_vars_iff:
  !ops v. MEM v (operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct >> simp[operand_vars_def] >>
  rpt gen_tac >> Cases_on `operand_var h` >> simp[operand_var_def] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

val MEM_Var_operand_vars =
  MEM_operand_vars_iff |> SPEC_ALL |> EQ_IMP_RULE |> snd
    |> GENL [``ops : operand list``, ``v : string``];

(* ML pre-computation: non-aborting opcodes can't produce Abort *)
local
  val nt_ni_nec_na_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val ni = EVAL ``^op_tm <> INVOKE``
        val nec = EVAL ``~is_ext_call_op ^op_tm``
        val na = EVAL ``~is_alloca_op ^op_tm``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl ni)) T
       andalso aconv (rhs (concl nec)) T andalso aconv (rhs (concl na)) T end
  ) (TypeBase.constructors_of ``:opcode``);
  val abort_ops = [``ASSERT``, ``ASSERT_UNREACHABLE``, ``RETURNDATACOPY``];
  val non_abort_ops = List.filter (fn op_tm =>
    not (List.exists (fn t => aconv t op_tm) abort_ops)) nt_ni_nec_na_ops;
  val nt_ni_clauses = map (fn op_tm =>
    REWRITE_CONV [step_inst_base_def, instruction_accfupds,
                  TypeBase.case_def_of ``:opcode``]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) non_abort_ops;
  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];
  val per_op_no_abort = map (fn (op_tm, clause) =>
    prove(
      ``inst.inst_opcode = ^op_tm ==>
        (!a s'. step_inst_base inst st <> Abort a s')``,
      strip_tac >>
      `inst with inst_opcode := ^op_tm = inst`
        by simp[instruction_component_equality] >>
      pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
      ONCE_REWRITE_TAC [clause] >>
      simp[dft_exec_helpers_result_shape] >> simp exec_helper_defs)
  ) (ListPair.zip(non_abort_ops, nt_ni_clauses));
in
  val step_inst_base_no_abort_combined = LIST_CONJ per_op_no_abort;
end

(* Helper: effects_independent with RETURNDATACOPY implies no returndata write *)
Triviality eff_ind_returndatacopy_no_write_rd:
  !op. effects_independent op RETURNDATACOPY ==>
       Eff_RETURNDATA NOTIN write_effects op
Proof
  rpt strip_tac >> gvs[effects_independent_def] >>
  spose_not_then assume_tac >>
  `Eff_RETURNDATA IN (read_effects RETURNDATACOPY UNION
                      write_effects RETURNDATACOPY)` by EVAL_TAC >>
  gvs[pred_setTheory.IN_DISJOINT] >>
  metis_tac[]
QED

(* Shared helper: if x OKs on s giving sx, and bi_independent x y,
   then y's operands evaluate identically on sx and s.
   This is THE core frame lemma for cross-instruction reasoning. *)
Triviality bi_ind_ok_preserves_eval_operand:
  !fuel ctx x y s sx op.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    MEM op y.inst_operands ==>
    eval_operand op sx = eval_operand op s
Proof
  rpt strip_tac >> fs[bi_independent_def] >>
  Cases_on `op` >> simp[eval_operand_def]
  (* Var case *)
  >- (`!v. ~MEM v x.inst_outputs ==> lookup_var v sx = lookup_var v s` by
        metis_tac[step_preserves_non_output_vars] >>
      first_x_assum irule >>
      `MEM s' (inst_uses y)` by
        (simp[inst_uses_def] >> irule MEM_Var_operand_vars >> simp[]) >>
      spose_not_then assume_tac >>
      `MEM s' (inst_defs x)` by fs[inst_defs_def] >>
      qpat_x_assum `DISJOINT (set (inst_defs x)) (set (inst_uses y))` mp_tac >>
      simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
      qexists_tac `s'` >> simp[])
  (* Label case *)
  >> (drule_all step_preserves_labels >> simp[])
QED

(* Corollary: all of y's operands evaluate the same on sx as s *)
Triviality bi_ind_ok_all_operands_same:
  !fuel ctx x y s sx.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx ==>
    MAP (\op. eval_operand op sx) y.inst_operands =
    MAP (\op. eval_operand op s) y.inst_operands
Proof
  rpt strip_tac >> irule MAP_CONG >> simp[] >>
  metis_tac[bi_ind_ok_preserves_eval_operand]
QED

(* Abort transfers between states with same operand values and returndata.
   If a non-term/non-alloca/non-ext/non-INVOKE instruction aborts from s,
   it also aborts (with the same abort type) from any s' that agrees on
   operand values and returndata. *)
Triviality step_inst_base_abort_transfer:
  !inst s s' a v.
    step_inst_base inst s = Abort a v /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s' = eval_operand op s) /\
    (inst.inst_opcode = RETURNDATACOPY ==>
     s'.vs_returndata = s.vs_returndata) ==>
    ?v'. step_inst_base inst s' = Abort a v'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      step_inst_base_no_abort_combined] >>
  (* Only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY remain *)
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  rpt strip_tac >> gvs[]
QED

Triviality bi_independent_cross_abort:
  !fuel ctx x y s sx a s_ab.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    step_inst fuel ctx y s = Abort a s_ab ==>
    ?s_ab'. step_inst fuel ctx y sx = Abort a s_ab' /\
            s_ab'.vs_returndata = [] /\ s_ab.vs_returndata = []
Proof
  rpt strip_tac >>
  drule bi_ind_ok_all_operands_same >>
  disch_then drule >> strip_tac >>
  fs[bi_independent_def] >>
  (* Convert step_inst -> step_inst_base *)
  qpat_x_assum `step_inst _ _ y _ = Abort _ _` mp_tac >>
  simp[step_inst_non_invoke] >> strip_tac >>
  simp[step_inst_non_invoke] >>
  (* Only 3 opcodes can abort *)
  Cases_on `y.inst_opcode` >>
  gvs[is_terminator_def, is_ext_call_op_def, is_alloca_op_def,
      step_inst_base_no_abort_combined] >>
  (* Shared pattern: decompose abort on s, rebuild on sx using same evals.
     ONCE_REWRITE_TAC[step_inst_base_def] unfolds once with known opcode. *)
  qpat_x_assum `step_inst_base _ s = _` mp_tac >>
  ONCE_REWRITE_TAC [step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  (* RETURNDATACOPY: also needs sx.vs_returndata = s.vs_returndata *)
  metis_tac[write_effects_sound_returndata,
            eff_ind_returndatacopy_no_write_rd]
QED

(* bi_independent is symmetric *)
Triviality bi_independent_sym:
  !x y. bi_independent x y ==> bi_independent y x
Proof
  rw[bi_independent_def, effects_independent_def, abort_compatible_def,
     gas_pair_def] >>
  metis_tac[pred_setTheory.DISJOINT_SYM]
QED

(* Cross-step preserves OK: if both succeed on s and are bi_independent,
   each also succeeds on the other's result state *)
Triviality bi_ind_cross_step_ok:
  !fuel ctx x y s sx.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    step_inst fuel ctx y s = OK (sy : venom_state) ==>
    ?v. step_inst_base y sx = OK v
Proof
  rpt strip_tac >>
  drule_all bi_ind_ok_all_operands_same >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_alloca_op x.inst_opcode /\
   ~is_ext_call_op x.inst_opcode /\ x.inst_opcode <> INVOKE /\
   ~is_terminator y.inst_opcode /\ ~is_alloca_op y.inst_opcode /\
   ~is_ext_call_op y.inst_opcode /\ y.inst_opcode <> INVOKE /\
   effects_independent x.inst_opcode y.inst_opcode` by
    fs[bi_independent_def] >>
  `step_inst_base y s = OK sy` by fs[step_inst_non_invoke] >>
  `sx.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_inst_preserves_prev_bb, step_inst_non_invoke] >>
  `sx.vs_params = s.vs_params` by
    metis_tac[step_preserves_params, step_inst_non_invoke] >>
  qspecl_then [`y`,`s`,`sy`,`sx`] mp_tac step_inst_base_ok_transfer >>
  simp[] >> disch_then irule >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
      simp[listTheory.MAP_EQ_f])
  >> (strip_tac >>
      `Eff_RETURNDATA NOTIN write_effects x.inst_opcode` by
        metis_tac[eff_ind_returndatacopy_no_write_rd] >>
      metis_tac[write_effects_sound_returndata, step_inst_non_invoke])
QED

(* Non-terminator, non-INVOKE bi_independent instructions never Halt or IntRet *)
Triviality bi_independent_no_halt_intret:
  !fuel ctx x y s.
    bi_independent x y ==>
    (!v. step_inst fuel ctx x s <> Halt v) /\
    (!v s'. step_inst fuel ctx x s <> IntRet v s') /\
    (!v. step_inst fuel ctx y s <> Halt v) /\
    (!v s'. step_inst fuel ctx y s <> IntRet v s')
Proof
  rw[bi_independent_def, step_inst_non_invoke] >>
  metis_tac[step_inst_base_not_halt_intret]
QED

(* Swap case helper: two bi_independent non-erroring instructions produce
   lift_result equivalent composed results. *)
Triviality step_swap_lift:
  !fuel ctx x y s.
    bi_independent x y /\
    (!e. step_inst fuel ctx x s <> Error e) /\
    (!e. step_inst fuel ctx y s <> Error e) ==>
    lift_result (=) (=) revert_equiv
      (case step_inst fuel ctx x s of
         OK sx => step_inst fuel ctx y sx
       | Halt v => Halt v | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s' | Error e => Error e)
      (case step_inst fuel ctx y s of
         OK sy => step_inst fuel ctx x sy
       | Halt v => Halt v | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s' | Error e => Error e)
Proof
  rpt strip_tac >>
  (* Get specific no-Halt/IntRet facts that gvs can use *)
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`] mp_tac
    bi_independent_no_halt_intret >> (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx x s` >> gvs[] >>
  Cases_on `step_inst fuel ctx y s` >> gvs[]
  (* OK x, OK y: commute via independent_commute_eq *)
  >- suspend "ok_ok"
  (* OK x, Abort y: cross_abort *)
  >- (drule_all bi_independent_cross_abort >> strip_tac >>
      simp[lift_result_def, revert_equiv_def])
  (* Abort x, OK y: symmetric — use cross_abort with roles swapped *)
  >- (rename1 `step_inst _ _ y s = OK sy` >>
      rename1 `step_inst _ _ x s = Abort abt sab` >>
      `bi_independent y x` by metis_tac[bi_independent_sym] >>
      qspecl_then [`fuel`,`ctx`,`y`,`x`,`s`,`sy`,`abt`,`sab`] mp_tac
        bi_independent_cross_abort >>
      (impl_tac >- simp[]) >> strip_tac >>
      simp[lift_result_def, revert_equiv_def])
  (* Abort x, Abort y: same type + both clear returndata *)
  >> (simp[lift_result_def, revert_equiv_def] >>
      fs[bi_independent_def] >>
      conj_tac
      >- metis_tac[abort_compatible_same_type, step_inst_non_invoke]
      >> metis_tac[step_inst_base_abort_returndata, step_inst_non_invoke])
QED

Resume step_swap_lift[ok_ok]:
  rename1 `step_inst _ _ x s = OK sx` >>
  rename1 `step_inst _ _ y s = OK sy` >>
  fs[bi_independent_def] >>
  simp[step_inst_non_invoke] >>
  (* Cross-steps both give OK (by bi_ind_cross_step_ok) *)
  `?vy. step_inst_base y sx = OK vy` by
    metis_tac[bi_ind_cross_step_ok, bi_independent_def] >>
  `?vx. step_inst_base x sy = OK vx` by
    metis_tac[bi_ind_cross_step_ok, bi_independent_sym, bi_independent_def] >>
  simp[lift_result_def] >>
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`,`sx`,`sy`] mp_tac
    independent_commute_eq >>
  simp[step_inst_non_invoke]
QED

Finalise step_swap_lift

(* bi_independent OK step preserves non-Error property *)
Triviality bi_ind_ok_preserves_no_error:
  !fuel ctx x i s s'.
    bi_independent x i /\
    step_inst fuel ctx x s = OK s' /\
    (!e. step_inst fuel ctx i s <> Error e) ==>
    (!e. step_inst fuel ctx i s' <> Error e)
Proof
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx i s` >> gvs[] >>
  TRY (drule_all bi_ind_cross_step_ok >> strip_tac >>
       gvs[bi_independent_def, step_inst_non_invoke] >> NO_TAC) >>
  TRY (drule_all bi_independent_cross_abort >> strip_tac >>
       gvs[bi_independent_def, step_inst_non_invoke] >> NO_TAC) >>
  qspecl_then [`fuel`,`ctx`,`x`,`i`,`s`] mp_tac
    bi_independent_no_halt_intret >> simp[]
QED

(* Stepping a bi-independent instruction preserves no-Error in both
   directions. Subsumes bi_ind_ok_preserves_no_error. *)
Triviality bi_ind_ok_no_error_iff:
  !fuel ctx x i s s'.
    bi_independent x i /\
    step_inst fuel ctx x s = OK s' ==>
    ((!e. step_inst fuel ctx i s <> Error e) <=>
     (!e. step_inst fuel ctx i s' <> Error e))
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  (* Forward: no-Error on s → no-Error on s' *)
  >- metis_tac[bi_ind_ok_preserves_no_error]
  (* Reverse: no-Error on s' → no-Error on s.
     We show step_inst i s gives the same constructor as step_inst i s'
     (which is not Error). Uses contrapositive on constructor case analysis. *)
  >> (rpt strip_tac >>
      (* Extract flags from bi_independent for BOTH x and i *)
      `~is_terminator x.inst_opcode /\ ~is_alloca_op x.inst_opcode /\
       ~is_ext_call_op x.inst_opcode /\ x.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
       ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE` by
        (fs[bi_independent_def]) >>
      (* Derive operand equivalence *)
      drule_all bi_ind_ok_all_operands_same >> strip_tac >>
      (* Get state field preservation *)
      `s'.vs_prev_bb = s.vs_prev_bb` by
        (qspecl_then [`fuel`,`ctx`,`x`,`s`,`s'`] mp_tac
           step_inst_preserves_prev_bb >> simp[]) >>
      `s'.vs_params = s.vs_params` by
        (qspecl_then [`fuel`,`ctx`,`x`,`s`,`s'`] mp_tac
           step_preserves_params >> simp[]) >>
      (* Returndata: conditional on i being RETURNDATACOPY *)
      `i.inst_opcode = RETURNDATACOPY ==>
       s'.vs_returndata = s.vs_returndata` by
        (strip_tac >>
         `Eff_RETURNDATA NOTIN write_effects x.inst_opcode` by
           metis_tac[eff_ind_returndatacopy_no_write_rd,
                     bi_independent_def] >>
         metis_tac[write_effects_sound_returndata]) >>
      suspend "reverse")
QED

Resume bi_ind_ok_no_error_iff[reverse]:
  (* Convert step_inst → step_inst_base, derive pointwise operand equality *)
  fs[step_inst_non_invoke] >>
  `!op. MEM op i.inst_operands ==>
        eval_operand op s' = eval_operand op s` by (
    qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
    simp[listTheory.MAP_EQ_f]) >>
  Cases_on `step_inst_base i s'` >> gvs[] >>
  TRY (metis_tac[step_inst_base_not_halt_intret])
  (* OK case: transfer OK from s' to s, contradicts Error *)
  >- (qspecl_then [`i`,`s'`,`v`,`s`] mp_tac
        passSharedPropsTheory.step_inst_base_ok_transfer >>
      simp[] >> strip_tac >> gvs[])
  (* Abort case: for each aborting opcode, unfold step_inst_base on both
     states; operand equality ensures same branch taken *)
  >> (Cases_on `i.inst_opcode` >>
      gvs[is_terminator_def, is_ext_call_op_def, is_alloca_op_def,
          step_inst_base_no_abort_combined] >>
      qpat_x_assum `step_inst_base _ s' = Abort _ _` mp_tac >>
      qpat_x_assum `step_inst_base _ s = Error _` mp_tac >>
      ntac 2 (ONCE_REWRITE_TAC [step_inst_base_def]) >>
      every_case_tac >> gvs[] >> IF_CASES_TAC >> gvs[])
QED

Finalise bi_ind_ok_no_error_iff;

(* PERM preserves pairwise_bi_independent and EVERY (bi_independent x) *)
Triviality perm_preserves_pairwise_bi_ind:
  !l1 l2.
    PERM l1 l2 ==>
    (pairwise_bi_independent l1 ==> pairwise_bi_independent l2) /\
    (!x. EVERY (bi_independent x) l1 ==> EVERY (bi_independent x) l2)
Proof
  ho_match_mp_tac PERM_IND >>
  rw[pairwise_bi_independent_def, EVERY_DEF] >>
  gvs[pairwise_bi_independent_def, EVERY_DEF] >>
  metis_tac[bi_independent_sym]
QED

(* Stepping a bi-independent instruction preserves no-error for an entire list *)
Triviality bi_ind_list_preserves_no_error:
  !fuel ctx x l s s'.
    EVERY (bi_independent x) l /\
    step_inst fuel ctx x s = OK s' /\
    EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l ==>
    EVERY (\i. !e. step_inst fuel ctx i s' <> Error e) l
Proof
  rpt strip_tac >> gvs[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  irule bi_ind_ok_preserves_no_error >>
  qexistsl [`s`, `x`] >> simp[]
QED

(* Main PERM lift_result lemma — uses perm_preserves_pairwise_bi_ind *)
Theorem run_insts_perm_lift_strong:
  !l1 l2.
    PERM l1 l2 ==>
    !fuel ctx s.
       pairwise_bi_independent l1 /\
       EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l1 ==>
       lift_result (=) (=) revert_equiv
         (run_insts fuel ctx l1 s) (run_insts fuel ctx l2 s)
Proof
  ho_match_mp_tac PERM_STRONG_IND >> rpt conj_tac
  (* nil *)
  >- simp[run_insts_def, lift_result_def]
  (* cons *)
  >- suspend "cons"
  (* swap *)
  >- suspend "swap"
  (* trans *)
  >> suspend "trans"
QED

Resume run_insts_perm_lift_strong[cons]:
  rpt strip_tac >>
  gvs[pairwise_bi_independent_def, EVERY_DEF, run_insts_def] >>
  Cases_on `step_inst fuel ctx x s` >> gvs[lift_result_def]
  >- (first_x_assum $ qspecl_then [`fuel`,`ctx`,`v`] mp_tac >>
      impl_tac
      >- suspend "cons_no_err"
      >> simp[])
  >> simp[revert_equiv_def]
QED

Resume run_insts_perm_lift_strong[cons_no_err]:
  irule bi_ind_list_preserves_no_error >>
  qexistsl [`s`, `x`] >> simp[]
QED

Resume run_insts_perm_lift_strong[swap]:
  rpt strip_tac >>
  gvs[pairwise_bi_independent_def, EVERY_DEF, run_insts_def] >>
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`] mp_tac
    bi_independent_no_halt_intret >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx x s` >> gvs[] >>
  Cases_on `step_inst fuel ctx y s` >> gvs[]
  (* OK/OK *)
  >- suspend "swap_ok_ok"
  (* OK/Abort *)
  >- (gvs[step_inst_non_invoke] >>
      drule_all bi_independent_cross_abort >>
      strip_tac >> gvs[lift_result_def, revert_equiv_def])
  (* Abort/OK *)
  >- (`bi_independent y x` by metis_tac[bi_independent_sym] >>
      gvs[step_inst_non_invoke] >>
      drule_all bi_independent_cross_abort >>
      strip_tac >> gvs[lift_result_def, revert_equiv_def])
  (* Abort/Abort *)
  >> gvs[bi_independent_def, step_inst_non_invoke,
         lift_result_def, revert_equiv_def] >>
     metis_tac[step_inst_base_abort_returndata,
               abort_compatible_same_type]
QED

Resume run_insts_perm_lift_strong[swap_ok_ok]:
  (* 1. Cross-step OK results — keep bi_independent intact for helpers *)
  `?s12. step_inst_base y v = OK s12` by
    metis_tac[bi_ind_cross_step_ok] >>
  `bi_independent y x` by metis_tac[bi_independent_sym] >>
  `?s21. step_inst_base x v' = OK s21` by
    metis_tac[bi_ind_cross_step_ok] >>
  (* 2. Convert step_inst_base to step_inst using ¬INVOKE from bi_independent *)
  `y.inst_opcode <> INVOKE /\ x.inst_opcode <> INVOKE` by
    fs[bi_independent_def] >>
  `step_inst fuel ctx y v = OK s12` by simp[step_inst_non_invoke] >>
  `step_inst fuel ctx x v' = OK s21` by simp[step_inst_non_invoke] >>
  (* 3. No-error transfer: s -> v (through x) -> s12 (through y) *)
  `EVERY (\i. !e. step_inst fuel ctx i v <> Error e) l1` by
    (irule bi_ind_list_preserves_no_error >>
     qexistsl [`s`, `x`] >> simp[]) >>
  `EVERY (\i. !e. step_inst fuel ctx i s12 <> Error e) l1` by
    (irule bi_ind_list_preserves_no_error >>
     qexistsl [`v`, `y`] >> simp[]) >>
  (* 4. Diamond: s12 = s21, using independent_commute_eq *)
  `s12 = s21` by
    (qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`,`v`,`v'`,`s12`,`s21`] mp_tac
       independent_commute_eq >>
     (impl_tac >- gvs[bi_independent_def, step_inst_non_invoke]) >>
     simp[]) >>
  gvs[]
QED

Resume run_insts_perm_lift_strong[trans]:
  rpt strip_tac >>
  imp_res_tac perm_preserves_pairwise_bi_ind >>
  `EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l1'` by
    metis_tac[PERM_EVERY] >>
  `lift_result $= $= revert_equiv
     (run_insts fuel ctx l1 s) (run_insts fuel ctx l1' s)` by
    metis_tac[] >>
  `lift_result $= $= revert_equiv
     (run_insts fuel ctx l1' s) (run_insts fuel ctx l2 s)` by
    metis_tac[] >>
  irule (SRULE [] lift_result_trans_proof) >>
  simp[revert_equiv_def] >>
  qexists `run_insts fuel ctx l1' s` >> simp[]
QED

Finalise run_insts_perm_lift_strong

(* When both orderings abort and all non-NoFail instructions are dep-chained,
   the abort types must match. Argument: the aborters are both non-NoFail,
   both MEM of the same set (PERM), hence dep-chained, so topo_sorted forces
   same relative order. The abort type is determined by the fail class of the
   aborter, and dep-chained non-NoFail instructions that both abort must have
   abort_compatible fail classes.
   Simpler: bi_independent (from non-dep) requires abort_compatible, and the
   chaining hypothesis ensures non-NoFail pairs ARE dep-related. Since the
   aborter's fail class determines the abort type, and all non-NoFail
   instructions in l have consistent fail class (being chained), a = a'. *)

(* Case-split approach: OK case by run_insts_topo_equiv (symmetric),
   non-OK case by structure (no Halt/IntRet, both Abort → revert_equiv).
   Requires: no Error in either execution (added as hypothesis).
   The non-NoFail chaining hypothesis ensures abort type consistency. *)
(* Topo-sorted permutations produce same OK result and revert_equiv Abort.
   Does NOT claim abort types match — that requires the abort chaining
   property from build_full_eda, proved at the exec_block level. *)
Theorem run_insts_topo_lift:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> bi_independent x y) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l1 /\
    (!e. run_insts fuel ctx l1 s <> Error e) /\
    (!e. run_insts fuel ctx l2 s <> Error e) ==>
    (* OK case: identical results *)
    (!r. run_insts fuel ctx l1 s = OK r ==>
         run_insts fuel ctx l2 s = OK r) /\
    (!r. run_insts fuel ctx l2 s = OK r ==>
         run_insts fuel ctx l1 s = OK r) /\
    (* Same constructor: both OK, both Abort, or both Error *)
    (?r. run_insts fuel ctx l1 s = OK r) =
    (?r. run_insts fuel ctx l2 s = OK r) /\
    (* Abort case: revert_equiv *)
    (!a1 s1 a2 s2.
       run_insts fuel ctx l1 s = Abort a1 s1 /\
       run_insts fuel ctx l2 s = Abort a2 s2 ==>
       revert_equiv s1 s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt conj_tac
  >- suspend "fwd"
  >- suspend "rev"
  >- suspend "iff"
  >> suspend "abort"
QED

Resume run_insts_topo_lift[fwd]:
  rpt strip_tac >> irule run_insts_topo_equiv >>
  qexistsl [`dep`, `l1`] >> simp[]
QED

Resume run_insts_topo_lift[rev]:
  rpt strip_tac >> irule run_insts_topo_equiv >>
  qexistsl [`dep`, `l2`] >> simp[] >>
  `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
  simp[] >> metis_tac[ALL_DISTINCT_PERM, PERM_SYM]
QED

Resume run_insts_topo_lift[iff]:
  eq_tac >> rpt strip_tac >> gvs[]
  >- (`run_insts fuel ctx l2 s = OK r` by
        (irule run_insts_topo_equiv >>
         qexistsl [`dep`, `l1`] >> simp[]) >>
      metis_tac[])
  >> (`run_insts fuel ctx l1 s = OK r` by
        (irule run_insts_topo_equiv >>
         qexistsl [`dep`, `l2`] >> simp[] >>
         `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
         simp[] >> metis_tac[ALL_DISTINCT_PERM, PERM_SYM]) >>
      metis_tac[])
QED

Resume run_insts_topo_lift[abort]:
  rpt strip_tac >> simp[revert_equiv_def] >>
  `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l2` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[run_insts_abort_clears_returndata]
QED

Finalise run_insts_topo_lift

(* from_block gives step_inst equivalence (uses strengthened from_block) *)
Theorem all_distinct_map_mem_inj:
  !f l a b. ALL_DISTINCT (MAP f l) /\ MEM a l /\ MEM b l /\
            f a = f b ==> a = b
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

(* Core block-level theorem: original block and a block_perm_of variant
   produce lift_result-equivalent exec_block results.
   bb must be the original (from fn.fn_blocks); bb' is the variant.
   bb_well_formed bb' needed because exec_block behavior depends on
   terminator position — without it, exec_block might exit early.
   NOTE: Two arbitrary block_perm_of blocks can reorder aborters,
   giving different abort types. Comparing to original avoids this
   because abort chaining preserves aborter order. *)
(* Sub-lemma: extract body (non-pseudo, non-terminator) instructions *)
(* For a well-formed block, the body is the middle section:
   instructions = phis ++ body ++ [terminator] *)
Definition block_body_def:
  block_body bb =
    FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode)
      bb.bb_instructions
End

(* EDA-level commutativity: either ext_bi_independent (handles effects_independent)
   or both effect-free with disjoint defs/uses (handles memory-read-only gap).
   This is the widest predicate under which two non-pseudo body instructions
   can be swapped while preserving the OK result. *)
Definition eda_commutes_def:
  eda_commutes i1 i2 <=>
    ext_bi_independent i1 i2 \/
    (is_effect_free_op i1.inst_opcode /\ is_effect_free_op i2.inst_opcode /\
     DISJOINT (set (inst_defs i1)) (set (inst_uses i2)) /\
     DISJOINT (set (inst_defs i2)) (set (inst_uses i1)) /\
     DISJOINT (set (inst_defs i1)) (set (inst_defs i2)) /\
     ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode)
End

(* Choose an original instruction from l1 for each instruction in l2 *)
Definition choose_original_def:
  choose_original l1 i = @j. MEM j l1 /\ j.inst_id = i.inst_id
End

Triviality choose_original_correct:
  !l1 i j.
    MEM j l1 /\ j.inst_id = i.inst_id ==>
    MEM (choose_original l1 i) l1 /\
    (choose_original l1 i).inst_id = i.inst_id
Proof
  rw[choose_original_def] >> SELECT_ELIM_TAC >> metis_tac[]
QED

Triviality choose_original_unique:
  !l1 i j.
    MEM j l1 /\ j.inst_id = i.inst_id /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) ==>
    choose_original l1 i = j
Proof
  rw[choose_original_def] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  metis_tac[all_distinct_map_mem_inj]
QED

(* EDA dependency relation: x depends on y iff some inst with y's inst_id
   is in x's dep list. Defined via inst_ids for transferability. *)
Definition eda_dep_def:
  eda_dep eda x y <=>
    ?d. MEM d (case FLOOKUP eda x.inst_id of NONE => [] | SOME ds => ds) /\
        d.inst_id = y.inst_id
End

(* eda_topo_compatible implies topo_sorted for non-pseudo instructions *)
Triviality eda_topo_compatible_topo_sorted:
  !bi eda order.
    eda_topo_compatible bi eda order /\
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    topo_sorted (eda_dep eda)
      (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)
Proof
  rw[topo_sorted_def, eda_dep_def] >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode /\
                                 ~is_terminator i.inst_opcode) bi` >>
  spose_not_then strip_assume_tac >>
  (* d witnesses the eda_dep: MEM d (FLOOKUP eda fl[i].inst_id), d.inst_id = fl[j].inst_id *)
  (* d is MEM bi and non-pseudo from eda_wf *)
  `MEM d bi /\ ~is_pseudo d.inst_opcode` by
    (fs[eda_wf_def] >>
     Cases_on `FLOOKUP eda (EL i fl).inst_id` >> gvs[] >>
     metis_tac[]) >>
  (* fl elements are in bi *)
  `MEM (EL j fl) bi` by
    (`MEM (EL j fl) fl` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
     fs[Abbr `fl`, MEM_FILTER]) >>
  (* d = fl[j] by ALL_DISTINCT inst_ids *)
  `d = EL j fl` by metis_tac[all_distinct_map_mem_inj] >>
  (* fl[i] is MEM bi and non-pseudo *)
  `MEM (EL i fl) bi /\ ~is_pseudo (EL i fl).inst_opcode` by
    (`MEM (EL i fl) fl` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
     fs[Abbr `fl`, MEM_FILTER]) >>
  (* fl[j] is in inst_all_deps of fl[i] (via eda deps) *)
  `MEM (EL j fl) (inst_all_deps bi order eda (EL i fl))` by
    (simp[inst_all_deps_def, LET_THM, MEM_nub] >>
     Cases_on `FLOOKUP eda (EL i fl).inst_id` >> gvs[]) >>
  (* eda_topo_compatible: dep fl[j] before inst fl[i] in bi *)
  `?p q. p < q /\ q < LENGTH bi /\ p < LENGTH bi /\
         EL p bi = EL j fl /\ EL q bi = EL i fl` by
    (fs[eda_topo_compatible_def] >>
     first_x_assum (qspecl_then [`EL i fl`, `EL j fl`] mp_tac) >>
     simp[]) >>
  (* filter_el_mono: fl[i] before fl[j] in bi *)
  `?a b. a < b /\ b < LENGTH bi /\
         EL a bi = EL i fl /\ EL b bi = EL j fl` by
    (qspecl_then [`\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode`,
                  `bi`, `i`, `j`] mp_tac filter_el_mono >>
     simp[Abbr `fl`]) >>
  (* ALL_DISTINCT: bi[a] = bi[q] = fl[i], bi[b] = bi[p] = fl[j] *)
  `a = q /\ b = p` by
    (`a < LENGTH bi` by simp[] >>
     `EL a (MAP (\i. i.inst_id) bi) = EL q (MAP (\i. i.inst_id) bi)` by
       simp[EL_MAP] >>
     `EL b (MAP (\i. i.inst_id) bi) = EL p (MAP (\i. i.inst_id) bi)` by
       simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  (* a < b = p < q = a — contradiction *)
  simp[]
QED

(* Combined dependency: eda + data deps + output aliasing.
   full_dep eda x y means "x depends on y" = "y must come before x" *)
Definition full_dep_def:
  full_dep eda x y <=>
    eda_dep eda x y \/
    ~DISJOINT (set (inst_uses x)) (set (inst_defs y)) \/
    ~DISJOINT (set (inst_defs x)) (set (inst_defs y))
End

(* ===== Barrier TC connectivity ===== *)

(* Subsequent EDA passes are monotone: add_chain_deps, add_barrier_deps, etc.
   only add entries, never remove existing deps. *)

(* FOLDL (\ds p. if MEM p ds then ds else p :: ds) preserves existing members *)
Theorem foldl_add_preserves_mem:
  !ps ds x. MEM x ds ==>
    MEM x (FOLDL (\ds p. if MEM p ds then ds else p :: ds) ds ps)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  IF_CASES_TAC >> simp[]
QED

(* add_deps_from_barrier preserves existing deps — let-expanded FOLDL body *)
Theorem add_deps_from_barrier_foldl_mono:
  !non_phis acc prev_insts id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else
        (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  irule foldl_add_preserves_mem >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

Theorem add_deps_from_barrier_mono:
  !bi eda id d.
    MEM d (case FLOOKUP eda id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (add_deps_from_barrier bi eda) id of
             NONE => [] | SOME ds => ds)
Proof
  rw[add_deps_from_barrier_def, LET_THM] >>
  irule add_deps_from_barrier_foldl_mono >> simp[]
QED

(* add_deps_on_barrier: let-expanded FOLDL mono *)
Theorem add_deps_on_barrier_foldl_mono:
  !non_phis acc last_bar id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then
        (acc, SOME inst)
      else
        (acc |+ (inst.inst_id,
           case last_bar of
             NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
           | SOME b =>
               if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
               then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
               else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
         last_bar))
    (acc, last_bar) non_phis)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `last_bar` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

(* add_chain_deps: let-expanded FOLDL mono *)
Theorem add_chain_deps_foldl_mono:
  !matching acc prev id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, prev) inst.
      (acc |+ (inst.inst_id,
         case prev of
           NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
         | SOME p =>
             if MEM p (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             else p :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
       SOME inst))
    (acc, prev) matching)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `prev` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

Theorem add_chain_deps_mono:
  !P bi eda id d.
    MEM d (case FLOOKUP eda id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (add_chain_deps P bi eda) id of
             NONE => [] | SOME ds => ds)
Proof
  rw[add_chain_deps_def, LET_THM] >>
  irule add_chain_deps_foldl_mono >> simp[]
QED

(* Combined: add_deps_from_barrier result survives to build_full_eda *)
Theorem build_full_eda_mono_from_barrier:
  !bi id d.
    MEM d (case FLOOKUP
      (add_deps_from_barrier bi
        (add_deps_on_barrier bi
          (add_abort_deps bi (build_eda bi)))) id of
             NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (build_full_eda bi) id of NONE => [] | SOME ds => ds)
Proof
  rw[build_full_eda_def, add_barrier_deps_def, add_alloca_deps_def] >>
  irule add_chain_deps_mono >> simp[]
QED

(* add_deps_on_barrier result survives through add_deps_from_barrier to build_full_eda *)
Theorem build_full_eda_mono_on_barrier:
  !bi id d.
    MEM d (case FLOOKUP
      (add_deps_on_barrier bi
        (add_abort_deps bi (build_eda bi))) id of
             NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (build_full_eda bi) id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> irule build_full_eda_mono_from_barrier >>
  irule add_deps_from_barrier_mono >> simp[]
QED

(* ===== FOLDL add_if_absent: prev members end up in result ===== *)
Triviality foldl_add_includes_prev:
  !ps ds x. MEM x ps ==>
    MEM x (FOLDL (\ds p. if MEM p ds then ds else p :: ds) ds ps)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  TRY (Cases_on `MEM h ds` >> simp[foldl_add_preserves_mem] >> NO_TAC) >>
  first_x_assum irule >> simp[]
QED

(* Helper: barrier x gets all prev_insts when processed *)
Theorem from_barrier_at_barrier:
  !non_phis acc prev_insts x suffix.
    non_phis = x :: suffix /\ is_barrier x ==>
    !y. MEM y prev_insts ==>
    MEM y (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis)) x.inst_id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> gvs[] >> simp[FOLDL] >>
  irule add_deps_from_barrier_foldl_mono >>
  simp[FLOOKUP_UPDATE] >>
  irule foldl_add_includes_prev >> simp[]
QED

(* Main spec: after processing, barrier x has all preceding non-phis as deps.
   Split-based formulation: non_phis = prefix ++ [x] ++ suffix *)
Triviality add_deps_from_barrier_foldl_spec:
  !prefix x suffix acc prev_insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prev_insts ++ prefix ++ [x] ++ suffix)) /\
    is_barrier x ==>
    !y. MEM y (prev_insts ++ prefix) ==>
    MEM y (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
    (acc, prev_insts) (prefix ++ [x] ++ suffix))) x.inst_id of
      NONE => [] | SOME ds => ds)
Proof
  Induct >> rpt strip_tac
  >- suspend "base"
  >> suspend "step"
QED

Resume add_deps_from_barrier_foldl_spec[base]:
  gvs[] >>
  irule (SRULE [] from_barrier_at_barrier) >> simp[]
QED

Resume add_deps_from_barrier_foldl_spec[step]:
  (* Unfold one FOLDL step for h, then apply IH.
     Both barrier/non-barrier cases: prev_insts becomes prev_insts ++ [h],
     acc may change. IH universally quantifies both. *)
  simp[FOLDL] >>
  Cases_on `is_barrier h` >> simp[] >> (
    (* In both cases, apply IH with prev_insts := prev_insts ++ [h] *)
    first_x_assum irule >> simp[] >>
    fs[ALL_DISTINCT_APPEND, MAP_APPEND, MEM_MAP, MEM_APPEND] >>
    metis_tac[])
QED

Finalise add_deps_from_barrier_foldl_spec

(* Helper: when processing non-barrier x with last_bar = SOME b,
   b ends up in x's deps in the result acc *)
Theorem on_barrier_at_inst:
  !x suffix acc b.
    ~is_barrier x ==>
    MEM b (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then (acc, SOME inst)
      else (acc |+ (inst.inst_id,
              case last_bar of
                NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
              | SOME b =>
                  if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
           last_bar))
    (acc, SOME b) (x :: suffix))) x.inst_id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> simp[FOLDL] >>
  irule add_deps_on_barrier_foldl_mono >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `MEM b (case FLOOKUP acc x.inst_id of NONE => [] | SOME ds => ds)` >>
  simp[]
QED

(* Main spec: if prefix contains a barrier and x is non-barrier,
   then the last barrier in prefix is in x's deps.
   FOLDL processes prefix ++ [x] ++ suffix starting with (acc, last_bar_init). *)
Theorem add_deps_on_barrier_foldl_spec:
  !prefix x suffix acc last_bar_init b.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [x] ++ suffix)) /\
    ~is_barrier x /\
    (case FILTER is_barrier prefix of
       [] => last_bar_init = SOME b
     | bs => LAST bs = b) ==>
    MEM b (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then (acc, SOME inst)
      else (acc |+ (inst.inst_id,
              case last_bar of
                NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
              | SOME b =>
                  if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
           last_bar))
    (acc, last_bar_init) (prefix ++ [x] ++ suffix))) x.inst_id of
      NONE => [] | SOME ds => ds)
Proof
  Induct >> rpt strip_tac
  >- ((* Base: prefix = [], last_bar_init = SOME b *)
      gvs[] >>
      qspecl_then [`x`, `suffix`, `acc`, `b`] mp_tac on_barrier_at_inst >>
      simp[])
  >> ((* Step: unfold one FOLDL step for h, apply IH *)
      Cases_on `is_barrier h` >> gvs[FILTER] >>
      simp[FOLDL] >>
      first_x_assum irule >> simp[] >>
      fs[ALL_DISTINCT_APPEND, MAP_APPEND, MEM_MAP, MEM_APPEND] >>
      Cases_on `FILTER is_barrier prefix` >> simp[])
QED

(* MAP choose_original preserves PERM of inst_ids *)
Triviality map_choose_original_perm:
  !l1 l2.
    PERM (MAP (\i. i.inst_id) l1) (MAP (\i. i.inst_id) l2) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) ==>
    PERM l1 (MAP (choose_original l1) l2)
Proof
  rpt strip_tac >>
  MATCH_MP_TAC PERM_ALL_DISTINCT >> rpt conj_tac
  >- suspend "ad_l1"
  >- suspend "ad_map"
  >> suspend "mem_eq"
QED

Resume map_choose_original_perm[ad_l1]:
  metis_tac[ALL_DISTINCT_MAP]
QED

Resume map_choose_original_perm[ad_map]:
  (`ALL_DISTINCT (MAP (\i. i.inst_id) l2)` by
    metis_tac[ALL_DISTINCT_PERM]) >>
  (`ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_MAP]) >>
  irule ALL_DISTINCT_MAP_INJ >> conj_tac
  >- (rpt strip_tac >>
      `(choose_original l1 x).inst_id = x.inst_id` by
        (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
      `(choose_original l1 y).inst_id = y.inst_id` by
        (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
      `x.inst_id = y.inst_id` by metis_tac[] >>
      metis_tac[all_distinct_map_mem_inj])
  >- simp[]
QED

Resume map_choose_original_perm[mem_eq]:
  gen_tac >> eq_tac >> strip_tac
  >- suspend "fwd"
  >> suspend "bwd"
QED

Resume map_choose_original_perm[fwd]:
  (* MEM x l1 → MEM x (MAP (choose_original l1) l2) *)
  simp[MEM_MAP] >>
  drule PERM_MEM_EQ >>
  disch_then (qspec_then `x.inst_id` mp_tac) >>
  simp[MEM_MAP] >>
  disch_then (mp_tac o #1 o EQ_IMP_RULE) >>
  (impl_tac >- (qexists `x` >> simp[])) >>
  strip_tac >> rename1 `MEM z l2` >>
  qexists `z` >> conj_tac >- metis_tac[choose_original_unique] >>
  simp[]
QED

Resume map_choose_original_perm[bwd]:
  (* MEM x (MAP (choose_original l1) l2) → MEM x l1 *)
  fs[MEM_MAP] >> metis_tac[choose_original_correct]
QED

Finalise map_choose_original_perm

(* topo_sorted transfers through choose_original mapping *)
Triviality map_choose_original_topo_sorted:
  !l1 l2 dep.
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    topo_sorted dep l2 /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) /\
    (* dep only depends on inst_id *)
    (!x y x' y'. x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
       (dep x y <=> dep x' y')) ==>
    topo_sorted dep (MAP (choose_original l1) l2)
Proof
  rw[topo_sorted_def, LENGTH_MAP] >>
  simp[EL_MAP] >>
  `MEM (EL i l2) l2` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  `MEM (EL j l2) l2` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
  `(choose_original l1 (EL i l2)).inst_id = (EL i l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `(choose_original l1 (EL j l2)).inst_id = (EL j l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  metis_tac[]
QED

(* eda_dep only depends on inst_id *)
Theorem eda_dep_inst_id_only:
  !eda x y x' y'.
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
    (eda_dep eda x y <=> eda_dep eda x' y')
Proof
  rw[eda_dep_def]
QED

(* Effect-free commutation predicate — no inst_wf needed *)
Definition ef_commutes_def:
  ef_commutes a b <=>
    is_effect_free_op a.inst_opcode /\ is_effect_free_op b.inst_opcode /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b))
End

(* ===== block_body_ok_equiv skeleton ===== *)

(* MEM x l ==> ?pfx sfx. l = pfx ++ [x] ++ sfx *)
Triviality last_split_sfx_nil:
  !pfx x sfx.
    x = LAST (pfx ++ [x] ++ sfx) /\ ALL_DISTINCT (pfx ++ [x] ++ sfx) ==>
    sfx = []
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  Cases_on `sfx` >- gvs[] >>
  `LAST (pfx ++ [x] ++ h::t) = LAST (h::t)` by
    (once_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp[LAST_APPEND_CONS, LAST_CONS_cond]) >>
  `MEM x (h::t)` by metis_tac[MEM_LAST] >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM]
QED

Triviality mem_split_append:
  !x l. MEM x l ==> ?pfx sfx. l = pfx ++ [x] ++ sfx
Proof
  metis_tac[MEM_SPLIT_APPEND_first]
QED

Triviality flat_map_outputs_fn_insts_blocks:
  !bbs.
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) =
    FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* block body instructions have ALL_DISTINCT inst_ids *)
Triviality all_distinct_flat_mem:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* General: if ALL_DISTINCT (FLAT (MAP f ls)), distinct elements a,b of ls
   have disjoint images under f *)
Triviality all_distinct_flat_map_disjoint:
  !ls f a b x.
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\ a <> b /\
    MEM x (f a) ==> ~MEM x (f b)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[MAP, FLAT, ALL_DISTINCT_APPEND]
  >> metis_tac[MEM_FLAT, MEM_MAP]
QED

Triviality all_distinct_flat_map_unique[local]:
  !ls f (a:'a) b (x:'b).
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\ MEM x (f a) /\ MEM x (f b) ==>
    a = b
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Triviality all_distinct_flat_map_filter[local]:
  !f P l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (FILTER P l)))
Proof
  Induct_on `l` >> simp[] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem block_body_all_distinct:
  !fn bb.
    wf_function fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (block_body bb))
Proof
  rpt strip_tac >>
  simp[block_body_def] >>
  irule all_distinct_map_filter >>
  irule all_distinct_flat_mem >>
  qexists `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks` >>
  gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  simp[MEM_MAP] >> qexists `bb` >> simp[]
QED

(* Given wf_function with distinct labels, block_perm_of's witness
   bb_orig must equal any fn block with the same label *)
Triviality block_perm_of_orig_unique:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    !bb_orig.
      MEM bb_orig fn.fn_blocks /\ bb'.bb_label = bb_orig.bb_label ==>
      bb_orig = bb
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb_orig` by
    (irule MEM_lookup_block >> simp[]) >>
  gvs[]
QED

(* Eliminate block_perm_of: replace bb_orig with bb *)
Theorem block_perm_of_elim:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    EVERY (\i. from_block bb.bb_instructions i)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    PERM (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))
         (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
    FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  `!bb_orig. MEM bb_orig fn.fn_blocks /\
             bb'.bb_label = bb_orig.bb_label ==> bb_orig = bb` by
    (rpt strip_tac >> irule block_perm_of_orig_unique >> metis_tac[]) >>
  fs[block_perm_of_def] >>
  `bb_orig = bb` by (first_x_assum irule >> simp[]) >>
  gvs[]
QED

(* Per-block ALL_DISTINCT inst_ids from wf_function *)
Theorem bb_inst_ids_distinct:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  irule all_distinct_flat_mem >>
  qexists `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks` >>
  gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  simp[MEM_MAP] >> qexists `bb` >> simp[]
QED

Triviality flip_operands_is_terminator:
  !i. is_terminator (flip_operands i).inst_opcode = is_terminator i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `i.inst_opcode` >> gvs[] >>
  EVAL_TAC
QED

(* topo_sorted for original block under full_dep eda (no TC needed).
   full_dep = eda_dep ∨ uses/defs overlap ∨ defs/defs overlap.
   Part 1 (eda_dep): from eda_topo_compatible_topo_sorted.
   Part 2 (uses/defs): from def_dominates_uses — user at i, definer at j>i impossible.
   Part 3 (defs/defs): from ssa_form — no two distinct instructions share outputs. *)
(* Use ssa_unique_output / mem_fn_insts_intro from allocaRemapSSATheory *)

(* If an instruction is MEM of two blocks, those blocks must be the same
   (by fn_inst_ids_distinct). *)
Triviality fn_inst_same_block:
  !fn bb1 bb2 inst.
    wf_function fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM inst bb1.bb_instructions /\ MEM inst bb2.bb_instructions ==>
    bb1 = bb2
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  fs[fn_inst_ids_distinct_def] >>
  `MEM inst.inst_id (MAP (\i. i.inst_id) bb2.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qspecl_then [`fn.fn_blocks`,
    `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
    `bb1`, `bb2`, `inst.inst_id`] mp_tac all_distinct_flat_map_disjoint >>
  simp[MEM_MAP] >> metis_tac[]
QED

(* In block_body, a later element cannot define a variable used by an earlier
   element. This follows from def_dominates_uses + SSA uniqueness + filter
   preserving order. *)
Triviality block_body_defs_before_uses:
  !fn bb i j v.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    i < j /\ j < LENGTH (block_body bb) /\
    MEM v (inst_defs (EL j (block_body bb))) /\
    MEM (Var v) (EL i (block_body bb)).inst_operands ==>
    F
Proof
  rpt strip_tac >>
  qabbrev_tac `bd = block_body bb` >>
  (* Step 1: EL i bd and EL j bd are distinct *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `ALL_DISTINCT bd` by
    (simp[Abbr `bd`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  `i < LENGTH bd` by decide_tac >>
  `EL i bd <> EL j bd` by
    (`i <> j` by decide_tac >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
  (* Step 2: Both are MEM of bb.bb_instructions *)
  `MEM (EL i bd) bb.bb_instructions /\ MEM (EL j bd) bb.bb_instructions` by
    (`MEM (EL i bd) bd /\ MEM (EL j bd) bd` by
       (simp[MEM_EL] >> metis_tac[]) >>
     unabbrev_all_tac >>
     fs[block_body_def, MEM_FILTER]) >>
  (* Step 3: Both are in fn_insts *)
  `MEM (EL i bd) (fn_insts fn) /\ MEM (EL j bd) (fn_insts fn)` by
    (conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  (* Step 4: v is in inst_outputs of EL j bd *)
  `MEM v (EL j bd).inst_outputs` by fs[inst_defs_def] >>
  (* Step 5: def_dominates_uses gives us a defining instruction *)
  gvs[wf_ssa_def] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  `MEM (EL i bd) bd` by
    (simp[MEM_EL] >> qexists_tac `i` >> simp[] >> decide_tac) >>
  `MEM (EL i bd) (block_body bb)` by gvs[Abbr `bd`] >>
  `~is_pseudo (EL i bd).inst_opcode` by
    fs[Abbr `bd`, block_body_def, MEM_FILTER] >>
  `(EL i bd).inst_opcode <> PHI` by
    (strip_tac >> gvs[is_pseudo_def]) >>
  `def_available_at fn bb (SOME (EL i bd)) v` by (
    first_x_assum (qspecl_then [`bb`, `EL i bd`] mp_tac) >>
    impl_tac >- simp[] >>
    qpat_x_assum `(EL i bd).inst_opcode <> PHI`
      (fn th => REWRITE_TAC [th]) >>
    disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at fn bb (SOME (EL i bd)) v`
    (strip_assume_tac o REWRITE_RULE[def_available_at_def]) >>
  (* Step 6: def_inst = EL j bd, and def_bb = bb *)
  `MEM def_inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `def_bb` >> simp[]) >>
  `MEM (EL j bd) (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  `def_inst = EL j bd` by metis_tac[ssa_unique_output] >>
  (* def_bb = bb: def_inst is MEM of both def_bb and bb (since def_inst = bd[j]).
     If def_bb ≠ bb, same inst_id in two blocks contradicts fn_inst_ids_distinct. *)
  `def_bb = bb` by
    metis_tac[fn_inst_same_block] >>
  gvs[] >>
  (* Now have: i' < j' with EL i' bb = definer (EL j bd),
     EL j' bb = user (EL i bd). But filter_el_mono gives
     fi < fj with EL fi bb = EL i bd, EL fj bb = EL j bd.
     By ALL_DISTINCT: fi = j' and fj = i', so j' < i'.
     Contradiction with i' < j'. *)
  `ALL_DISTINCT bb.bb_instructions` by
    metis_tac[ALL_DISTINCT_MAP] >>
  `i < LENGTH bd` by decide_tac >>
  `?fi fj. fi < fj /\ fj < LENGTH bb.bb_instructions /\
           EL fi bb.bb_instructions = EL i bd /\
           EL fj bb.bb_instructions = EL j bd` by
    (qspecl_then [`\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode`,
      `bb.bb_instructions`, `i`, `j`] mp_tac filter_el_mono >>
     unabbrev_all_tac >> simp[GSYM block_body_def]) >>
  `fi < LENGTH bb.bb_instructions` by decide_tac >>
  `i' < LENGTH bb.bb_instructions` by decide_tac >>
  `fi = j'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `fj = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  decide_tac
QED

Theorem block_body_topo_sorted:
  !fn bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    bb_well_formed bb ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (block_body bb)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `topo_sorted (eda_dep (build_full_eda bb.bb_instructions)) (block_body bb)` by
    suspend "eda_topo" >>
  simp[topo_sorted_def, full_dep_def] >>
  qabbrev_tac `bd = block_body bb` >>
  `ALL_DISTINCT bd` by
    (simp[Abbr `bd`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  rpt strip_tac
  >- (gvs[topo_sorted_def] >> metis_tac[])
  >- suspend "case1"
  >> suspend "case2"
QED

Resume block_body_topo_sorted[eda_topo]:
  rewrite_tac[block_body_def] >>
  irule eda_topo_compatible_topo_sorted >>
  simp[] >> conj_tac
  >- metis_tac[build_full_eda_wf]
  >> metis_tac[eda_topo_compatible_original]
QED

Resume block_body_topo_sorted[case1]:
  (* DISJOINT (inst_uses bd[i]) (inst_defs bd[j]) when i < j *)
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `MEM (Var v) (EL i bd).inst_operands` by
    gvs[inst_uses_def, MEM_operand_vars_iff] >>
  `bd = block_body bb` by fs[markerTheory.Abbrev_def] >>
  metis_tac[block_body_defs_before_uses]
QED

Resume block_body_topo_sorted[case2]:
  (* DISJOINT (inst_defs bd[i]) (inst_defs bd[j]) when i < j:
     SSA says each var has one definer, so bd[i] = bd[j], contradicting ALL_DISTINCT *)
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `i < LENGTH bd` by decide_tac >>
  `MEM (EL i bd) bd /\ MEM (EL j bd) bd` by
    (simp[MEM_EL] >> metis_tac[]) >>
  `MEM (EL i bd) bb.bb_instructions /\ MEM (EL j bd) bb.bb_instructions` by
    (fs[markerTheory.Abbrev_def] >>
     metis_tac[MEM_FILTER, block_body_def]) >>
  `MEM (EL i bd) (fn_insts fn) /\ MEM (EL j bd) (fn_insts fn)` by
    (conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  `MEM v (EL i bd).inst_outputs /\ MEM v (EL j bd).inst_outputs` by
    fs[inst_defs_def] >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `EL i bd = EL j bd` by
    metis_tac[ssa_unique_output] >>
  `i < LENGTH bd /\ i <> j` by decide_tac >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

Finalise block_body_topo_sorted

(* from_block source: unique original with inst_id, inst_outputs, ¬is_pseudo *)
Triviality from_block_source:
  !bi a.
    from_block bi a /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    ?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\
        j.inst_id = a.inst_id /\ j.inst_outputs = a.inst_outputs
Proof
  rw[from_block_def] >> gvs[]
  >- (qexists `a` >> simp[])
  >> qexists `j` >>
     simp[flip_operands_inst_id, flip_operands_inst_outputs]
QED

Triviality from_block_list_outputs_distinct[local]:
  !bi l.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
    EVERY (from_block bi) l ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) l))
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> rpt conj_tac
  >- (drule_all from_block_source >> strip_tac >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\i. i.inst_outputs) bi` >>
      simp[MEM_MAP] >> metis_tac[])
  >- (spose_not_then strip_assume_tac >>
      gvs[MEM_FLAT, MEM_MAP] >> rename1 `MEM y l` >>
      `from_block bi h /\ from_block bi y` by simp[] >>
      `?src_h. MEM src_h bi /\ ~is_pseudo src_h.inst_opcode /\
               src_h.inst_id = h.inst_id /\
               src_h.inst_outputs = h.inst_outputs` by
        (mp_tac (Q.SPECL [`bi`, `h`] from_block_source) >> simp[]) >>
      `?src_y. MEM src_y bi /\ ~is_pseudo src_y.inst_opcode /\
               src_y.inst_id = y.inst_id /\
               src_y.inst_outputs = y.inst_outputs` by
        (mp_tac (Q.SPECL [`bi`, `y`] from_block_source) >> simp[]) >>
      `src_h = src_y` by metis_tac[all_distinct_flat_map_unique] >>
      `h.inst_id = y.inst_id` by gvs[] >>
      `h = y` by metis_tac[all_distinct_map_mem_inj, MEM] >>
      gvs[])
  >> (first_x_assum irule >> simp[] >> metis_tac[])
QED

Triviality all_distinct_flat_map_append_disjoint[local]:
  !f l1 l2.
    ALL_DISTINCT (FLAT (MAP f l1)) /\
    ALL_DISTINCT (FLAT (MAP f l2)) /\
    (!x a b. MEM a l1 /\ MEM b l2 /\ MEM x (f a) /\ MEM x (f b) ==> F) ==>
    ALL_DISTINCT (FLAT (MAP f l1) ++ FLAT (MAP f l2))
Proof
  rpt strip_tac >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Triviality pseudo_from_block_outputs_disjoint[local]:
  !bi sched p y e.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    EVERY (from_block bi) sched /\
    MEM p (FILTER (\i. is_pseudo i.inst_opcode) bi) /\
    MEM y sched /\
    MEM e p.inst_outputs /\ MEM e y.inst_outputs ==>
    F
Proof
  rpt strip_tac >>
  `from_block bi y` by fs[EVERY_MEM] >>
  `?src_y. MEM src_y bi /\ ~is_pseudo src_y.inst_opcode /\
           src_y.inst_id = y.inst_id /\
           src_y.inst_outputs = y.inst_outputs` by
    (mp_tac (Q.SPECL [`bi`, `y`] from_block_source) >> simp[]) >>
  `MEM p bi /\ is_pseudo p.inst_opcode` by fs[MEM_FILTER] >>
  `p = src_y` by metis_tac[all_distinct_flat_map_unique] >>
  gvs[]
QED

(* Variant of map_choose_original_topo_sorted where condition 4
   is restricted to elements of l1 and l2 *)
Theorem map_choose_original_topo_sorted_restricted:
  !l1 l2 dep.
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    topo_sorted dep l2 /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) /\
    (!x y x' y'. MEM x l2 /\ MEM y l2 /\ MEM x' l1 /\ MEM y' l1 /\
       x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
       (dep x y <=> dep x' y')) ==>
    topo_sorted dep (MAP (choose_original l1) l2)
Proof
  rw[topo_sorted_def, LENGTH_MAP] >>
  simp[EL_MAP] >>
  `MEM (EL i l2) l2` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  `MEM (EL j l2) l2` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
  `(choose_original l1 (EL i l2)).inst_id = (EL i l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `(choose_original l1 (EL j l2)).inst_id = (EL j l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `MEM (choose_original l1 (EL i l2)) l1` by
    (irule (cj 1 choose_original_correct) >> metis_tac[]) >>
  `MEM (choose_original l1 (EL j l2)) l1` by
    (irule (cj 1 choose_original_correct) >> metis_tac[]) >>
  metis_tac[]
QED

(* NOTE: block_body_topo_sorted_co was FALSE as stated — block_perm_of
   does not carry ordering info. topo_sorted must come from the DFT pipeline
   (schedule_output_eda_before + schedule_output_producer_before).
   Now passed as hypothesis to block_body_ok_equiv. *)

(* Convert output_eda_before + output_producer_before → topo_sorted (full_dep eda).
   Key bridge from DFT topo sort results to the permutation simulation. *)
(* Per-block SSA: no two instructions share an output variable *)
Triviality schedule_topo_sorted_full_dep:
  !bi eda output.
    eda_wf eda bi /\
    output_eda_before eda output /\
    output_producer_before bi output /\
    ALL_DISTINCT (MAP (\i. i.inst_id) output) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!i. MEM i output ==> from_block bi i /\ ~is_pseudo i.inst_opcode) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) ==>
    topo_sorted (full_dep eda) output
Proof
  rw[topo_sorted_def, full_dep_def] >>
  spose_not_then strip_assume_tac >>
  gvs[]
  >- suspend "eda_case"
  >- suspend "uses_defs_case"
  >> suspend "defs_defs_case"
QED

(* Case 1: eda_dep(EL i, EL j) with i < j contradicts output_eda_before *)
Resume schedule_topo_sorted_full_dep[eda_case]:
  fs[output_eda_before_def, eda_dep_def] >>
  `~is_pseudo d.inst_opcode` by
    (qpat_x_assum `eda_wf _ _` mp_tac >> rw[eda_wf_def] >>
     Cases_on `FLOOKUP eda (EL i output).inst_id` >> gvs[] >>
     res_tac >> simp[]) >>
  (* Apply output_eda_before with k=i, witness d *)
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  qexists `d` >> simp[] >>
  rpt strip_tac >>
  (* m < i, (EL m output).inst_id = d.inst_id = (EL j output).inst_id *)
  (* ALL_DISTINCT → m = j → j < i, contradicts i < j *)
  `m < LENGTH output` by decide_tac >>
  `EL m (MAP (\i. i.inst_id) output) = EL j (MAP (\i. i.inst_id) output)` by
    simp[EL_MAP] >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `m`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[]
QED

(* Case 2: uses(EL i) ∩ defs(EL j) with i < j contradicts output_producer_before *)
Resume schedule_topo_sorted_full_dep[uses_defs_case]:
  fs[pred_setTheory.IN_DISJOINT, inst_uses_def, inst_defs_def] >>
  rename1 `MEM v (operand_vars _)` >>
  `MEM (Var v) (EL i output).inst_operands` by metis_tac[MEM_operand_vars_iff] >>
  `MEM (EL j output) output` by (simp[MEM_EL] >> metis_tac[]) >>
  (* Get j_orig ∈ bi: inst_id, inst_outputs, ¬is_pseudo — no case split *)
  `from_block bi (EL j output)` by metis_tac[] >>
  `?j_orig. MEM j_orig bi /\ ~is_pseudo j_orig.inst_opcode /\
            j_orig.inst_id = (EL j output).inst_id /\
            j_orig.inst_outputs = (EL j output).inst_outputs` by
    metis_tac[from_block_source] >>
  `MEM v j_orig.inst_outputs` by gvs[] >>
  (* producing_inst bi v = SOME j_orig (unique definer under SSA) *)
  `producing_inst bi v = SOME j_orig` by
    (qspecl_then [`bi`, `v`, `j_orig`] mp_tac producing_inst_unique_definer >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     rename1 `MEM other bi` >>
     qspecl_then [`bi`, `(\i. i.inst_outputs)`, `j_orig`, `other`, `v`]
       mp_tac all_distinct_flat_map_disjoint >> simp[]) >>
  (* Apply output_producer_before with k=i *)
  fs[output_producer_before_def] >>
  first_x_assum (qspecl_then [`i`, `v`, `j_orig`] mp_tac) >> simp[] >>
  strip_tac >>
  (* ALL_DISTINCT → m = j → j ≥ i, done *)
  rpt strip_tac >>
  spose_not_then assume_tac >> gvs[] >>
  `m < LENGTH output` by decide_tac >>
  `EL m (MAP (\i. i.inst_id) output) = EL j (MAP (\i. i.inst_id) output)` by
    simp[EL_MAP] >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `m`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[]
QED

(* Case 3: defs(EL i) ∩ defs(EL j) with i < j contradicts SSA unique outputs *)
Resume schedule_topo_sorted_full_dep[defs_defs_case]:
  fs[pred_setTheory.IN_DISJOINT, inst_defs_def] >>
  rename1 `MEM v (EL j output).inst_outputs` >>
  (* Get originals from bi for both EL i and EL j *)
  `i < LENGTH output` by decide_tac >>
  `MEM (EL i output) output` by metis_tac[MEM_EL] >>
  `MEM (EL j output) output` by metis_tac[MEM_EL] >>
  `from_block bi (EL i output) /\ from_block bi (EL j output)` by metis_tac[] >>
  `?i_orig. MEM i_orig bi /\ i_orig.inst_id = (EL i output).inst_id /\
            i_orig.inst_outputs = (EL i output).inst_outputs` by
    metis_tac[from_block_source] >>
  `?j_orig. MEM j_orig bi /\ j_orig.inst_id = (EL j output).inst_id /\
            j_orig.inst_outputs = (EL j output).inst_outputs` by
    metis_tac[from_block_source] >>
  (* Both originals define v → must be same instruction under SSA *)
  `MEM v i_orig.inst_outputs /\ MEM v j_orig.inst_outputs` by gvs[] >>
  `i_orig = j_orig` by
    (spose_not_then assume_tac >>
     qspecl_then [`bi`, `(\i. i.inst_outputs)`, `i_orig`, `j_orig`, `v`]
       mp_tac all_distinct_flat_map_disjoint >> simp[]) >>
  (* Same original → same inst_id → i = j, contradicts i < j *)
  `(EL i output).inst_id = (EL j output).inst_id` by
    (qpat_x_assum `i_orig = j_orig` SUBST_ALL_TAC >> gvs[]) >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `i`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[EL_MAP]
QED

Finalise schedule_topo_sorted_full_dep;

(* Helper: from_barrier result lifts to eda_dep of build_full_eda.
   If b is barrier at position after prefix in non_phis, and y is in prefix,
   then eda_dep(build_full_eda bi) b y. *)
Theorem from_barrier_to_eda_dep:
  !bi prefix b suffix y.
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = prefix ++ [b] ++ suffix /\
    is_barrier b /\ MEM y prefix /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    eda_dep (build_full_eda bi) b y
Proof
  rpt strip_tac >>
  simp[eda_dep_def] >> qexists `y` >> simp[] >>
  irule build_full_eda_mono_from_barrier >>
  (* add_deps_from_barrier bi eda = FST(FOLDL ... (eda,[]) non_phis) *)
  simp[add_deps_from_barrier_def, LET_THM] >>
  qspecl_then [`prefix`, `b`, `suffix`,
    `add_deps_on_barrier bi (add_abort_deps bi (build_eda bi))`, `[]`]
    mp_tac add_deps_from_barrier_foldl_spec >>
  simp[] >> disch_then irule >>
  conj_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [b] ++ suffix))` by
        (qpat_x_assum `FILTER _ _ = _` (SUBST1_TAC o SYM) >>
         irule all_distinct_map_filter >> simp[]) >>
      gvs[MAP_APPEND])
  >> simp[]
QED

(* Helper: on_barrier result lifts to eda_dep of build_full_eda.
   If y is non-barrier, and last barrier before y in non_phis is b',
   then eda_dep(build_full_eda bi) y b'. *)
Theorem on_barrier_to_eda_dep:
  !bi prefix y suffix b.
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = prefix ++ [y] ++ suffix /\
    ~is_barrier y /\
    (case FILTER is_barrier prefix of
       [] => F  (* no barrier before y — vacuous *)
     | bs => LAST bs = b) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    eda_dep (build_full_eda bi) y b
Proof
  rpt strip_tac >>
  simp[eda_dep_def] >> qexists `b` >> simp[] >>
  irule build_full_eda_mono_on_barrier >>
  (* add_deps_on_barrier operates on non_phis *)
  simp[add_deps_on_barrier_def, LET_THM] >>
  qspecl_then [`prefix`, `y`, `suffix`,
    `add_abort_deps bi (build_eda bi)`, `NONE`, `b`]
    mp_tac add_deps_on_barrier_foldl_spec >>
  impl_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [y] ++ suffix))` by
        (qpat_x_assum `FILTER _ _ = _` (SUBST1_TAC o SYM) >>
         irule all_distinct_map_filter >> simp[]) >>
      gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >>
      Cases_on `FILTER is_barrier prefix` >> gvs[])
  >> simp[]
QED

(* Barriers are TC-connected to all body elements via the restricted dep
   (full_dep restricted to block_body elements). Each eda_dep step in the
   chain has both endpoints in block_body, so we get TC of the restricted dep. *)
Theorem barrier_tc_connected:
  !bb b y dep.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM b (block_body bb) /\ MEM y (block_body bb) /\ b <> y /\
    is_barrier b /\
    dep = (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                 MEM a (block_body bb) /\ MEM c (block_body bb)) ==>
    TC dep b y \/ TC dep y b
Proof
  rpt strip_tac >> gvs[] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by simp[Abbr `bi`] >>
  `MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (fs[block_body_def, MEM_FILTER, Abbr `bi`] >> fs[]) >>
  `MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (fs[block_body_def, MEM_FILTER, Abbr `bi`] >> fs[]) >>
  qpat_x_assum `MEM b (FILTER _ _)`
    (strip_assume_tac o MATCH_MP mem_split_append) >>
  `MEM y (pfx ++ [b] ++ sfx)` by metis_tac[] >>
  fs[MEM_APPEND, MEM]
  >- suspend "y_before_b"
  >- gvs[]
  >> suspend "y_after_b"
QED

Resume barrier_tc_connected[y_before_b]:
  (* y in pfx = before b. barrier b has eda_dep to all before it *)
  disj1_tac >> irule TC_SUBSET >>
  simp[full_dep_def] >> disj1_tac >>
  simp[Abbr `eda`] >>
  irule from_barrier_to_eda_dep >>
  simp[] >> qexistsl [`pfx`, `sfx`] >> simp[]
QED

Resume barrier_tc_connected[y_after_b]:
  (* y in sfx = after b *)
  disj2_tac >>
  qpat_x_assum `MEM y sfx` (strip_assume_tac o MATCH_MP mem_split_append) >>
  qabbrev_tac `pre_y = pfx ++ [b] ++ pfx'` >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bi = pre_y ++ [y] ++ sfx'` by
    simp[Abbr `pre_y`] >>
  `MEM b (FILTER is_barrier pre_y)` by
    simp[Abbr `pre_y`, MEM_FILTER, MEM_APPEND] >>
  Cases_on `is_barrier y`
  >- suspend "y_barrier"
  >> suspend "y_not_barrier"
QED

Resume barrier_tc_connected[y_barrier]:
  (* y is also barrier — eda_dep from y to b, single step *)
  irule TC_SUBSET >> simp[full_dep_def] >> disj1_tac >>
  simp[Abbr `eda`] >>
  irule from_barrier_to_eda_dep >>
  simp[] >> qexistsl [`pre_y`, `sfx'`] >>
  simp[Abbr `pre_y`, MEM_APPEND]
QED

Resume barrier_tc_connected[y_not_barrier]:
  (* y not barrier — chain through last barrier b' in pre_y *)
  (* Unfold eda early so irule can match *)
  qpat_x_assum `Abbrev (eda = _)` (SUBST_ALL_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `FILTER is_barrier pre_y <> []` by (strip_tac >> fs[MEM]) >>
  Cases_on `FILTER is_barrier pre_y` >- gvs[] >>
  qabbrev_tac `b' = LAST (h::t)` >>
  `eda_dep (build_full_eda bi) y b'` by
    (irule on_barrier_to_eda_dep >>
     simp[] >> qexistsl [`pre_y`, `sfx'`] >>
     simp[Abbr `b'`]) >>
  (* b' is in block_body: barrier in pre_y, not terminator *)
  `MEM b' (block_body bb)` by suspend "mem_b'_body" >>
  Cases_on `b' = b`
  >- (gvs[] >> irule TC_SUBSET >>
      simp[full_dep_def] >> disj1_tac >> simp[eda_dep_def] >>
      first_x_assum (fn th => qexists `b` >> mp_tac th) >> simp[])
  (* b' <> b: chain y -> b' -> b *)
  >> `MEM b' (FILTER is_barrier pre_y)` by
       (qpat_assum `FILTER is_barrier pre_y = h::t` SUBST1_TAC >>
        simp[Abbr `b'`, MEM_LAST]) >>
  `is_barrier b' /\ MEM b' pre_y` by fs[MEM_FILTER] >>
  qpat_x_assum `MEM b' pre_y`
    (CHOOSE_THEN (CHOOSE_THEN assume_tac) o MATCH_MP mem_split_append) >>
  rename1 `pre_y = pre_b' ++ [b'] ++ suf_b'` >>
  `FILTER is_barrier suf_b' = []` by
    (`FILTER is_barrier pre_b' ++ [b'] ++ FILTER is_barrier suf_b' = h::t` by
       (qpat_assum `pre_y = pre_b' ++ _ ++ _`
          (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        gvs[FILTER_APPEND_DISTRIB]) >>
     qpat_assum `ALL_DISTINCT (MAP _ bi)`
       (assume_tac o MATCH_MP ALL_DISTINCT_MAP o
        Q.SPEC `\i. ~is_pseudo i.inst_opcode` o
        MATCH_MP all_distinct_map_filter) >>
     `ALL_DISTINCT (pre_y ++ [y] ++ sfx')` by metis_tac[] >>
     `ALL_DISTINCT pre_y` by fs[ALL_DISTINCT_APPEND] >>
     `ALL_DISTINCT (h::t)` by
       (qpat_assum `FILTER is_barrier pre_y = h::t` (SUBST1_TAC o SYM) >>
        simp[FILTER_ALL_DISTINCT]) >>
     irule last_split_sfx_nil >>
     qexistsl [`FILTER is_barrier pre_b'`, `b'`] >>
     simp[Abbr `b'`]) >>
  `MEM b pre_b'` by
    (`FILTER is_barrier pre_b' ++ [b'] = h::t` by
       (qpat_assum `pre_y = pre_b' ++ _ ++ _`
          (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        gvs[FILTER_APPEND_DISTRIB]) >>
     `MEM b (FILTER is_barrier pre_b' ++ [b'])` by
       (qpat_assum `FILTER is_barrier pre_b' ++ [b'] = h::t` SUBST1_TAC >>
        simp[]) >>
     `b <> b'` by metis_tac[] >>
     fs[MEM_APPEND, MEM, MEM_FILTER]) >>
  `eda_dep (build_full_eda bi) b' b` by
    (irule from_barrier_to_eda_dep >>
     simp[] >> qexistsl [`pre_b'`, `suf_b' ++ [y] ++ sfx'`] >>
     simp[MEM_APPEND]) >>
  (* Chain: TC dep y b via y -> b' -> b *)
  irule (CONJUNCT2 (SPEC_ALL TC_RULES)) >>
  qexists `b'` >> conj_tac >>
  irule TC_SUBSET >> simp[full_dep_def] >> disj1_tac >> simp[]
QED

(* Helper: element in prefix of FILTER is not at last position of original list.
   Used to show that a barrier appearing before y in the non-pseudo filter
   cannot be the terminator (which is always last in bi). *)
Triviality filter_prefix_not_last:
  !P l pre y sfx e.
    ALL_DISTINCT l /\ FILTER P l = pre ++ [y] ++ sfx /\
    MEM e pre /\ P e /\ MEM e l /\
    (!k. k < LENGTH l /\ is_terminator (EL k l).inst_opcode ==>
         k = PRE (LENGTH l)) /\
    l <> [] /\ is_terminator e.inst_opcode ==>
    F
Proof
  rpt strip_tac >>
  (* e is in pre, hence at index n < LENGTH pre in the filter *)
  `?n. n < LENGTH pre /\ EL n pre = e` by metis_tac[MEM_EL] >>
  (* y is at index LENGTH pre in the filter *)
  `n < LENGTH (FILTER P l)` by
    (pop_assum kall_tac >>
     qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  `LENGTH pre < LENGTH (FILTER P l)` by
    (qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  (* EL n (FILTER P l) = e, and EL (LENGTH pre) (FILTER P l) = y *)
  `EL n (FILTER P l) = e /\
   EL (LENGTH pre) (FILTER P l) = y` by
    (asm_rewrite_tac[] >> conj_tac >>
     simp[EL_APPEND_EQN]) >>
  (* filter_el_mono: n < LENGTH pre, so positions in l satisfy i' < j' *)
  drule_all filter_el_mono >>
  disch_then (qx_choosel_then [`ne`, `ny`] strip_assume_tac) >>
  (* ne is the position of e in l, ny is the position of y in l *)
  (* l[ne] = e, so ne = PRE(LENGTH l) since e is terminator *)
  `ne = PRE (LENGTH l)` by
    (first_x_assum irule >> gvs[]) >>
  (* But ny > ne and ny < LENGTH l => PRE(LENGTH l) < ny < LENGTH l.
     That means LENGTH l <= ny, contradiction. *)
  decide_tac
QED

Resume barrier_tc_connected[mem_b'_body]:
  (* b' = LAST(h::t) is in FILTER is_barrier pre_y, hence in pre_y.
     b' is not pseudo (from FILTER not_pseudo bi). Need: ~is_terminator.
     Use filter_prefix_not_last for the contradiction. *)
  `MEM b' (FILTER is_barrier pre_y)` by
    (qpat_assum `FILTER is_barrier pre_y = h::t` SUBST1_TAC >>
     simp[Abbr `b'`, MEM_LAST]) >>
  `is_barrier b' /\ MEM b' pre_y` by fs[MEM_FILTER] >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (qpat_assum `FILTER _ bi = pre_y ++ _ ++ _` SUBST1_TAC >>
     simp[MEM_APPEND]) >>
  `~is_pseudo b'.inst_opcode /\ MEM b' bi` by fs[MEM_FILTER] >>
  `MEM y bi` by
    (qpat_assum `MEM y (block_body bb)` mp_tac >>
     rewrite_tac[block_body_def, MEM_FILTER] >> metis_tac[]) >>
  simp[block_body_def, MEM_FILTER] >>
  spose_not_then assume_tac >>
  `bi = bb.bb_instructions` by fs[markerTheory.Abbrev_def] >>
  `ALL_DISTINCT bi` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bi)` mp_tac >>
     metis_tac[ALL_DISTINCT_MAP]) >>
  qpat_x_assum `bb_well_formed bb`
    (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
  irule filter_prefix_not_last >>
  qexistsl [`\i. ~is_pseudo i.inst_opcode`, `b'`, `bi`, `pre_y`, `sfx'`, `y`] >>
  BETA_TAC >> asm_rewrite_tac[]
QED

Finalise barrier_tc_connected

(* In a topo_sorted ALL_DISTINCT list, for an element TC-connected to
   all others, elements before it satisfy TC dep b y, and after don't. *)
Triviality tc_connected_before_after:
  !l dep b k.
    ALL_DISTINCT l /\ topo_sorted (TC dep) l /\
    k < LENGTH l /\ EL k l = b /\
    (!y. MEM y l /\ y <> b ==> TC dep b y \/ TC dep y b) ==>
    EVERY (\y. TC dep b y) (TAKE k l) /\
    EVERY (\y. ~TC dep b y) (DROP (SUC k) l)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
      `n < LENGTH l` by decide_tac >>
      `EL n l <> b` by
        (strip_tac >>
         qspecl_then [`l`, `n`, `k`] mp_tac ALL_DISTINCT_EL_IMP >>
         simp[]) >>
      `~TC dep (EL n l) (EL k l)` by
        (fs[topo_sorted_def] >> first_x_assum match_mp_tac >> decide_tac) >>
      `MEM (EL n l) l` by metis_tac[MEM_EL] >>
      gvs[] >> metis_tac[])
  >> (simp[EVERY_EL, EL_DROP] >> rpt strip_tac >>
      fs[topo_sorted_def] >>
      first_x_assum (qspecl_then [`k`, `SUC k + n`] mp_tac) >>
      simp[])
QED

(* Count of elements satisfying P in l, decomposed via TAKE/EL/DROP *)
Triviality filter_count_decompose:
  !P l k.
    k < LENGTH l ==>
    LENGTH (FILTER P l) =
      LENGTH (FILTER P (TAKE k l)) +
      (if P (EL k l) then 1 else 0) +
      LENGTH (FILTER P (DROP (SUC k) l))
Proof
  rpt strip_tac >>
  `l = TAKE k l ++ [EL k l] ++ DROP (SUC k) l` by
    simp[TAKE_DROP_SUC] >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[FILTER_APPEND_DISTRIB] >> IF_CASES_TAC >> simp[]
QED

(* Barriers are at the same positions in any two topo-sorted permutations.
   Proof: count predecessors (TC dep b y) using PERM_FILTER. *)
Triviality barriers_same_el:
  !l1 l2 dep k.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) /\
    k < LENGTH l1 /\ is_barrier (EL k l1) ==>
    EL k l2 = EL k l1
Proof
  rpt strip_tac >>
  qabbrev_tac `b = EL k l1` >>
  qabbrev_tac `P = \y:instruction. TC dep b y` >>
  `MEM b l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `?k'. k' < LENGTH l2 /\ EL k' l2 = b` by metis_tac[MEM_EL] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `k = k'` suffices_by simp[] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  (* b is TC-connected to all other elements *)
  `!y. MEM y l1 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    (rpt strip_tac >>
     first_x_assum (qspecl_then [`b`, `y`] mp_tac) >> simp[]) >>
  `EVERY P (TAKE k l1) /\ EVERY (\y. ~P y) (DROP (SUC k) l1)` by
    (simp[Abbr `P`] >>
     qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  `!y. MEM y l2 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[PERM_MEM_EQ] >>
  `EVERY P (TAKE k' l2) /\ EVERY (\y. ~P y) (DROP (SUC k') l2)` by
    (simp[Abbr `P`] >>
     qspecl_then [`l2`, `dep`, `b`, `k'`] mp_tac tc_connected_before_after >>
     simp[]) >>
  (* Count P in l1: use decomposition + EVERY assumptions *)
  `FILTER P (TAKE k l1) = TAKE k l1` by
    simp[FILTER_EQ_ID] >>
  `FILTER P (DROP (SUC k) l1) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (FILTER P l1) = k + (if P b then 1 else 0)` by
    (qspecl_then [`P`, `l1`, `k`] mp_tac filter_count_decompose >>
     simp[Abbr `b`]) >>
  (* Count P in l2 *)
  `FILTER P (TAKE k' l2) = TAKE k' l2` by
    simp[FILTER_EQ_ID] >>
  `FILTER P (DROP (SUC k') l2) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (FILTER P l2) = k' + (if P b then 1 else 0)` by
    (qspecl_then [`P`, `l2`, `k'`] mp_tac filter_count_decompose >>
     simp[]) >>
  (* PERM preserves FILTER length *)
  `LENGTH (FILTER P l1) = LENGTH (FILTER P l2)` by
    metis_tac[PERM_FILTER, PERM_LENGTH] >>
  fs[]
QED

(* ===== Unified lift_result for topo-sorted permutations ===== *)

(* run_insts_append: decompose run_insts over concatenation *)
Triviality run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED


(* ===== Topo-sorted permutation lift_result ===== *)

(* Strategy: Use run_insts_topo_lift for OK<=>OK and Abort=>revert_equiv,
   then prove a1=a2 for the Abort case separately using:
   1. FILTER equality: dep-chained P-elements have same FILTER in topo-sorted perms
   2. bi_independent_cross_abort: abort type preserved through bi-ind OK steps
   3. The first non-NoFail aborter is the same instruction in both orderings *)

(* --- Helper: first P-element in topo-sorted list with pairwise-dep P-elements
   is the same regardless of list ordering --- *)

(* Helper: in a topo_sorted list, no P-element can appear before index i
   if i is the minimal P-index in a permutation *)
Triviality topo_sorted_no_earlier_P:
  !l1 l2 dep P i1 b.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\ P x /\ P y ==>
           dep x y \/ dep y x) /\
    i1 < LENGTH l1 /\ b = EL i1 l1 /\ P b /\
    (!j. j < i1 ==> ~P (EL j l1)) ==>
    !i2 j. i2 < LENGTH l2 /\ b = EL i2 l2 /\
           j < i2 ==> ~P (EL j l2)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `j < LENGTH l2` by simp[] >>
  `j <> i2` by simp[] >>
  `EL j l2 <> b` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `MEM (EL j l2) l1` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  `dep (EL j l2) b \/ dep b (EL j l2)` by
    (first_x_assum irule >> simp[]) >>
  `~dep (EL j l2) (EL i2 l2)` by
    (qpat_x_assum `topo_sorted dep l2` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`j`, `i2`] mp_tac) >> simp[]) >>
  `~dep (EL j l2) b` by gvs[] >>
  `dep b (EL j l2)` by metis_tac[] >>
  `?k. k < LENGTH l1 /\ EL j l2 = EL k l1` by metis_tac[MEM_EL] >>
  `dep (EL i1 l1) (EL k l1)` by metis_tac[] >>
  `~(i1 < k)` by
    (strip_tac >>
     `~dep (EL i1 l1) (EL k l1)` suffices_by metis_tac[] >>
     qpat_x_assum `topo_sorted dep l1` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`i1`, `k`] mp_tac) >> simp[]) >>
  `k < i1 \/ k = i1` by simp[]
  >- metis_tac[]
  >> metis_tac[]
QED

(* If all P-satisfying pairs are dep-related, the first P-element in any
   topo-sorted permutation is the same element. *)
Triviality topo_first_P_element:
  !l1 l2 dep P.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\ P x /\ P y ==>
           dep x y \/ dep y x) /\
    (?x. MEM x l1 /\ P x) ==>
    ?pfx1 sfx1 pfx2 sfx2 x.
      l1 = pfx1 ++ [x] ++ sfx1 /\ l2 = pfx2 ++ [x] ++ sfx2 /\
      P x /\ EVERY ($~ o P) pfx1 /\ EVERY ($~ o P) pfx2
Proof
  rpt strip_tac >>
  suspend "main"
QED

Resume topo_first_P_element[main]:
  (* Use WOP to find minimal P-index in l1 *)
  `?i1. i1 < LENGTH l1 /\ P (EL i1 l1) /\
        !j. j < i1 ==> ~P (EL j l1)` by
    (`?n. n < LENGTH l1 /\ P (EL n l1)` by metis_tac[MEM_EL] >>
     qspecl_then [`\i. i < LENGTH l1 /\ P (EL i l1)`] mp_tac WOP >>
     impl_tac >- metis_tac[] >>
     disch_then (qx_choose_then `i1` (strip_assume_tac o BETA_RULE)) >>
     qexists `i1` >> simp[] >>
     rpt strip_tac >>
     `j < LENGTH l1` suffices_by metis_tac[] >> simp[]) >>
  (* b = first P-element in l1; find its index in l2 *)
  `MEM (EL i1 l1) l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `?i2. i2 < LENGTH l2 /\ EL i1 l1 = EL i2 l2` by metis_tac[MEM_EL] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  (* ~P before i2 in l2, using the extracted helper *)
  `!i2' j'. i2' < LENGTH l2 /\ EL i1 l1 = EL i2' l2 /\
            j' < i2' ==> ~P (EL j' l2)` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`l1`, `l2`, `dep`, `P`, `i1`, `EL i1 l1`]
       mp_tac topo_sorted_no_earlier_P >>
     impl_tac >- simp[] >>
     disch_then (qspecl_then [`i2'`, `j'`] mp_tac) >> simp[]) >>
  (* Decompose both lists *)
  qexistsl [`TAKE i1 l1`, `DROP (SUC i1) l1`,
            `TAKE i2 l2`, `DROP (SUC i2) l2`, `EL i1 l1`] >>
  simp[Once (GSYM TAKE_DROP_SUC)] >>
  simp[Once (GSYM TAKE_DROP_SUC)] >>
  simp[EVERY_EL, LENGTH_TAKE_EQ] >>
  rpt strip_tac >> gvs[EL_TAKE] >> metis_tac[]
QED

Finalise topo_first_P_element;

(* Prefix before a barrier in topo-sorted list: same elements in both orderings.
   By tc_connected_before_after, TAKE k l = FILTER (TC dep b) l for both lists.
   Since PERM l1 l2, FILTER on a predicate gives PERM of the filtered lists. *)
Triviality barrier_prefix_perm:
  !l1 l2 dep k.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) /\
    k < LENGTH l1 /\ is_barrier (EL k l1) ==>
    PERM (TAKE k l1) (TAKE k l2)
Proof
  rpt strip_tac >>
  qabbrev_tac `b = EL k l1` >>
  `EL k l2 = b` by metis_tac[barriers_same_el] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  `!y. MEM y l1 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[] >>
  `!y. MEM y l2 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[PERM_MEM_EQ] >>
  (* tc_connected_before_after for l1 *)
  `EVERY (\y. TC dep b y) (TAKE k l1)` by
    (qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  `EVERY (\y. ~TC dep b y) (DROP (SUC k) l1)` by
    (qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  (* tc_connected_before_after for l2 *)
  `k < LENGTH l2` by simp[] >>
  `EVERY (\y. TC dep b y) (TAKE k l2)` by
    (qspecl_then [`l2`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[]) >>
  `EVERY (\y. ~TC dep b y) (DROP (SUC k) l2)` by
    (qspecl_then [`l2`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[]) >>
  (* Core: TC dep b x forces x to appear before k in any topo_sorted list *)
  `!l' j'. topo_sorted (TC dep) l' /\ ALL_DISTINCT l' /\
           k < LENGTH l' /\ EL k l' = b /\
           j' < LENGTH l' /\ j' <> k /\ TC dep b (EL j' l') ==> j' < k` by
    (rpt gen_tac >> strip_tac >>
     spose_not_then assume_tac >>
     `k < j'` by simp[] >>
     qpat_assum `topo_sorted _ l'` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`k`, `j'`] mp_tac) >> simp[]) >>
  (* Subset direction 1: TAKE k l1 ⊆ TAKE k l2 *)
  `!x. MEM x (TAKE k l1) ==> MEM x (TAKE k l2)` by
    suspend "dir1" >>
  (* Subset direction 2: TAKE k l2 ⊆ TAKE k l1 *)
  `!x. MEM x (TAKE k l2) ==> MEM x (TAKE k l1)` by
    suspend "dir2" >>
  (* Both directions + same length + ALL_DISTINCT => PERM *)
  irule PERM_ALL_DISTINCT >>
  simp[ALL_DISTINCT_TAKE] >>
  metis_tac[]
QED

(*
 * Shared helper: EL k l is NOT in TAKE k l when ALL_DISTINCT
 *)
Triviality el_not_mem_take:
  !l k. ALL_DISTINCT l /\ k < LENGTH l ==> ~MEM (EL k l) (TAKE k l)
Proof
  rpt strip_tac >>
  `MEM (EL k l) (DROP k l)` by
    (simp[MEM_DROP] >> qexists `0` >> simp[]) >>
  metis_tac[ALL_DISTINCT_TAKE_DROP]
QED

Resume barrier_prefix_perm[dir1]:
  rpt strip_tac >>
  `TC dep b x` by fs[EVERY_MEM] >>
  `x <> b` by
    (strip_tac >> gvs[Abbr `b`] >> metis_tac[el_not_mem_take]) >>
  `MEM x l2` by metis_tac[MEM_TAKE, PERM_MEM_EQ] >>
  `?j'. j' < LENGTH l2 /\ EL j' l2 = x` by metis_tac[MEM_EL] >>
  `j' <> k` by
    (strip_tac >> gvs[] >> metis_tac[el_not_mem_take]) >>
  `j' < k` by
    (qpat_x_assum `!l' j'. topo_sorted _ l' /\ _ ==> _`
       (qspecl_then [`l2`, `j'`] mp_tac) >> gvs[]) >>
  simp[MEM_EL] >> qexists `j'` >> simp[LENGTH_TAKE_EQ, EL_TAKE]
QED

Resume barrier_prefix_perm[dir2]:
  rpt strip_tac >>
  `TC dep b x` by fs[EVERY_MEM] >>
  `x <> b` by
    (strip_tac >> gvs[] >> metis_tac[el_not_mem_take]) >>
  `MEM x l1` by metis_tac[MEM_TAKE, PERM_MEM_EQ] >>
  `?j'. j' < LENGTH l1 /\ EL j' l1 = x` by metis_tac[MEM_EL] >>
  `j' <> k` by
    (strip_tac >> gvs[Abbr `b`] >> metis_tac[el_not_mem_take]) >>
  `j' < k` by
    (qpat_x_assum `!l' j'. topo_sorted _ l' /\ _ ==> _`
       (qspecl_then [`l1`, `j'`] mp_tac) >> gvs[Abbr `b`]) >>
  simp[MEM_EL] >> qexists `j'` >> simp[LENGTH_TAKE_EQ, EL_TAKE]
QED

Finalise barrier_prefix_perm

(* Sorted-by-predicate list decomposes as FILTER P ++ FILTER ~P *)
Triviality sorted_pred_split:
  !l P. (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    FILTER P l ++ FILTER ($~ o P) l = l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> simp[]
  >- (first_x_assum (qspec_then `P` mp_tac) >>
      impl_tac >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[])
  >> (* h fails P. Then ALL elements fail P (if any passed, h would too) *)
     `EVERY (\x. ~P x) l` by
       (simp[EVERY_MEM, MEM_EL, PULL_EXISTS] >>
        rpt strip_tac >> spose_not_then assume_tac >>
        first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
     `FILTER P l = []` by simp[FILTER_EQ_NIL] >>
     `FILTER ($~ o P) l = l` by
       (simp[FILTER_EQ_ID] >> fs[EVERY_MEM]) >>
     simp[]
QED

Triviality sorted_prefix_take_filter:
  !l P.
    (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    TAKE (LENGTH (FILTER P l)) l = FILTER P l
Proof
  rpt strip_tac >>
  `FILTER P l ++ FILTER ($~ o P) l = l` by metis_tac[sorted_pred_split] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))) >>
  simp[TAKE_LENGTH_APPEND]
QED

Triviality pseudo_prefix_take_filter:
  !bb.
    pseudos_prefix bb ==>
    TAKE (LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
      bb.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  irule sorted_prefix_take_filter >>
  rpt strip_tac >>
  qpat_x_assum `pseudos_prefix bb` mp_tac >>
  simp[pseudos_prefix_def] >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >>
  impl_tac >- gvs[] >>
  simp[]
QED

(* ===== FRONT-based exec_block decomposition ===== *)

(* For a well-formed block, FRONT has no terminators and LAST is the terminator.
   exec_block = run_insts FRONT + step_inst LAST.
   If run_insts FRONT produces OK, exec_block reduces to stepping the terminator.
   If run_insts FRONT produces Abort/Error, exec_block propagates that. *)

(* FRONT elements of a well-formed block are non-terminators *)
Triviality front_no_terminators:
  !bb. bb_well_formed bb ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `~NULL bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL n (FRONT bb.bb_instructions) = EL n bb.bb_instructions` by
    simp[EL_FRONT] >>
  `n < LENGTH bb.bb_instructions` by
    (gvs[LENGTH_FRONT] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `n = PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `bb_well_formed _` mp_tac >>
     simp[bb_well_formed_def] >> strip_tac >>
     first_x_assum irule >> gvs[]) >>
  gvs[LENGTH_FRONT]
QED

(* Two distinct instructions in fn_insts can't share an output variable *)
Triviality ssa_no_shared_output:
  !fn i1 i2 v.
    ssa_form fn /\ MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    i1 <> i2 /\ MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==>
    F
Proof
  rw[ssa_form_def, fn_insts_def] >>
  metis_tac[all_distinct_flat_map_disjoint]
QED

(* Consequence: distinct same-block instructions have disjoint defs *)
Theorem ssa_disjoint_defs:
  !fn bb i1 i2.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    MEM i1 bb.bb_instructions /\ MEM i2 bb.bb_instructions /\ i1 <> i2 ==>
    DISJOINT (set (inst_defs i1)) (set (inst_defs i2))
Proof
  rpt strip_tac >>
  simp[inst_defs_def, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[ssa_no_shared_output, mem_fn_insts_blocks, fn_insts_def]
QED

(* Key: pseudo inst_id is not among non-pseudo inst_ids *)
Triviality pseudo_id_not_in_nonpseudo:
  !bi p.
    is_pseudo p.inst_opcode /\ MEM p bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    ~MEM p.inst_id (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt strip_tac >> gvs[MEM_MAP, MEM_FILTER] >>
  (* y is non-pseudo, MEM y bi, y.inst_id = p.inst_id *)
  (* By ALL_DISTINCT MAP inst_id, y = p. But y is non-pseudo, p is pseudo. *)
  gvs[MEM_EL] >>
  `EL n (MAP (\i. i.inst_id) bi) = EL n' (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  `n < LENGTH (MAP (\i. i.inst_id) bi) /\
   n' < LENGTH (MAP (\i. i.inst_id) bi)` by simp[] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Helper: FOLDL with |+ from list elements has FDOM ⊆ initial ∪ list_ids.
   Stated without let to avoid IH matching issues. *)
Triviality fdom_chain_foldl:
  !l (eda:num |-> instruction list) prev.
    FDOM (FST (FOLDL (\(acc,prev) (inst:instruction).
      (acc |+ (inst.inst_id,
        case prev of NONE =>
          (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
        | SOME p =>
          if MEM p (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
          then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
          else p::(case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
       SOME inst)) (eda,prev) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `FOLDL _ (eda',_) l` >>
  first_x_assum (qspecl_then [`eda'`, `SOME h`] mp_tac) >>
  `FDOM eda' = h.inst_id INSERT FDOM eda` by
    simp[Abbr `eda'`, FDOM_FUPDATE] >>
  strip_tac >> irule SUBSET_TRANS >> qexists `FDOM eda' UNION set (MAP (\i. i.inst_id) l)` >>
  simp[] >> simp[SUBSET_DEF] >> metis_tac[]
QED

(* FDOM of build_eda FOLDL is subset of accumulator FDOM + list inst_ids *)
Triviality fdom_build_eda_foldl:
  !l (acc:num |-> instruction list) et.
    FDOM (FST (FOLDL (\(acc_map,et) inst.
      (\(deps,et'). (acc_map |+ (inst.inst_id, deps), et'))
        (compute_effect_deps et inst)) (acc,et) l))
    SUBSET (FDOM acc UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `compute_effect_deps et h` >>
  first_x_assum (qspecl_then [`acc |+ (h.inst_id, q)`, `r`] mp_tac) >>
  simp[FDOM_FUPDATE, SUBSET_DEF] >> metis_tac[]
QED

(* FDOM of build_eda is subset of non-pseudo inst_ids *)
Triviality fdom_build_eda:
  !bi. FDOM (build_eda bi) SUBSET
       set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  gen_tac >> simp[build_eda_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`,
               `FEMPTY`, `empty_effect_track`]
    mp_tac fdom_build_eda_foldl >>
  simp[FDOM_FEMPTY]
QED

(* FDOM of add_deps_on_barrier: only adds keys from non-pseudo list *)
Triviality fdom_on_barrier_foldl:
  !l (eda:num |-> instruction list) lb.
    FDOM (FST (FOLDL (\(acc,last_bar) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds in
      if is_barrier inst then (acc, SOME inst)
      else let new_deps = case last_bar of NONE => old_deps
           | SOME b => if MEM b old_deps then old_deps else b::old_deps
           in (acc |+ (inst.inst_id, new_deps), last_bar))
      (eda,lb) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `is_barrier h` >> simp[LET_THM]
  >- (first_x_assum (qspecl_then [`eda`, `SOME h`] mp_tac) >>
      simp[LET_THM, SUBSET_DEF] >> metis_tac[])
  >> (qmatch_goalsub_abbrev_tac `FOLDL _ (eda',_) l` >>
      first_x_assum (qspecl_then [`eda'`, `lb`] mp_tac) >>
      simp[LET_THM] >>
      `FDOM eda' = h.inst_id INSERT FDOM eda` by
        simp[Abbr `eda'`, FDOM_FUPDATE] >>
      simp[SUBSET_DEF] >> metis_tac[])
QED

Triviality fdom_add_deps_on_barrier:
  !bi eda. FDOM (add_deps_on_barrier bi eda) SUBSET
           FDOM eda UNION set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_deps_on_barrier_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `eda`, `NONE`]
    mp_tac fdom_on_barrier_foldl >> simp[]
QED

(* FDOM of add_deps_from_barrier: only adds keys from non-pseudo list *)
Triviality fdom_from_barrier_foldl:
  !l (eda:num |-> instruction list) pi.
    FDOM (FST (FOLDL (\(acc,prev_insts) inst.
      if is_barrier inst then
        let old_deps = case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds;
            new_deps = FOLDL (\ds p. if MEM p ds then ds else p::ds)
                       old_deps prev_insts
        in (acc |+ (inst.inst_id, new_deps), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
      (eda,pi) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  Cases_on `is_barrier h` >> simp[LET_THM]
  >- (disch_then (qspecl_then
        [`eda |+ (h.inst_id,
            FOLDL (\ds p. if MEM p ds then ds else p::ds)
              (case FLOOKUP eda h.inst_id of NONE => [] | SOME ds => ds) pi')`,
         `pi' ++ [h]`] mp_tac) >>
      simp[FDOM_FUPDATE, SUBSET_DEF] >> metis_tac[])
  >> (disch_then (qspecl_then [`eda`, `pi' ++ [h]`] mp_tac) >>
      simp[SUBSET_DEF] >> metis_tac[])
QED

Triviality fdom_add_deps_from_barrier:
  !bi eda. FDOM (add_deps_from_barrier bi eda) SUBSET
           FDOM eda UNION set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_deps_from_barrier_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `eda`, `[]`]
    mp_tac fdom_from_barrier_foldl >> simp[]
QED

(* FDOM of add_chain_deps: only adds keys from non-pseudo list *)
Triviality fdom_add_chain_deps:
  !P' bi eda. FDOM (add_chain_deps P' bi eda) SUBSET
              FDOM eda UNION set (MAP (\i. i.inst_id)
                (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_chain_deps_def, LET_THM] >>
  irule SUBSET_TRANS >> irule_at Any fdom_chain_foldl >>
  simp[UNION_SUBSET, SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* FDOM of build_full_eda: only contains non-pseudo inst_ids *)
Triviality fdom_build_full_eda:
  !bi. FDOM (build_full_eda bi) SUBSET
       set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  gen_tac >>
  simp[build_full_eda_def, add_alloca_deps_def,
       add_barrier_deps_def, add_abort_deps_def] >>
  qabbrev_tac `ids = set (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bi))` >>
  (* Helper: each layer preserves SUBSET ids *)
  `!P eda. FDOM eda SUBSET ids ==> FDOM (add_chain_deps P bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_chain_deps >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `!eda. FDOM eda SUBSET ids ==> FDOM (add_deps_on_barrier bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_deps_on_barrier >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `!eda. FDOM eda SUBSET ids ==> FDOM (add_deps_from_barrier bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_deps_from_barrier >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `FDOM (build_eda bi) SUBSET ids` by
    (irule SUBSET_TRANS >> irule_at Any fdom_build_eda >>
     simp[Abbr `ids`]) >>
  metis_tac[]
QED

(* EDA has no entry for pseudo instruction ids *)
Triviality build_full_eda_pseudo_none:
  !bi p.
    is_pseudo p.inst_opcode /\ MEM p bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    FLOOKUP (build_full_eda bi) p.inst_id = NONE
Proof
  rpt strip_tac >>
  drule_all pseudo_id_not_in_nonpseudo >> strip_tac >>
  simp[FLOOKUP_DEF] >> strip_tac >>
  mp_tac (SPEC_ALL fdom_build_full_eda) >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

(* Helper: no forward data dependency in a well-formed SSA block.
   If i < j in a block, EL i cannot use a variable defined by EL j. *)
Triviality no_forward_data_dep:
  !fn bb i j.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    i < j /\ j < LENGTH bb.bb_instructions ==>
    DISJOINT (set (inst_uses (EL i bb.bb_instructions)))
             (set (inst_defs (EL j bb.bb_instructions)))
Proof
  rpt strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `MEM (Var v) (EL i bi).inst_operands` by
    gvs[inst_uses_def, MEM_operand_vars_iff] >>
  `MEM v (EL j bi).inst_outputs` by fs[inst_defs_def] >>
  (* EL i and EL j are distinct *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by
    (simp[Abbr `bi`] >> metis_tac[bb_inst_ids_distinct]) >>
  `i < LENGTH bi` by decide_tac >>
  `EL i bi <> EL j bi` by
    (`ALL_DISTINCT bi` by metis_tac[ALL_DISTINCT_MAP] >>
     `i <> j` by decide_tac >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
  (* Both are MEM of bb.bb_instructions *)
  `MEM (EL i bi) bi /\ MEM (EL j bi) bi` by metis_tac[MEM_EL] >>
  (* Both are in fn_insts *)
  `MEM (EL i bi) (fn_insts fn) /\ MEM (EL j bi) (fn_insts fn)` by
    (simp[Abbr `bi`] >>
     conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[MEM_EL] >>
     metis_tac[]) >>
  (* def_dominates_uses gives us a defining instruction for v *)
  `def_dominates_uses fn` by gvs[wf_ssa_def] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  `(EL i bi).inst_opcode <> PHI` by simp[Abbr `bi`] >>
  `def_available_at fn bb (SOME (EL i bi)) v` by (
    first_x_assum (qspecl_then [`bb`, `EL i bi`] mp_tac) >>
    impl_tac >- (simp[Abbr `bi`, MEM_EL] >> metis_tac[MEM_EL]) >>
    qpat_x_assum `(EL i bi).inst_opcode <> PHI`
      (fn th => REWRITE_TAC [th]) >>
    disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at fn bb (SOME (EL i bi)) v`
    (strip_assume_tac o REWRITE_RULE[def_available_at_def]) >>
  (* def_inst = EL j bi by ssa_form uniqueness *)
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `MEM def_inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `def_bb` >> simp[]) >>
  `def_inst = EL j bi` by
    metis_tac[ssa_unique_output, inst_defs_def] >>
  gvs[] >>
  (* def_bb = bb: EL j bi is in both def_bb and bb.
     By fn_inst_ids_distinct, instruction IDs are unique across all blocks,
     so these must be the same block. *)
  `def_bb = bb` by
    (spose_not_then assume_tac >>
     qspecl_then [`fn.fn_blocks`,
       `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
       `def_bb`, `bb`, `(EL j bi).inst_id`]
       mp_tac all_distinct_flat_map_disjoint >>
     simp[MEM_MAP] >>
     gvs[wf_function_def, fn_inst_ids_distinct_def] >>
     conj_tac >> qexists `EL j bi` >>
     simp[Abbr `bi`, MEM_EL] >> metis_tac[]) >>
  gvs[] >>
  (* Now: i' < j' < LENGTH bi, EL i' bi = EL j bi, EL j' bi = EL i bi
     By ALL_DISTINCT: i' = j, j' = i. So j < i. But i < j. *)
  `ALL_DISTINCT bi` by metis_tac[ALL_DISTINCT_MAP] >>
  `i' < LENGTH bi /\ i < LENGTH bi` by decide_tac >>
  `i' = j` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `j' = i` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* Reverse of filter_el_mono: positions in full list → positions in FILTER *)
Triviality filter_el_mono_rev:
  !P (l:'a list) i j. ALL_DISTINCT l /\ i < j /\ j < LENGTH l /\
    P (EL i l) /\ P (EL j l) ==>
    ?i' j'. i' < j' /\ j' < LENGTH (FILTER P l) /\
            EL i' (FILTER P l) = EL i l /\
            EL j' (FILTER P l) = EL j l
Proof
  rpt strip_tac >>
  `i < LENGTH l` by decide_tac >>
  qexistsl [`LENGTH (FILTER P (TAKE i l))`,
            `LENGTH (FILTER P (TAKE j l))`] >>
  `l = TAKE i l ++ EL i l :: DROP (SUC i) l` by
    metis_tac[DROP_CONS_EL, TAKE_DROP, APPEND_ASSOC, CONS_APPEND] >>
  `l = TAKE j l ++ EL j l :: DROP (SUC j) l` by
    metis_tac[DROP_CONS_EL, TAKE_DROP, APPEND_ASSOC, CONS_APPEND] >>
  rpt conj_tac
  >- suspend "lt_ij"
  >- suspend "lt_jl"
  >- suspend "el_i"
  >> suspend "el_j"
QED

Resume filter_el_mono_rev[lt_ij]:
  (* LENGTH (FILTER P (TAKE i l)) < LENGTH (FILTER P (TAKE j l)) *)
  `FILTER P (TAKE j l) = FILTER P (TAKE i l) ++
     FILTER P (DROP i (TAKE j l))` by
    (`TAKE j l = TAKE i (TAKE j l) ++ DROP i (TAKE j l)` by
       metis_tac[TAKE_DROP] >>
     `TAKE i (TAKE j l) = TAKE i l` by simp[TAKE_TAKE_T] >>
     pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
     metis_tac[FILTER_APPEND_DISTRIB]) >>
  simp[] >>
  `DROP i (TAKE j l) = TAKE (j - i) (DROP i l)` by
    simp[DROP_TAKE] >>
  `DROP i l = EL i l :: DROP (SUC i) l` by simp[DROP_CONS_EL] >>
  Cases_on `j - i` >> gvs[]
QED

Resume filter_el_mono_rev[lt_jl]:
  (* LENGTH (FILTER P (TAKE j l)) < LENGTH (FILTER P l) *)
  `FILTER P l = FILTER P (TAKE j l) ++ FILTER P (DROP j l)` by
    metis_tac[TAKE_DROP, FILTER_APPEND_DISTRIB] >>
  `DROP j l = EL j l :: DROP (SUC j) l` by simp[DROP_CONS_EL] >>
  simp[]
QED

Resume filter_el_mono_rev[el_i]:
  qspecl_then [`P`, `l`, `TAKE i l`, `DROP (SUC i) l`, `EL i l`]
    mp_tac FILTER_EL_IMP >> simp[LET_THM]
QED

Resume filter_el_mono_rev[el_j]:
  qspecl_then [`P`, `l`, `TAKE j l`, `DROP (SUC j) l`, `EL j l`]
    mp_tac FILTER_EL_IMP >> simp[LET_THM]
QED

Finalise filter_el_mono_rev

(* FRONT of a well-formed block is topo_sorted under full_dep *)
Triviality front_topo_sorted:
  !fn bb eda.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    EVERY (λinst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    eda = build_full_eda bb.bb_instructions ==>
    topo_sorted (full_dep eda) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  simp[topo_sorted_def] >>
  qx_gen_tac `p` >> qx_gen_tac `q` >> strip_tac >>
  `bb_well_formed bb` by
    (drule (iffLR wf_function_def) >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all bb_inst_ids_distinct >> strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  simp[EL_FRONT, NULL_EQ] >>
  `q < LENGTH bi` by
    (qpat_x_assum `q < LENGTH (FRONT bi)` mp_tac >>
     simp[LENGTH_FRONT]) >>
  `p < LENGTH bi` by simp[] >>
  imp_res_tac ALL_DISTINCT_MAP >>
  simp[full_dep_def] >>
  rpt strip_tac
  >- suspend "eda_dep"
  >- suspend "data_dep"
  >> suspend "output_alias"
QED

Resume front_topo_sorted[eda_dep]:
  `MEM (EL p bi) bi /\ MEM (EL q bi) bi` by metis_tac[MEM_EL] >>
  Cases_on `is_pseudo (EL p bi).inst_opcode`
  >- (`FLOOKUP (build_full_eda bi) (EL p bi).inst_id = NONE` by
        (irule build_full_eda_pseudo_none >> simp[]) >>
      fs[eda_dep_def])
  >> Cases_on `is_pseudo (EL q bi).inst_opcode`
  >- (fs[eda_dep_def] >>
      Cases_on `FLOOKUP (build_full_eda bi) (EL p bi).inst_id` >> fs[] >>
      `eda_wf (build_full_eda bi) bi` by simp[build_full_eda_wf] >>
      fs[eda_wf_def] >>
      rename1 `FLOOKUP _ _ = SOME deps` >>
      rename1 `MEM d0 deps` >>
      `MEM d0 bi /\ ~is_pseudo d0.inst_opcode` by metis_tac[] >>
      `d0 = EL q bi` by metis_tac[all_distinct_map_mem_inj] >>
      fs[])
  >> (* Both non-pseudo: reduce to block_body_topo_sorted *)
  qabbrev_tac `bd = block_body bb` >>
  `bd = FILTER (\x. ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode) bi` by
    simp[Abbr `bd`, block_body_def, Abbr `bi`] >>
  (* Both EL p bi and EL q bi are non-terminators (in FRONT) *)
  `~is_terminator (EL p bi).inst_opcode /\ ~is_terminator (EL q bi).inst_opcode` by
    (`EVERY (\inst. ~is_terminator inst.inst_opcode) (FRONT bi)` by
       (simp[Abbr `bi`] >> metis_tac[front_no_terminators]) >>
     `p < LENGTH (FRONT bi)` by simp[] >>
     qpat_x_assum `EVERY _ (FRONT bi)` mp_tac >>
     simp[EVERY_EL, EL_FRONT, NULL_EQ]) >>
  `?pp qq. pp < qq /\ qq < LENGTH bd /\
           EL pp bd = EL p bi /\ EL qq bd = EL q bi` by
    (qspecl_then [`\x. ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode`,
                  `bi`, `p`, `q`]
       mp_tac filter_el_mono_rev >> simp[]) >>
  `topo_sorted (full_dep (build_full_eda bi)) bd` by
    (simp[Abbr `bd`, Abbr `bi`] >> metis_tac[block_body_topo_sorted]) >>
  fs[topo_sorted_def] >>
  first_x_assum (qspecl_then [`pp`, `qq`] mp_tac) >> simp[] >>
  simp[full_dep_def]
QED

Resume front_topo_sorted[data_dep]:
  `(EL p bi).inst_opcode <> PHI` by
    (fs[EVERY_EL, Abbr `bi`] >> metis_tac[]) >> qspecl_then [`fn`, `bb`, `p`, `q`] mp_tac no_forward_data_dep >>
  simp[Abbr `bi`]
QED

Resume front_topo_sorted[output_alias]:
  `EL p bi <> EL q bi` by
    (strip_tac >> `p = q` suffices_by simp[] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  `MEM (EL p bi) bi /\ MEM (EL q bi) bi` by metis_tac[MEM_EL] >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  qspecl_then [`fn`, `bb`, `EL p bi`, `EL q bi`] mp_tac ssa_disjoint_defs >>
  simp[Abbr `bi`]
QED

Finalise front_topo_sorted

Triviality terminator_not_pseudo_not_flippable:
  !op. is_terminator op ==> ~is_pseudo op /\ ~is_flippable op
Proof
  Cases >> simp[is_terminator_def, is_pseudo_def, is_flippable_def,
                is_commutative_def, is_comparator_def]
QED

Theorem lift_result_refl:
  !x. lift_result (state_equiv {}) (execution_equiv {}) revert_equiv x x
Proof
  Cases >> simp[lift_result_def, state_equiv_refl, execution_equiv_refl,
                revert_equiv_def]
QED


(* Original blocks satisfy block_perm_of *)
Theorem original_block_perm_of:
  !fn bb. MEM bb fn.fn_blocks ==> block_perm_of fn bb
Proof
  rpt strip_tac >> simp[block_perm_of_def] >>
  qexists_tac `bb` >> simp[from_block_def] >>
  simp[EVERY_FILTER, EVERY_MEM] >> rpt strip_tac >>
  qexists_tac `i` >> simp[]
QED

(* from_block preserves inst_id *)
Triviality from_block_inst_id:
  !bi i. from_block bi i ==> ?j. MEM j bi /\ i.inst_id = j.inst_id
Proof
  rw[from_block_def] >> metis_tac[flip_operands_inst_id]
QED

(* dft_block produces a PERM of inst_ids of non-pseudo instructions *)
Theorem dft_block_perm_ids:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    PERM (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode)
               (dft_block order bb).bb_instructions))
         (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  (* Standard preamble *)
  `eda_wf eda bi` by simp[Abbr `eda`, build_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak_plain >>
     simp[] >> disch_then irule >>
     fs[bb_well_formed_def, non_pseudo_defs_before_uses_def, Abbr `bi`]) >>
  `bi <> []` by fs[bb_well_formed_def, Abbr `bi`] >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by fs[bb_well_formed_def, Abbr `bi`] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  (* non-pseudo of (phis ++ sched) = sched *)
  `FILTER (\i. ~is_pseudo i.inst_opcode)
     (FILTER (\i. is_pseudo i.inst_opcode) bi ++ sched) = sched` by
    (once_rewrite_tac[FILTER_APPEND_DISTRIB] >>
     (`FILTER (\i. ~is_pseudo i.inst_opcode)
         (FILTER (\i. is_pseudo i.inst_opcode) bi) = []` by
        simp[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]) >>
     simp[FILTER_EQ_ID]) >>
  simp[] >>
  MATCH_MP_TAC PERM_ALL_DISTINCT >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule dftPipelineInvarTheory.all_distinct_map_filter >> simp[]) >>
  rpt strip_tac >> eq_tac >> strip_tac
  (* → : from sched to bb — via from_block *)
  >- (gvs[MEM_MAP, MEM_FILTER] >>
      rename1 `MEM j sched` >>
      `from_block bi j` by
        (qspecl_then [`bi`,`order`,`eda`,`om`,`entries`,`j`]
           mp_tac (cj 1 schedule_output_from_block) >>
         simp[Abbr `sched`]) >>
      gvs[from_block_def] >>
      simp[MEM_MAP, MEM_FILTER, flip_operands_inst_id] >>
      metis_tac[])
  (* ← : from bb to sched — completeness *)
  >> (gvs[MEM_MAP, MEM_FILTER] >>
      `MEM i.inst_id (MAP (\j. j.inst_id) sched)` by
        (qspecl_then [`bi`,`order`,`eda`,`om`] mp_tac
           schedule_output_complete >>
         simp[Abbr `sched`, Abbr `entries`] >>
         disch_then (qspec_then `i` mp_tac) >> simp[Abbr `bi`]) >>
      gvs[MEM_MAP] >>
      metis_tac[])
QED

(* dft_block preserves block_perm_of, given dft_inv conditions *)
Theorem dft_block_preserves_perm_of:
  !order fn bb.
    block_perm_of fn bb /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    block_perm_of fn (dft_block order bb)
Proof
  rw[block_perm_of_def] >>
  qexists_tac `bb_orig` >> simp[dft_block_phis] >>
  conj_tac
  (* from_block transitivity *)
  >- (fs[EVERY_MEM, listTheory.MEM_FILTER] >> rpt strip_tac >>
      `from_block bb.bb_instructions i` by
        (mp_tac (Q.SPECL [`order`, `bb`, `i`] dft_block_from_orig) >>
         simp[listTheory.MEM_FILTER]) >>
      irule from_block_trans >> qexists_tac `bb.bb_instructions` >> simp[])
  (* PERM: PERM_TRANS through bb *)
  >> irule PERM_TRANS >>
  qexists_tac `MAP (\i. i.inst_id)
                 (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` >>
  simp[dft_block_perm_ids]
QED


(* ===== dft_fn preserves bb_well_formed ===== *)

(* dft_block preserves bb_well_formed: terminator stays at end,
   phis stay as prefix, non-empty *)
(* dft_block preserves bb_well_formed when terminator isn't a dep target.
   wf_ssa ensures terminators have empty outputs (via def_dominates_uses),
   hence no instruction within the block depends on them. *)
(*  Helper: terminator is an entry instruction (has no dependents) *)
Triviality terminator_is_entry:
  !bi order eda.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    MEM (LAST bi) (entry_instructions bi order eda)
Proof
  rpt strip_tac >>
  simp[entry_instructions_def, LET_THM, MEM_FILTER] >>
  conj_tac
  (* LAST bi's inst_id is not in any dep list *)
  >- (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      rpt strip_tac >> rename1 `MEM instr (FILTER _ bi)` >>
      qspecl_then [`bi`, `eda`, `order`, `instr`] mp_tac
        terminator_not_dep_target >>
      gvs[MEM_FILTER, MEM_MAP] >> metis_tac[])
  (* LAST bi is in bi *)
  >> imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")
QED

(* Helper: terminator is last among entries (FILTER preserves order) *)
Triviality filter_last_when_last_passes:
  !P l. l <> [] /\ P (LAST l) ==> FILTER P l <> [] /\ LAST (FILTER P l) = LAST l
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l = []`
  >- (gvs[LAST_DEF] >> simp[FILTER])
  >> (gvs[LAST_DEF] >>
      `FILTER P l <> [] /\ LAST (FILTER P l) = LAST l` by simp[] >>
      Cases_on `P h` >> gvs[FILTER, LAST_DEF])
QED

Triviality terminator_last_entry:
  !bi order eda.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    let entries = entry_instructions bi order eda in
    entries <> [] /\ LAST entries = LAST bi
Proof
  rpt strip_tac >> simp[LET_THM] >>
  `MEM (LAST bi) (entry_instructions bi order eda)` by
    (irule terminator_is_entry >> simp[]) >>
  simp[entry_instructions_def, LET_THM] >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  (* Establish: nps <> [] /\ LAST nps = LAST bi *)
  `nps <> [] /\ LAST nps = LAST bi` by
    (simp[Abbr `nps`] >> irule filter_last_when_last_passes >> simp[]) >>
  (* Establish: LAST bi passes the dep filter *)
  `~MEM (LAST bi).inst_id
     (FLAT (MAP (\i. MAP (\d. d.inst_id) (inst_all_deps bi order eda i)) nps))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     rename1 `MEM instr nps` >>
     qspecl_then [`bi`, `eda`, `order`, `instr`] mp_tac terminator_not_dep_target >>
     gvs[Abbr `nps`, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  (* Now apply filter_last_when_last_passes *)
  qabbrev_tac `Q = \i:instruction. ~MEM i.inst_id
     (FLAT (MAP (\i. MAP (\d. d.inst_id) (inst_all_deps bi order eda i)) nps))` >>
  `Q (LAST nps)` by simp[Abbr `Q`] >>
  drule_all filter_last_when_last_passes >>
  simp[Abbr `Q`]
QED

(* Helper: ALL_DISTINCT preserved by MAP over FILTER *)
Theorem all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  rw[] >> gvs[MEM_MAP, MEM_FILTER]
QED

(* Helper: terminator id not in FRONT entries' process stack *)
Triviality id_not_in_map_process:
  !l tid.
    id_not_in_stack tid (MAP DfsProcess l) <=>
    ~MEM tid (MAP (\i. i.inst_id) l)
Proof
  Induct >> simp[id_not_in_stack_def] >> metis_tac[]
QED

Triviality terminator_not_in_front_entries:
  !bi order eda.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    let entries = entry_instructions bi order eda in
    entries <> [] ==>
    LAST entries = LAST bi ==>
    id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))
Proof
  rpt strip_tac >> simp[LET_THM] >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  rpt strip_tac >>
  (* entries is FILTER of FILTER of bi, so ALL_DISTINCT (MAP inst_id entries) *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) entries)` by
    (simp[Abbr `entries`, entry_instructions_def, LET_THM] >>
     irule all_distinct_map_filter >> irule all_distinct_map_filter >> simp[]) >>
  (* Use MEM_FRONT_NOT_LAST on MAP inst_id entries *)
  `~MEM (LAST entries).inst_id
        (MAP (\i. i.inst_id) (FRONT entries))` by
    (qspecl_then [`MAP (\i. i.inst_id) entries`] mp_tac
       (DB.fetch "rich_list" "MEM_FRONT_NOT_LAST") >>
     simp[LAST_MAP, MAP_FRONT]) >>
  gvs[] >>
  simp[id_not_in_map_process]
QED

(* If from_block bi i and i.inst_id matches some unique element j,
   then i = j or i = flip_operands j *)
Triviality from_block_id_unique:
  !bi i j.
    from_block bi i /\ MEM j bi /\ ~is_pseudo j.inst_opcode /\
    i.inst_id = j.inst_id /\ ALL_DISTINCT (MAP (\x. x.inst_id) bi) ==>
    i = j \/ i = flip_operands j
Proof
  rw[from_block_def] >> gvs[flip_operands_inst_id] >>
  gvs[MEM_EL] >>
  `n = n'` by
    (`fEL (MAP (\x. x.inst_id) bi) n = fEL (MAP (\x. x.inst_id) bi) n'` by
       simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  gvs[]
QED

Triviality from_block_terminator_id:
  !bi i.
    from_block bi i /\ is_terminator i.inst_opcode /\
    bi <> [] /\
    ALL_DISTINCT (MAP (\x. x.inst_id) bi) /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    i.inst_id = (LAST bi).inst_id
Proof
  rpt strip_tac >>
  fs[from_block_def] >> (
    (* Both subgoals: i = j or i = flip_operands j, MEM j bi, ¬is_pseudo j.
       In the i=j case: is_terminator i = is_terminator j, direct.
       In the flip case: is_terminator (flip_operands j) = is_terminator j.
       Either way j is a terminator, hence j = LAST bi. *)
    `is_terminator j.inst_opcode` by gvs[flip_operands_is_terminator] >>
    `?n. n < LENGTH bi /\ EL n bi = j` by metis_tac[MEM_EL] >>
    `n = PRE (LENGTH bi)` by metis_tac[] >>
    `j = LAST bi` by
      (simp[LAST_EL] >> `0 < LENGTH bi` by (Cases_on `bi` >> gvs[]) >> gvs[]) >>
    gvs[flip_operands_inst_id])
QED

Triviality dft_block_wf_unique_terminator:
  !bi phis sched.
    phis = FILTER (\i. is_pseudo i.inst_opcode) bi /\
    bi <> [] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\
    sched <> [] /\
    (LAST sched).inst_id = (LAST bi).inst_id /\
    (!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) sched) ==>
    !i. i < LENGTH phis + LENGTH sched /\
        is_terminator (EL i (phis ++ sched)).inst_opcode ==>
        i = PRE (LENGTH phis + LENGTH sched)
Proof
  rpt strip_tac >>
  qpat_x_assum `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` SUBST_ALL_TAC >>
  Cases_on `i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)` >> gvs[]
  >- (`is_terminator (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode` by
        gvs[EL_APPEND1] >>
      `MEM (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi))
         (FILTER (\i. is_pseudo i.inst_opcode) bi)` by metis_tac[MEM_EL] >>
      `is_pseudo (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode` by
        gvs[MEM_FILTER] >>
      metis_tac[terminator_not_pseudo_not_flippable]) >>
  `i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi) < LENGTH sched` by simp[] >>
  `is_terminator
     (EL (i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)) sched).inst_opcode` by
    gvs[EL_APPEND2] >>
  qabbrev_tac `k = i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)` >>
  `MEM (EL k sched) sched` by metis_tac[MEM_EL] >>
  `from_block bi (EL k sched)` by metis_tac[] >>
  `(EL k sched).inst_id = (LAST bi).inst_id` by
    (irule from_block_terminator_id >> simp[] >> metis_tac[]) >>
  `0 < LENGTH sched` by (Cases_on `sched` >> gvs[]) >>
  `PRE (LENGTH sched) < LENGTH sched` by simp[] >>
  `EL k (MAP (\x. x.inst_id) sched) =
   EL (PRE (LENGTH sched)) (MAP (\x. x.inst_id) sched)` by
    (simp[EL_MAP] >> gvs[LAST_EL]) >>
  `k = PRE (LENGTH sched)` by
    (qspecl_then [`MAP (\x. x.inst_id) sched`, `k`, `PRE (LENGTH sched)`]
      mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  gvs[Abbr `k`]
QED

(* Generalized: dft_block preserves invariant triple.
   No dependency on fn or MEM bb fn.fn_blocks. *)
Theorem dft_block_well_formed_gen:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    bb_well_formed (dft_block order bb) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions) /\
    non_pseudo_defs_before_uses (dft_block order bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` >>
  qabbrev_tac `eda = build_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  (* Prerequisites — shared preamble *)
  `eda_wf eda bi` by simp[Abbr `eda`, build_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak_plain >>
     simp[non_pseudo_defs_before_uses_def] >> disch_then irule >>
     fs[bb_well_formed_def, non_pseudo_defs_before_uses_def, Abbr `bi`]) >>
  `bi <> []` by (fs[bb_well_formed_def, Abbr `bi`]) >>
  `is_terminator (LAST bi).inst_opcode` by
    fs[bb_well_formed_def, Abbr `bi`] >>
  `~is_pseudo (LAST bi).inst_opcode` by
    (drule terminator_not_pseudo_not_flippable >> simp[]) >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by
    fs[bb_well_formed_def, Abbr `bi`] >>
  `entries <> [] /\ LAST entries = LAST bi` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_last_entry) >>
     simp[LET_THM, Abbr `entries`]) >>
  `id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_not_in_front_entries) >>
     simp[LET_THM, Abbr `entries`]) >>
  `!i'. MEM i' bi /\ ~is_pseudo i'.inst_opcode ==>
       ~MEM (LAST bi).inst_id
         (MAP (\d. d.inst_id) (inst_all_deps bi order eda i'))` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `eda`, `order`, `i'`] mp_tac terminator_not_dep_target >>
     simp[]) >>
  `sched <> [] /\ (LAST sched).inst_id = (LAST bi).inst_id` by
    (qspecl_then [`bi`, `order`, `eda`, `om`] mp_tac
       (SIMP_RULE std_ss [LET_THM] schedule_terminator_last) >>
     simp[Abbr `entries`, Abbr `sched`]) >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `order`, `eda`, `om`, `entries`, `i`] mp_tac
       schedule_output_from_block >> simp[Abbr `sched`]) >>
  `MEM (LAST bi) bi` by
    (imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")) >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) phis)` by
    (simp[Abbr `phis`] >> irule all_distinct_map_filter >> simp[]) >>
  `output_producer_before bi sched` by
    (simp[Abbr `sched`] >>
     irule schedule_output_producer_before >> simp[Abbr `entries`]) >>
  rpt conj_tac
  (* ===== Part 1: bb_well_formed ===== *)
  >- suspend "wf"
  (* ===== Part 2: ALL_DISTINCT inst_ids ===== *)
  >- suspend "all_distinct"
  (* ===== Part 3: non_pseudo_defs_before_uses ===== *)
  >> suspend "np_defs_before"
QED

(* --- Part 1: bb_well_formed --- *)

Resume dft_block_well_formed_gen[wf]:
  CONV_TAC (REWRITE_CONV [bb_well_formed_def]) >> simp[] >>
  conj_tac
  (* LAST is terminator *)
  >- (simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      `from_block bi (LAST sched)` by
        (first_x_assum (qspec_then `LAST sched` mp_tac) >>
         impl_tac >- (imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")) >>
         strip_tac) >>
      drule from_block_id_unique >>
      disch_then (qspec_then `LAST bi` mp_tac) >> simp[] >>
      strip_tac >> gvs[flip_operands_is_terminator]) >>
  conj_tac
  (* unique terminator position *)
  >- (qspecl_then [`bi`, `phis`, `sched`] mp_tac dft_block_wf_unique_terminator >>
      impl_tac
      >- (conj_tac >- simp[Abbr `phis`] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          first_assum ACCEPT_TAC) >>
      strip_tac >>
      first_assum ACCEPT_TAC) >>
  (* PHI prefix *)
  (
    rpt strip_tac >>
    Cases_on `j < LENGTH phis`
    >- (
      `i < LENGTH phis` by simp[] >>
      simp[EL_APPEND1] >>
      qspecl_then [`\i. is_pseudo i.inst_opcode`, `bi`, `i`, `j`]
        mp_tac filter_el_mono >>
      simp[Abbr `phis`] >> strip_tac >>
      `(!i'' j''.
          i'' < j'' /\ j'' < LENGTH bi /\
          (EL j'' bi).inst_opcode = PHI ==>
          (EL i'' bi).inst_opcode = PHI)` by
        fs[bb_well_formed_def, Abbr `bi`] >>
      `(EL j (FILTER (\i. is_pseudo i.inst_opcode) bi ++ sched)).inst_opcode = PHI`
        by gvs[] >>
      `(EL j (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode = PHI`
        by gvs[EL_APPEND1] >>
      `(EL j' bi).inst_opcode = PHI` by gvs[] >>
      `(EL i' bi).inst_opcode = PHI` by metis_tac[] >>
      gvs[])
    >> (
      `j - LENGTH phis < LENGTH sched` by simp[] >>
      `EL j (phis ++ sched) = EL (j - LENGTH phis) sched` by simp[EL_APPEND2] >>
      `MEM (EL (j - LENGTH phis) sched) sched` by metis_tac[MEM_EL] >>
      `~is_pseudo (EL (j - LENGTH phis) sched).inst_opcode` by metis_tac[] >>
      `(EL (j - LENGTH phis) sched).inst_opcode = PHI` by gvs[] >>
      fs[is_pseudo_def]))
QED

(* --- Part 2: ALL_DISTINCT inst_ids --- *)

Resume dft_block_well_formed_gen[all_distinct]:
  simp[ALL_DISTINCT_APPEND, MAP_MAP_o] >>
  rpt strip_tac >>
  rename1 `MEM eid _` >>
  `?p. MEM p phis /\ p.inst_id = eid` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `?s. MEM s sched /\ s.inst_id = eid` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `is_pseudo p.inst_opcode` by gvs[Abbr `phis`, MEM_FILTER] >>
  `~is_pseudo s.inst_opcode` by metis_tac[] >>
  `from_block bi s` by metis_tac[] >>
  `?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\ s.inst_id = j.inst_id` by
    (gvs[from_block_def] >> metis_tac[flip_operands_inst_id]) >>
  `MEM p bi` by gvs[Abbr `phis`, MEM_FILTER] >>
  `j.inst_id = p.inst_id` by gvs[] >>
  `?n1. n1 < LENGTH bi /\ EL n1 bi = p` by metis_tac[MEM_EL] >>
  `?n2. n2 < LENGTH bi /\ EL n2 bi = j` by metis_tac[MEM_EL] >>
  `EL n1 (MAP (\i. i.inst_id) bi) = EL n2 (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  `n1 = n2` by
    (qspecl_then [`MAP (\i. i.inst_id) bi`, `n1`, `n2`]
      mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  gvs[]
QED

(* --- Part 3: defs_before_uses --- *)

(* Helper: producing_inst on append *)
Triviality producing_inst_append:
  !l1 l2 var inst. producing_inst (l1 ++ l2) var = SOME inst ==>
    producing_inst l1 var = SOME inst \/
    (producing_inst l1 var = NONE /\ producing_inst l2 var = SOME inst)
Proof
  Induct_on `l1` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[producing_inst_def]
QED

(* Helper: producing_inst gives an index *)
Triviality producing_inst_index:
  !insts var inst. producing_inst insts var = SOME inst ==>
    ?p. p < LENGTH insts /\ EL p insts = inst /\ MEM var inst.inst_outputs
Proof
  Induct_on `insts` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
  >- (qexists `0` >> simp[])
  >> (res_tac >> qexists `SUC p` >> simp[])
QED

(* Helper: producing_inst finds earliest, so any earlier definer
   implies the result is at or before that position *)
Triviality producing_inst_earliest:
  !insts var inst p.
    producing_inst insts var = SOME inst /\
    p < LENGTH insts /\ MEM var (EL p insts).inst_outputs ==>
    ?q. q <= p /\ q < LENGTH insts /\ EL q insts = inst
Proof
  Induct_on `insts` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
  >- (qexists `0` >> simp[])
  >> (Cases_on `p` >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists `SUC q` >> simp[])
QED

(* Helper: if a definer is in the list, producing_inst is not NONE *)
Triviality producing_inst_not_none:
  !insts var x. MEM x insts /\ MEM var x.inst_outputs ==>
    ?y. producing_inst insts var = SOME y
Proof
  Induct >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> simp[] >>
  gvs[] >> metis_tac[]
QED

(* Helper: from_block preserves inst_outputs *)
Triviality from_block_inst_outputs:
  !bi i. from_block bi i ==>
    ?j. MEM j bi /\ i.inst_outputs = j.inst_outputs /\
        i.inst_id = j.inst_id
Proof
  rw[from_block_def] >> gvs[] >> metis_tac[flip_operands_inst_outputs,
    flip_operands_inst_id]
QED

Resume dft_block_well_formed_gen[np_defs_before]:
  CONV_TAC (REWRITE_CONV [non_pseudo_defs_before_uses_def]) >>
  CONV_TAC (REWRITE_CONV [np_defs_before_uses_def]) >> simp[] >>
  rpt strip_tac >>
  (* User at index j is non-pseudo, so NOT in phis (phis only contain pseudos) *)
  `~(j < LENGTH phis)` by
    (spose_not_then assume_tac >>
     `EL j (phis ++ sched) = EL j phis` by simp[EL_APPEND1] >>
     `MEM (EL j phis) phis` by metis_tac[MEM_EL] >>
     `is_pseudo (EL j phis).inst_opcode` by fs[Abbr `phis`, MEM_FILTER] >>
     gvs[]) >>
  (* User is in sched at position k = j - LENGTH phis *)
  drule producing_inst_append >> strip_tac >>
  `j - LENGTH phis < LENGTH sched` by simp[] >>
  qabbrev_tac `k = j - LENGTH phis` >>
  Cases_on `producing_inst phis var` >> gvs[]
  >- (
    (* Sub-case a: producer in phis -> witness at position p *)
    drule producing_inst_index >> strip_tac >>
    qexists `p` >> simp[EL_APPEND1])
  >> (
    (* Sub-case b: producer in sched, use output_producer_before *)
    `producing_inst sched var = SOME prod` by gvs[] >>
    `EL j (phis ++ sched) = EL k sched` by simp[Abbr `k`, EL_APPEND2] >>
    `MEM (Var var) (EL k sched).inst_operands` by metis_tac[] >>
    `MEM (EL k sched) sched` by metis_tac[MEM_EL] >>
    imp_res_tac producing_inst_unique >>
    `MEM prod sched` by metis_tac[] >>
    `from_block bi prod` by metis_tac[] >>
    drule from_block_inst_outputs >> strip_tac >>
    rename1 `MEM j_orig bi` >>
    `MEM var j_orig.inst_outputs` by metis_tac[] >>
    `?prod_bi. producing_inst bi var = SOME prod_bi` by
      metis_tac[producing_inst_not_none] >>
    (* prod_bi is non-pseudo: if pseudo, it'd be in phis, contradicting
       producing_inst phis var = NONE *)
    `~is_pseudo prod_bi.inst_opcode` by
      (spose_not_then assume_tac >>
       imp_res_tac producing_inst_unique >>
       `MEM prod_bi phis` by fs[Abbr `phis`, MEM_FILTER] >>
       `?z. producing_inst phis var = SOME z` by
         metis_tac[producing_inst_not_none] >>
       gvs[]) >>
    (* output_producer_before gives exists m < k with matching inst_id *)
    qpat_x_assum `output_producer_before _ _`
      (fn th => assume_tac (REWRITE_RULE [output_producer_before_def] th)) >>
    first_x_assum (qspecl_then [`k`, `var`, `prod_bi`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rename1 `m < k` >>
    `m < LENGTH sched` by simp[] >>
    `MEM (EL m sched) sched` by metis_tac[MEM_EL] >>
    `from_block bi (EL m sched)` by metis_tac[] >>
    drule from_block_inst_outputs >> strip_tac >>
    rename1 `MEM j2 bi` >>
    `j2.inst_id = prod_bi.inst_id` by metis_tac[] >>
    `MEM prod_bi bi` by (imp_res_tac producing_inst_unique >> simp[]) >>
    (* ALL_DISTINCT inst_ids: j2 = prod_bi *)
    `?n1. n1 < LENGTH bi /\ EL n1 bi = j2` by metis_tac[MEM_EL] >>
    `?n2. n2 < LENGTH bi /\ EL n2 bi = prod_bi` by metis_tac[MEM_EL] >>
    `EL n1 (MAP (\i. i.inst_id) bi) = EL n2 (MAP (\i. i.inst_id) bi)` by
      simp[EL_MAP] >>
    `n1 = n2` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
    `j2 = prod_bi` by gvs[] >>
    `MEM var (EL m sched).inst_outputs` by
      (imp_res_tac producing_inst_unique >> gvs[]) >>
    drule_all producing_inst_earliest >>
    strip_tac >> rename1 `q <= m` >>
    qexists `LENGTH phis + q` >> simp[EL_APPEND2, Abbr `k`])
QED

Finalise dft_block_well_formed_gen

(* Original: dft_block preserves well-formedness for original blocks *)
Theorem dft_block_well_formed:
  !fn order bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    bb_well_formed (dft_block order bb)
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by (gvs[wf_function_def, EVERY_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule wf_fn_block_inst_ids_distinct >> metis_tac[]) >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >>
     irule wf_ssa_defs_before_uses >> metis_tac[]) >>
  metis_tac[dft_block_well_formed_gen]
QED

Triviality dft_block_preserves_output_distinct[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (dft_block order bb).bb_instructions))
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` >>
  qabbrev_tac `eda = build_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  `eda_wf eda bi` by simp[Abbr `eda`, build_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (fs[Abbr `eda`, Abbr `bi`, bb_well_formed_def,
        non_pseudo_defs_before_uses_def] >>
     metis_tac[eda_topo_compatible_gen_weak_plain]) >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `bi <> []` by fs[bb_well_formed_def, Abbr `bi`] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by fs[bb_well_formed_def, Abbr `bi`] >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  `EVERY (from_block bi) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis))` by
    (simp[Abbr `phis`] >> irule all_distinct_flat_map_filter >> simp[Abbr `bi`]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) sched))` by
    (mp_tac (Q.SPECL [`bi`, `sched`] from_block_list_outputs_distinct) >>
     simp[Abbr `bi`]) >>
  `!x a b.
     MEM a phis /\ MEM b sched /\
     MEM x a.inst_outputs /\ MEM x b.inst_outputs ==> F` by
    (simp[Abbr `phis`] >> metis_tac[pseudo_from_block_outputs_disjoint]) >>
  metis_tac[all_distinct_flat_map_append_disjoint]
QED

(* Helper: MAP with conditional replacement preserves EVERY *)
Theorem every_map_replace:
  !P bbs lbl bb'.
    EVERY P bbs /\ P bb' ==>
    EVERY P (MAP (\b. if b.bb_label = lbl then bb' else b) bbs)
Proof
  Induct_on `bbs` >> simp[] >> rpt strip_tac >> rw[]
QED

(* FUNPOW invariant predicate *)
Definition dft_inv_def:
  dft_inv bbs <=>
    EVERY (\bb. bb_well_formed bb /\
                ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
                non_pseudo_defs_before_uses bb.bb_instructions /\
                ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))) bbs
End

(* dft_process_one preserves dft_inv *)
Theorem dft_process_one_preserves_inv:
  !cfg lr fn st lbl.
    dft_inv st.dls_blocks ==>
    dft_inv (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[dft_inv_def] >>
  irule every_map_replace >> simp[] >>
  fs[dft_inv_def] >>
  `MEM x st.dls_blocks` by
    (fs[lookup_block_def] >> imp_res_tac venomExecPropsTheory.FIND_MEM) >>
  `bb_well_formed x /\ ALL_DISTINCT (MAP (\i. i.inst_id) x.bb_instructions) /\
   non_pseudo_defs_before_uses x.bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) x.bb_instructions))` by fs[EVERY_MEM] >>
  drule_all dft_block_well_formed_gen >> strip_tac >>
  drule_all dft_block_preserves_output_distinct >> strip_tac >>
  simp[]
QED

(* dft_loop_step preserves dft_inv *)
Theorem dft_loop_step_preserves_inv:
  !cfg lr fn trip.
    dft_inv (FST trip).dls_blocks ==>
    dft_inv (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_inv >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

(* FUNPOW preserves dft_inv *)
Theorem funpow_dft_loop_preserves_inv:
  !n cfg lr fn trip.
    dft_inv (FST trip).dls_blocks ==>
    dft_inv (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_preserves_inv >>
  first_x_assum irule >> simp[]
QED

(* Core: dft_fn preserves dft_inv *)
(* Original blocks satisfy dft_inv *)
Theorem wf_fn_initial_dft_inv:
  !fn. wf_ssa fn /\ wf_function fn ==> dft_inv fn.fn_blocks
Proof
  rpt strip_tac >> simp[dft_inv_def, EVERY_MEM] >> rpt strip_tac
  >- (gvs[wf_function_def, EVERY_MEM])
  >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
  >- (simp[non_pseudo_defs_before_uses_def] >>
      irule wf_ssa_defs_before_uses >> metis_tac[])
  >> (`ALL_DISTINCT
        (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                fn.fn_blocks))` by
        gvs[wf_ssa_def, ssa_form_def, fn_insts_def,
            flat_map_outputs_fn_insts_blocks] >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                    fn.fn_blocks` >>
      simp[MEM_MAP] >> metis_tac[])
QED

(* dft_fn output satisfies dft_inv *)
Theorem dft_fn_dft_inv:
  !fn. wf_ssa fn /\ wf_function fn ==> dft_inv (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  MATCH_MP_TAC funpow_dft_loop_preserves_inv >>
  drule_all wf_fn_initial_dft_inv >> simp[]
QED

(* ===== FUNPOW invariant: blocks maintain block_perm_of ===== *)

(* Predicate: every block in bbs is block_perm_of fn *)
Definition all_blocks_perm_of_def:
  all_blocks_perm_of fn bbs <=>
    EVERY (block_perm_of fn) bbs
End

(* dft_process_one preserves all_blocks_perm_of, given dft_inv *)
Theorem dft_process_one_preserves_perm:
  !cfg lr fn st lbl.
    all_blocks_perm_of fn st.dls_blocks /\ dft_inv st.dls_blocks ==>
    all_blocks_perm_of fn (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[all_blocks_perm_of_def] >>
  irule every_map_replace >> simp[] >>
  fs[all_blocks_perm_of_def, dft_inv_def] >>
  irule dft_block_preserves_perm_of >>
  fs[lookup_block_def] >>
  imp_res_tac venomExecPropsTheory.FIND_MEM >>
  fs[EVERY_MEM]
QED

(* FUNPOW lifting: dft_loop_step preserves all_blocks_perm_of *)
Theorem dft_loop_step_preserves_perm:
  !cfg lr fn trip.
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    all_blocks_perm_of fn (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_perm >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem funpow_dft_loop_preserves_perm:
  !n cfg lr fn trip.
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    all_blocks_perm_of fn
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  MATCH_MP_TAC (SRULE [] dft_loop_step_preserves_perm) >>
  conj_tac
  >- (first_x_assum MATCH_MP_TAC >> simp[] >>
      MATCH_MP_TAC funpow_dft_loop_preserves_inv >> simp[])
  >> (MATCH_MP_TAC funpow_dft_loop_preserves_inv >> simp[])
QED

(* Core: dft_fn blocks are all block_perm_of fn *)
Theorem dft_fn_all_perm_of:
  !fn.
    wf_ssa fn /\ wf_function fn ==>
    all_blocks_perm_of fn (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >> simp[dft_fn_def, LET_THM] >>
  rewrite_tac[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  irule funpow_dft_loop_preserves_perm >>
  simp[all_blocks_perm_of_def, EVERY_MEM, original_block_perm_of] >>
  irule wf_fn_initial_dft_inv >> simp[]
QED


(* All blocks in dft_fn are well-formed *)
Theorem dft_fn_blocks_well_formed:
  !fn bb'.
    wf_ssa fn /\ wf_function fn /\ MEM bb' (dft_fn fn).fn_blocks ==>
    bb_well_formed bb'
Proof
  rpt strip_tac >>
  drule_all dft_fn_dft_inv >> strip_tac >>
  gvs[dft_inv_def, EVERY_MEM]
QED

(* ===== DFT output topo_sorted w.r.t. original deps ===== *)

(* topo_sorted_map: subsumed by map_choose_original_topo_sorted_restricted *)

(* flip_operands_inst_outputs: already in dftStructuralTheory *)

(* flip_operands preserves set of operand_vars *)
Triviality flip_operands_operand_vars_set:
  !i. set (operand_vars (flip_operands i).inst_operands) =
      set (operand_vars i.inst_operands)
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  TRY (IF_CASES_TAC >> simp[]) >>
  (* Two-operand case: [a; b] → [b; a] *)
  simp[operand_vars_def] >>
  every_case_tac >> gvs[EXTENSION] >> metis_tac[]
QED

(* full_dep only depends on inst_id for from_block elements:
   from_block preserves inst_id, set(inst_defs), and set(inst_uses).
   So full_dep(eda)(x, y) ⟺ full_dep(eda)(x', y') when inst_ids match
   and all instructions are from_block elements of the same block.
   Proof: eda_dep only uses inst_id (proven as eda_dep_inst_id_only).
          inst_defs = inst_outputs preserved by flip_operands_inst_outputs.
          set(inst_uses) = set(operand_vars) preserved by flip_operands_operand_vars_set.
   This condition is exactly what map_choose_original_topo_sorted_restricted needs. *)


(* ===== Function-level: run_blocks lift_result ===== *)

(* Specialized rewrite for run_blocks (SUC fuel) — avoids hanging issues
   with simp/ONCE_REWRITE_TAC on the recursive definition *)
val run_blocks_SUC = let
  val rb = run_blocks_def
  val (vars, _) = strip_forall (concl rb)
  val [sv,fv,fnv,cv] = vars
  val inst = SPECL [sv, mk_comb(``SUC``, fv), fnv, cv] rb
in SIMP_RULE (srw_ss()) [] inst |> GENL [sv, fv, fnv, cv] end;

(* DFT preserves fn_pseudos_prefix: dft_block outputs pseudos ++ scheduled,
   and scheduled contains only non-pseudo instructions. *)
Triviality dft_block_pseudos_prefix[local]:
  !order bb. pseudos_prefix (dft_block order bb)
Proof
  rpt strip_tac >>
  simp[pseudos_prefix_def, dft_block_def, LET_THM] >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `sched = schedule_from_entries bb.bb_instructions order
    (build_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions order)
    (entry_instructions bb.bb_instructions order
      (build_eda bb.bb_instructions))` >>
  rpt strip_tac >>
  Cases_on `j < LENGTH phis`
  >- (
    `i < LENGTH phis` by decide_tac >>
    `EL i (phis ++ sched) = EL i phis` by simp[EL_APPEND1] >>
    `MEM (EL i phis) phis` by metis_tac[MEM_EL] >>
    gvs[Abbr `phis`, MEM_FILTER]) >>
  `j - LENGTH phis < LENGTH sched` by simp[] >>
  `EL j (phis ++ sched) = EL (j - LENGTH phis) sched` by simp[EL_APPEND2] >>
  `MEM (EL (j - LENGTH phis) sched) sched` by metis_tac[MEM_EL] >>
  `~is_pseudo (EL (j - LENGTH phis) sched).inst_opcode` by
    metis_tac[schedule_output_from_block, build_eda_wf,
              entry_instructions_mem] >>
  gvs[]
QED

(* The plain Python EDA omits the conservative barrier/abort/ALLOCA chains.
   Semantic correctness therefore requires the explicit compiler invariant that
   its schedule still respects the full dependency relation. *)
Definition dft_schedule_safe_def:
  dft_schedule_safe <=>
    !bb order.
      bb_well_formed bb /\
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
      non_pseudo_defs_before_uses bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
      topo_sorted (full_dep (build_full_eda bb.bb_instructions))
        (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions) /\
      topo_sorted (full_dep (build_full_eda bb.bb_instructions))
        (MAP (choose_original (block_body bb))
          (block_body (dft_block order bb)))
End

(* dft_schedule_safe is false, so every theorem below that assumes it is
   vacuous.  In MSTORE %p %v; ASSERT %x; RETURN %p 32 the plain EDA that
   dft_block schedules from gives ASSERT no edges, so DFT emits it first,
   while build_full_eda's barrier chain makes ASSERT depend on the MSTORE. *)
Definition assert_hoist_block_def:
  assert_hoist_block =
    <| bb_label := "entry";
       bb_instructions :=
         [<|inst_id := 1; inst_opcode := MSTORE;
            inst_operands := [Var "p"; Var "v"]; inst_outputs := []|>;
          <|inst_id := 2; inst_opcode := ASSERT;
            inst_operands := [Var "x"]; inst_outputs := []|>;
          <|inst_id := 3; inst_opcode := RETURN;
            inst_operands := [Var "p"; Lit 32w]; inst_outputs := []|>] |>
End

Theorem assert_hoist_schedule[local]:
  (dft_block [] assert_hoist_block).bb_instructions =
  [EL 1 assert_hoist_block.bb_instructions;
   EL 0 assert_hoist_block.bb_instructions;
   EL 2 assert_hoist_block.bb_instructions]
Proof
  EVAL_TAC
QED

Theorem lt3_cases[local]:
  (n:num) < 3 <=> n = 0 \/ n = 1 \/ n = 2
Proof
  decide_tac
QED

Theorem dft_schedule_safe_false:
  ~dft_schedule_safe
Proof
  simp[dft_schedule_safe_def] >>
  qexistsl [`assert_hoist_block`, `[]`] >> rpt conj_tac
  >- simp[bb_well_formed_def, assert_hoist_block_def, is_terminator_def,
          lt3_cases, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM,
          FORALL_AND_THM]
  >- EVAL_TAC
  >- simp[non_pseudo_defs_before_uses_def, np_defs_before_uses_def,
          assert_hoist_block_def, producing_inst_def,
          lt3_cases, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM,
          FORALL_AND_THM]
  >- EVAL_TAC
  >- (simp[assert_hoist_schedule, topo_sorted_def] >> disj1_tac >>
      qexistsl [`0`, `1`] >>
      EVAL_TAC >> simp[])
QED




Triviality error_or_lift_trans[local]:
  !r1 r2 r3.
    (((?e. r1 = Error e) /\ (?e. r2 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r1 r2) /\
    (((?e. r2 = Error e) /\ (?e. r3 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r2 r3) ==>
    (((?e. r1 = Error e) /\ (?e. r3 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r1 r3)
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  gvs[lift_result_def, revert_equiv_def] >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

Triviality dft_process_one_pseudos_prefix[local]:
  !cfg lr fn st lbl.
    (!bb. MEM bb st.dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (dft_process_one cfg lr fn st lbl)).dls_blocks ==>
         pseudos_prefix bb
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `MEM bb _` mp_tac >>
  simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  TRY (Cases_on `so_analyze_block cfg lr st.dls_from_to lbl x.bb_instructions` >> simp[] >>
       Cases_on `so_get_stack cfg lr (fn with fn_blocks := st.dls_blocks)
         (so_record_from_to cfg st.dls_from_to lbl q) lbl` >> simp[] >>
       BasicProvers.TOP_CASE_TAC >> simp[] >>
       gvs[MEM_MAP] >> metis_tac[dft_block_pseudos_prefix] >> NO_TAC) >>
  metis_tac[]
QED

Triviality dft_loop_step_pseudos_prefix[local]:
  !cfg lr fn trip.
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (dft_loop_step cfg lr fn trip)).dls_blocks ==>
         pseudos_prefix bb
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def] >>
  IF_CASES_TAC >> simp[] >>
  TRY (Cases_on `trip1` >> simp[] >>
       TRY (rpt strip_tac >>
            `!bb. MEM bb (FST (dft_process_one cfg lr fn trip0 h)).dls_blocks ==>
                  pseudos_prefix bb` by
              (mp_tac (Q.SPECL [`cfg`, `lr`, `fn`, `trip0`, `h`]
                 dft_process_one_pseudos_prefix) >> simp[]) >>
            Cases_on `dft_process_one cfg lr fn trip0 h` >>
            Cases_on `r` >> Cases_on `q'` >>
            gvs[] >> metis_tac[] >> NO_TAC) >>
       metis_tac[] >> NO_TAC) >>
  metis_tac[]
QED

Triviality funpow_dft_loop_pseudos_prefix[local]:
  !n cfg lr fn trip.
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks ==>
         pseudos_prefix bb
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  qabbrev_tac `tripn = FUNPOW (dft_loop_step cfg lr fn) n trip` >>
  `!bb. MEM bb (FST tripn).dls_blocks ==> pseudos_prefix bb` by
    (qunabbrev_tac `tripn` >>
     qpat_x_assum `!cfg lr fn trip. _`
       (qspecl_then [`cfg`, `lr`, `fn`, `trip`] mp_tac) >>
     simp[]) >>
  mp_tac (Q.SPECL [`cfg`, `lr`, `fn`, `tripn`]
    dft_loop_step_pseudos_prefix) >>
  simp[] >> disch_then (qspec_then `bb` mp_tac) >> simp[Abbr `tripn`]
QED

Triviality dft_fn_pseudos_prefix:
  !fn. fn_pseudos_prefix fn ==> fn_pseudos_prefix (dft_fn fn)
Proof
  rw[dft_fn_def, fn_pseudos_prefix_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qabbrev_tac `steps = LENGTH fn.fn_blocks * LENGTH fn.fn_blocks` >>
  qabbrev_tac `trip = (<|dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
                         dls_last_order := FEMPTY|>,
                       (cfg_analyze fn).cfg_dfs_post,F)` >>
  qabbrev_tac `res = FUNPOW (dft_loop_step (cfg_analyze fn)
      (liveness_analyze fn) fn) steps trip` >>
  `!bb. MEM bb (FST res).dls_blocks ==> pseudos_prefix bb` by
    (qunabbrev_tac `res` >>
     mp_tac (Q.SPECL [`steps`, `cfg_analyze fn`, `liveness_analyze fn`, `fn`, `trip`]
       funpow_dft_loop_pseudos_prefix) >>
     simp[Abbr `trip`, Abbr `steps`, fn_pseudos_prefix_def]) >>
  PairCases_on `res` >> gvs[]
QED

Definition run_block_compare_def:
  run_block_compare bb bb' <=>
    !fuel ctx s.
      (((?e. run_block fuel ctx bb s = Error e) /\
        (?e. run_block fuel ctx bb' s = Error e)) \/
       lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
         (run_block fuel ctx bb s)
         (run_block fuel ctx bb' s))
End

Definition all_blocks_run_rel_def:
  all_blocks_run_rel fn bbs <=>
    !bb bb'.
      MEM bb fn.fn_blocks /\ MEM bb' bbs /\
      bb.bb_label = bb'.bb_label ==>
      run_block_compare bb bb'
End

(* ===== canonical_topo_inv for dft_fn loop ===== *)

Definition canonical_topo_inv_def:
  canonical_topo_inv fn blocks <=>
    !bb. MEM bb blocks ==>
      ?bb_orig. MEM bb_orig fn.fn_blocks /\
        bb.bb_label = bb_orig.bb_label /\
        topo_sorted (canonical_dep bb_orig.bb_instructions)
          (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)
End