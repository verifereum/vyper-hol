(*
 * Pass Shared Properties (API)
 *
 * Re-exports theorems from proof files. Inline proofs only for
 * trivial one-liners or cheated stubs.
 *
 * TOP-LEVEL:
 *   Instruction builders:
 *     mk_nop_inst_correct        — NOP replacement is identity on state
 *     mk_assign_inst_correct     — ASSIGN replacement evaluates and binds output
 *
 *   NOP clearing:
 *     clear_nops_block_correct    — removing NOPs preserves execution (result_equiv)
 *     clear_nops_function_correct — removing NOPs preserves execution (result_equiv)
 *
 *   Operand substitution:
 *     subst_operand_eval           — single substitution preserves eval_operand
 *     subst_op_map_eval            — map substitution preserves eval_operand
 *     subst_operand_eval_operands  — single substitution preserves eval_operands
 *     subst_op_map_eval_operands   — map substitution preserves eval_operands
 *     subst_operands_correct       — single substitution preserves step_inst
 *     subst_operands_map_correct   — map substitution preserves step_inst
 *
 *   State preservation:
 *     step_inst_preserves_all              — 18-conjunct field preservation
 *     step_base_preserves_tracked          — step_inst_base field preservation
 *     eligible_no_write_balance_extcode    — eligible ops don't write BALANCE/EXTCODE
 *
 *   Transfer/determinism:
 *     step_inst_base_ok_transfer           — OK transfers across agreeing states
 *     step_inst_base_output_determined_fields — per-field output determinism
 *
 *   Variable frame:
 *     step_inst_base_var_frame_full        — step_inst_base preserves non-output vars
 *     step_inst_var_frame_full             — step_inst preserves non-output vars
 *
 *   Commutativity:
 *     effects_independent_commute          — independent instructions commute
 *)

Theory passSharedProps
Ancestors
  passSharedDefs venomExecSemantics venomEffects stateEquiv venomInstProofs
  passSharedField passSharedTransfer passSharedVarFrame passSharedFrame
  passSharedSubst instIdxIndep

open venomStateTheory venomInstTheory;

(* ===================================================================== *)
(* ===== Instruction builders (trivial) ================================ *)
(* ===================================================================== *)

Theorem mk_nop_inst_correct:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rw[mk_nop_inst_def, step_inst_def, step_inst_base_def]
QED

Theorem mk_assign_inst_correct:
  !fuel ctx inst src_op s v out.
    eval_operand src_op s = SOME v /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx (mk_assign_inst inst src_op) s =
      OK (update_var out v s)
Proof
  rw[mk_assign_inst_def, step_inst_def, step_inst_base_def] >> rw[]
QED

(* ===================================================================== *)
(* ===== NOP clearing ================================================= *)
(* ===================================================================== *)

(* FILTER/TAKE helpers for index correspondence *)

Triviality filter_take_el:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    EL (LENGTH (FILTER P (TAKE i l))) (FILTER P l) = EL i l
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_nop:
  !l (P:'a -> bool) i. i < LENGTH l /\ ~P (EL i l) ==>
    LENGTH (FILTER P (TAKE (SUC i) l)) = LENGTH (FILTER P (TAKE i l))
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_keep:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    LENGTH (FILTER P (TAKE (SUC i) l)) = SUC (LENGTH (FILTER P (TAKE i l)))
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_lt:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    LENGTH (FILTER P (TAKE i l)) < LENGTH (FILTER P l)
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_all:
  !l (P:'a -> bool) i. LENGTH l <= i ==> FILTER P (TAKE i l) = FILTER P l
Proof
  Induct >> simp[]
QED

(* Combined helpers: NOP-skip and non-NOP index correspondence.
   Pre-specialized to avoid beta-redex issues with irule/metis_tac. *)
Triviality nop_skip_facts:
  !bb s fuel ctx.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = NOP ==>
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))) /\
    run_block fuel ctx bb s =
    run_block fuel ctx bb (s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac
  >- (irule filter_take_nop >> simp[])
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
      simp[get_instruction_def, step_nop_identity] >> EVAL_TAC)
QED

Triviality non_nop_idx_facts:
  !bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> NOP ==>
    (EL (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                        (TAKE s.vs_inst_idx bb.bb_instructions)))
        (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions) =
     EL s.vs_inst_idx bb.bb_instructions) /\
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions)) <
     LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions)) /\
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     SUC (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                         (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  rpt strip_tac
  >- (irule filter_take_el >> simp[])
  >- (irule filter_take_lt >> simp[])
  >- (irule filter_take_keep >> simp[])
QED

Triviality filter_take_all_nop:
  !bb i. LENGTH bb.bb_instructions <= i ==>
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                   (TAKE i bb.bb_instructions)) =
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions)
Proof
  rw[] >> AP_TERM_TAC >> irule filter_take_all >> simp[]
QED

(* Past-end case: both sides get NONE from get_instruction *)
Triviality clear_nops_past_end:
  !fuel ctx bb s.
    ~(s.vs_inst_idx < LENGTH bb.bb_instructions) ==>
    run_block fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE s.vs_inst_idx bb.bb_instructions))) =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  `LENGTH bb.bb_instructions <= s.vs_inst_idx` by DECIDE_TAC >>
  imp_res_tac filter_take_all_nop >>
  ONCE_REWRITE_TAC[run_block_def] >>
  gvs[get_instruction_def, clear_nops_block_def]
QED

(* NOP case: skip in original, filtered index unchanged, apply IH *)
Triviality clear_nops_nop_step:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = NOP /\
    run_block fuel ctx (clear_nops_block bb)
      ((s with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE (SUC s.vs_inst_idx) bb.bb_instructions))) =
    run_block fuel ctx bb (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
    run_block fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE s.vs_inst_idx bb.bb_instructions))) =
    run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  imp_res_tac nop_skip_facts >> gvs[]
QED

(* NOP removal preserves execution up to vs_inst_idx.
   Why true: step_inst on NOP returns OK s (identity). run_block increments
   vs_inst_idx after each non-terminator, so skipping a NOP just skips an
   idx increment. For OK results (JMP/JNZ terminators), jump_to resets
   vs_inst_idx := 0 so state_equiv {} holds. For Halt/Revert, vs_inst_idx
   differs but execution_equiv {} ignores it.

   Proof approach: induction on run_block (or on instruction list length).
   Key facts: step_inst NOP = OK s (from step_inst_base_def),
   FILTER removes NOPs, result_equiv = lift_result state_equiv execution_equiv.

   The block-level result propagates to function-level by fuel induction:
   run_function calls run_block then recurses. The OK case has vs_inst_idx=0
   (from jump_to), so the inductive hypothesis applies. Terminal cases use
   execution_equiv which ignores vs_inst_idx. *)
(* Non-terminator step_inst at different idx: OK results agree modulo idx.
   Covers both INVOKE and non-INVOKE non-terminator instructions. *)
(* Non-terminator step_inst at different idx: OK results agree modulo idx.
   Covers both INVOKE and non-INVOKE non-terminator instructions.
   Why: step_inst never reads vs_inst_idx; it only reads/writes other fields. *)
Triviality foldl_update_var_idx:
  !ps st j.
    FOLDL (\s' (out,val). update_var out val s') (st with vs_inst_idx := j) ps =
    FOLDL (\s' (out,val). update_var out val s') st ps with vs_inst_idx := j
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  `update_var p_1 p_2 (st with vs_inst_idx := j) =
   update_var p_1 p_2 st with vs_inst_idx := j` by
    simp[update_var_def] >>
  simp[]
QED

Triviality bind_outputs_idx:
  !outs vals st j.
    bind_outputs outs vals (st with vs_inst_idx := j) =
    OPTION_MAP (\s'. s' with vs_inst_idx := j) (bind_outputs outs vals st)
Proof
  rw[bind_outputs_def, foldl_update_var_idx]
QED

(* Non-terminator step_inst at different idx:
   - OK results: state shifted by idx
   - Non-OK results: execution_equiv {} (ignores idx)
   This is what clear_nops_block_gen needs. *)
Triviality step_inst_non_term_idx:
  !fuel ctx inst s j.
    ~is_terminator inst.inst_opcode ==>
    (case step_inst fuel ctx inst s of
       OK v =>
         step_inst fuel ctx inst (s with vs_inst_idx := j) =
         OK (v with vs_inst_idx := j)
     | _ =>
         result_equiv {}
           (step_inst fuel ctx inst (s with vs_inst_idx := j))
           (step_inst fuel ctx inst s))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[step_inst_def, eval_ops_inst_idx] >>
    Cases_on `decode_invoke inst` >> simp[result_equiv_def] >>
    Cases_on `x` >> simp[] >>
    Cases_on `lookup_function q ctx.ctx_functions` >>
    simp[result_equiv_def] >>
    Cases_on `eval_operands r s` >> simp[result_equiv_def] >>
    rename1 `eval_operands _ s = SOME args` >>
    rename1 `lookup_function _ _ = SOME callee_fn` >>
    `setup_callee callee_fn args (s with vs_inst_idx := j) =
     setup_callee callee_fn args s` by simp[setup_callee_def] >>
    simp[] >>
    Cases_on `setup_callee callee_fn args s` >>
    simp[result_equiv_def] >>
    rename1 `setup_callee _ _ s = SOME callee_s` >>
    Cases_on `run_function fuel ctx callee_fn callee_s` >>
    simp[result_equiv_def, execution_equiv_def, lookup_var_def,
         venom_state_component_equality] >>
    (* IntRet case *)
    rename1 `run_function _ _ _ _ = IntRet ret_vals callee_s'` >>
    `merge_callee_state (s with vs_inst_idx := j) callee_s' =
     merge_callee_state s callee_s' with vs_inst_idx := j` by
      simp[merge_callee_state_def, venom_state_component_equality] >>
    simp[bind_outputs_idx] >>
    Cases_on `bind_outputs inst.inst_outputs ret_vals
                (merge_callee_state s callee_s')` >>
    simp[result_equiv_def, execution_equiv_def, lookup_var_def,
         venom_state_component_equality]
  ) >>
  (* Non-INVOKE: step_inst = step_inst_base, use idx_indep *)
  simp[step_inst_non_invoke, step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base inst s` >>
  simp[exec_result_map_def, result_equiv_def, execution_equiv_def,
       lookup_var_def, venom_state_component_equality]
QED

(* Terminator step_inst_base at different idx gives result_equiv {}.
   Key insight: normalization (rw) MUST come before Cases_on. *)
Triviality step_inst_base_term_result_equiv:
  !inst s j.
    is_terminator inst.inst_opcode ==>
    result_equiv {}
      (case step_inst_base inst s of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
      (case step_inst_base inst (s with vs_inst_idx := j) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  qabbrev_tac `r1 = step_inst_base inst s` >>
  qabbrev_tac `r2 = step_inst_base inst (s with vs_inst_idx := j)` >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0) r2 =
   exec_result_map (\s'. s' with vs_inst_idx := 0) r1` by
    simp[Abbr `r1`, Abbr `r2`, terminator_step_inst_base_idx_norm0] >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[exec_result_map_def] >>
  (* All cross-constructor cases eliminated by gvs. Remaining: same constructor. *)
  (* From v' with idx:=0 = v with idx:=0, extract all non-idx fields equal *)
  gvs[venom_state_component_equality] >>
  simp[result_equiv_def, execution_equiv_def, lookup_var_def] >>
  (* OK-OK case: use terminator_OK_inst_idx_0 to get idx=0 *)
  imp_res_tac terminator_OK_inst_idx_0 >> gvs[] >>
  Cases_on `v.vs_halted` >>
  simp[result_equiv_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, venom_state_component_equality]
QED

(* Generalized: relates run_block at any idx to run_block on filtered block
   at the corresponding filtered index. *)
Triviality clear_nops_block_gen:
  !fuel ctx bb s.
    result_equiv {}
      (run_block fuel ctx bb s)
      (run_block fuel ctx (clear_nops_block bb)
        (s with vs_inst_idx :=
          LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                         (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  (* Unroll one step of run_block on the original side *)
  simp[Once run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (
    (* Past end: both sides get NONE *)
    `~(s.vs_inst_idx < LENGTH bb.bb_instructions)` by
      fs[get_instruction_def] >>
    `LENGTH bb.bb_instructions <= s.vs_inst_idx` by DECIDE_TAC >>
    imp_res_tac filter_take_all_nop >>
    simp[Once run_block_def, get_instruction_def, clear_nops_block_def,
         result_equiv_def]
  ) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (
    (* NOP case: original steps identity, filtered index unchanged *)
    `step_inst fuel ctx inst s = OK s` by
      simp[step_nop_identity] >>
    `~is_terminator NOP` by EVAL_TAC >>
    simp[] >>
    `LENGTH (FILTER (\i. i.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     LENGTH (FILTER (\i. i.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))` by
      (irule filter_take_nop >> gvs[]) >>
    first_x_assum (qspecl_then [`inst`, `s`] mp_tac) >>
    gvs[]
  ) >>
  (* Non-NOP case: both sides execute the same instruction *)
  imp_res_tac non_nop_idx_facts >> rfs[] >>
  qabbrev_tac `j = LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))` >>
  `get_instruction (clear_nops_block bb) j = SOME inst` by
    simp[get_instruction_def, clear_nops_block_def] >>
  Cases_on `is_terminator inst.inst_opcode` >- (
    (* Terminator case *)
    `inst.inst_opcode <> INVOKE` by
      (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
    simp[step_inst_non_invoke] >>
    simp[Once run_block_def, step_inst_non_invoke] >>
    irule step_inst_base_term_result_equiv >> simp[]
  ) >>
  (* Non-terminator case *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `j`] step_inst_non_term_idx) >>
  simp[] >> Cases_on `step_inst fuel ctx inst s` >> simp[]
  (* OK case: have step_inst ... (s with idx:=j) = OK (v with idx:=j) *)
  >- (
    strip_tac >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[] >> fs[] >>
    first_x_assum match_mp_tac >> simp[]
  ) >>
  (* Non-OK cases: have result_equiv {} (step_inst ... shifted) (original) *)
  disch_then assume_tac >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst (s with vs_inst_idx := j)` >>
  fs[result_equiv_def, execution_equiv_def, lookup_var_def,
     venom_state_component_equality]
QED

Theorem clear_nops_block_correct:
  !fuel ctx bb s.
    s.vs_inst_idx = 0 ==>
    result_equiv {}
      (run_block fuel ctx bb s)
      (run_block fuel ctx (clear_nops_block bb) s)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] clear_nops_block_gen) >>
  `s with vs_inst_idx := 0 = s` by gvs[venom_state_component_equality] >>
  simp[]
QED

Triviality lookup_block_clear_nops:
  !lbl bbs. lookup_block lbl (MAP clear_nops_block bbs) =
            OPTION_MAP clear_nops_block (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm, clear_nops_block_def] >>
  rw[] >> fs[lookup_block_def, clear_nops_block_def]
QED

Triviality run_block_ok_inst_idx_0:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  pop_assum mp_tac >> simp[Once run_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  rw[] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  fs[step_inst_non_invoke] >>
  imp_res_tac terminator_OK_inst_idx_0
QED

Triviality state_equiv_empty_eq:
  !s1 s2. state_equiv {} s1 s2 ==> s1 = s2
Proof
  rw[state_equiv_def, execution_equiv_def, venom_state_component_equality,
     lookup_var_def] >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by metis_tac[] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, EQ_EXT]
QED

Triviality result_equiv_empty_ok:
  !s1 s2.
    result_equiv {} (OK s1) (OK s2) ==> s1 = s2
Proof
  rw[result_equiv_def, state_equiv_def, execution_equiv_def,
     venom_state_component_equality, lookup_var_def] >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by metis_tac[] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, EQ_EXT]
QED

Theorem clear_nops_function_correct:
  !fuel ctx fn s.
    s.vs_inst_idx = 0 ==>
    result_equiv {}
      (run_function fuel ctx fn s)
      (run_function fuel ctx (clear_nops_function fn) s)
Proof
  Induct_on `fuel` >> rpt strip_tac >>
  once_rewrite_tac[run_function_def] >>
  simp[clear_nops_function_def, lookup_block_clear_nops] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[result_equiv_def] >>
  rename1 `SOME bb` >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] clear_nops_block_correct) >>
  simp[] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
  simp[result_equiv_def] >> strip_tac >>
  imp_res_tac state_equiv_empty_eq >>
  imp_res_tac run_block_ok_inst_idx_0 >> gvs[] >>
  rw[] >>
  simp[result_equiv_def, execution_equiv_def, lookup_var_def,
       clear_nops_function_def] >>
  rewrite_tac[GSYM clear_nops_function_def] >>
  first_x_assum irule >> simp[]
QED

(* ===================================================================== *)
(* ===== Re-exported proof results ===================================== *)
(* ===================================================================== *)

(* Operand substitution *)
Theorem subst_operand_eval =
  passSharedSubstTheory.subst_operand_eval

Theorem subst_op_map_eval =
  passSharedSubstTheory.subst_op_map_eval

Theorem subst_operand_eval_operands =
  passSharedSubstTheory.subst_operand_eval_operands

Theorem subst_op_map_eval_operands =
  passSharedSubstTheory.subst_op_map_eval_operands

Theorem subst_operands_correct =
  passSharedSubstTheory.subst_operands_correct

(* Supersedes passSharedSubstTheory.subst_operands_map_correct:
   inst_wf handles structural positions (Lit in PARAM/ALLOCA/LOG),
   so per-opcode exclusions unnecessary — only PHI excluded. *)
Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst_wf inst /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  irule passSharedSubstTheory.subst_operands_map_correct_wf >> simp[]
QED

(* State field preservation *)
Theorem step_inst_preserves_all =
  passSharedFieldTheory.step_inst_preserves_all

Theorem step_base_preserves_tracked =
  passSharedFieldTheory.step_base_preserves_tracked

Theorem eligible_no_write_balance_extcode =
  passSharedFieldTheory.eligible_no_write_balance_extcode

(* Transfer/determinism *)
Theorem step_inst_base_ok_transfer =
  passSharedTransferTheory.step_inst_base_ok_transfer

Theorem step_inst_base_output_determined_fields =
  passSharedTransferTheory.step_inst_base_output_determined_fields

(* Variable frame *)
Theorem step_inst_base_var_frame_full =
  passSharedVarFrameTheory.step_inst_base_var_frame_full

Theorem step_inst_var_frame_full =
  passSharedVarFrameTheory.step_inst_var_frame_full

(* Commutativity *)
Theorem effects_independent_commute =
  passSharedFrameTheory.effects_independent_commute
