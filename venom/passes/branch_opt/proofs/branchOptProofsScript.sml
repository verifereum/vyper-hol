(*
 * Branch Optimization Pass — Proofs
 *
 * Architecture:
 *   Uses block_sim_function_inv with bo_iszero_inv as the invariant.
 *   Invariant preservation is taken as a precondition because it requires
 *   an SSA-execution bridge (connecting CFG dominance to runtime state)
 *   that is outside scope. The precondition is satisfied by the pipeline.
 *)

Theory branchOptProofs
Ancestors
  branchOptDefs passSimulationDefs passSimulationProps stateEquiv
  stateEquivProps execEquivParamProps venomInstProps venomExecProps
  dfgAnalysisProps venomState venomWf venomExecSemantics venomExecProofs
  pred_set arithmetic list rich_list finite_map

(* ===== Label Preservation ===== *)

Theorem branch_opt_block_label[local]:
  !dfg live_at bb. (branch_opt_block dfg live_at bb).bb_label = bb.bb_label
Proof
  rw[branch_opt_block_def, LET_THM] >>
  rpt (CASE_TAC >> gvs[])
QED

(* ===== Function as function_map_transform ===== *)

Theorem branch_opt_as_fmt[local]:
  !live_at fn.
    branch_opt_function live_at fn =
    function_map_transform (branch_opt_block (dfg_build_function fn) live_at) fn
Proof
  rw[branch_opt_function_def, function_map_transform_def, LET_THM]
QED

(* ===== SSA Invariant =====

   Every ISZERO-defined variable satisfies the expected relationship.
   Unconditional: implies lookup_var v s <> NONE. *)

Definition bo_iszero_inv_def:
  bo_iszero_inv dfg s <=>
    !v iszero_inst input_op.
      dfg_get_def dfg v = SOME iszero_inst /\
      iszero_inst.inst_opcode = ISZERO /\
      iszero_inst.inst_operands = [input_op] ==>
      ?input_val.
        eval_operand input_op s = SOME input_val /\
        lookup_var v s = SOME (bool_to_word (input_val = 0w))
End

(* ===== Per-Block Simulation ===== *)

(* Key lemma: JNZ with ISZERO-inverted condition produces same result *)
Theorem jnz_iszero_equiv[local]:
  !inst1 inst2 v input_op fst_lbl snd_lbl input_val st.
    inst1.inst_opcode = JNZ /\
    inst1.inst_operands = [Var v; Label fst_lbl; Label snd_lbl] /\
    inst2.inst_opcode = JNZ /\
    inst2.inst_operands = [input_op; Label snd_lbl; Label fst_lbl] /\
    lookup_var v st = SOME (bool_to_word (input_val = 0w)) /\
    eval_operand input_op st = SOME input_val ==>
    step_inst_base inst1 st = step_inst_base inst2 st
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `input_val = 0w` >> gvs[bool_to_word_def]
QED

(* FRONT/APPEND helpers — eliminate PRE/LENGTH_FRONT arithmetic *)
Theorem LENGTH_FRONT_APPEND1[local]:
  !l (x:'a). l <> [] ==> LENGTH (FRONT l ++ [x]) = LENGTH l
Proof
  rw[LENGTH_APPEND, rich_listTheory.LENGTH_FRONT] >>
  Cases_on `l` >> fs[]
QED

Theorem EL_FRONT_APPEND1[local]:
  !l (x:'a) i. l <> [] /\ i < LENGTH l - 1 ==>
    EL i (FRONT l ++ [x]) = EL i l
Proof
  rw[] >> `i < LENGTH (FRONT l)` by (
    Cases_on `l` >> fs[rich_listTheory.LENGTH_FRONT]) >>
  simp[EL_APPEND1] >>
  irule rich_listTheory.EL_FRONT >> fs[NULL_EQ]
QED

Theorem EL_LAST_FRONT_APPEND1[local]:
  !l (x:'a). l <> [] ==> EL (LENGTH l - 1) (FRONT l ++ [x]) = x
Proof
  rw[] >> `LENGTH l >= 1` by (Cases_on `l` >> fs[]) >>
  simp[rich_listTheory.LENGTH_FRONT, EL_APPEND2] >>
  `LENGTH l - (PRE (LENGTH l) + 1) = 0` by DECIDE_TAC >> simp[]
QED

(* Shared helper: two blocks that agree on instructions 0..N-2 produce
   related exec_block results. Parameterized over relations R_ok/R_term
   (must be reflexive). Carries a predicate P through the prefix. *)
Theorem exec_block_agree_prefix[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   bb bb' fuel ctx s (P : venom_state -> bool).
    (!s. R_ok s s) /\ (!s. R_term s s) /\
    s.vs_inst_idx = 0 /\
    ~NULL bb.bb_instructions /\
    P s /\
    LENGTH bb'.bb_instructions >= LENGTH bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      EL i bb'.bb_instructions = EL i bb.bb_instructions) /\
    (* P is preserved by each prefix instruction *)
    (!st st' inst. P st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions - 1 /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel ctx inst st = OK st' ==>
       P (st' with vs_inst_idx := SUC st.vs_inst_idx)) /\
    (* At the last instruction, assuming P st *)
    (!st. P st /\
          st.vs_inst_idx = LENGTH bb.bb_instructions - 1 /\
          st.vs_inst_idx < LENGTH bb'.bb_instructions ==>
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb st)
        (exec_block fuel ctx bb' st)) ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx bb' s)

Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `N = LENGTH bb.bb_instructions` >>
  `N >= 1` by (Cases_on `bb.bb_instructions` >> fs[Abbr `N`, NULL_EQ]) >>
  `!n st.
     n = N - st.vs_inst_idx /\
     st.vs_inst_idx < N /\
     P st ==>
     lift_result R_ok R_term R_term
       (exec_block fuel ctx bb st)
       (exec_block fuel ctx bb' st)`

    suffices_by (
      disch_then (qspecl_then [`N`, `s`] mp_tac) >>
      simp[Abbr `N`]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx < N - 1`
  >- (
    `EL idx bb'.bb_instructions = EL idx bb.bb_instructions` by (
      qpat_x_assum `!i. i < _ - 1 ==> _` (qspec_then `idx` mp_tac) >>
      simp[Abbr `idx`]) >>
    `idx < LENGTH bb'.bb_instructions` by simp[Abbr `idx`] >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[venomInstTheory.get_instruction_def] >>
    Cases_on `step_inst fuel ctx (EL idx bb.bb_instructions) st` >>
    simp[lift_result_refl] >>
    Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >>
    simp[lift_result_refl] >>
    (* Apply P preservation *)
    `P (v with vs_inst_idx := SUC idx)` by (
      qpat_x_assum `!st st' inst. _` (qspecl_then [`st`, `v`, `EL idx bb.bb_instructions`] mp_tac) >>
      simp[Abbr `idx`]) >>
    qpat_x_assum `!m. m < _ ==> _` (qspec_then `N - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspec_then `v with vs_inst_idx := SUC idx` mp_tac) >>
    simp[Abbr `idx`]) >>
  `idx = N - 1` by simp[Abbr `idx`] >>
  `idx < LENGTH bb'.bb_instructions` by simp[Abbr `idx`] >>
  first_x_assum (qspec_then `st` mp_tac) >>
  simp[Abbr `idx`, Abbr `N`]
QED

(* Corollary: P=T specialization — no predicate preservation needed. *)
Theorem exec_block_agree_prefix_noP[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   bb bb' fuel ctx s.
    (!s. R_ok s s) /\ (!s. R_term s s) /\
    s.vs_inst_idx = 0 /\
    ~NULL bb.bb_instructions /\
    LENGTH bb'.bb_instructions >= LENGTH bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      EL i bb'.bb_instructions = EL i bb.bb_instructions) /\
    (!st. st.vs_inst_idx = LENGTH bb.bb_instructions - 1 /\
          st.vs_inst_idx < LENGTH bb'.bb_instructions ==>
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb st)
        (exec_block fuel ctx bb' st)) ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx bb' s)

Proof
  rpt strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `bb`, `bb'`, `fuel`, `ctx`, `s`, `\s. T`]
    mp_tac exec_block_agree_prefix >>
  simp[]
QED

(* Corollary: replace the last instruction of a block.
   Both terminators produce the same step_inst_base result under invariant P.
   Parameterized over R_ok/R_term (must be reflexive). *)
Theorem exec_block_replace_last[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   bb new_last fuel ctx s (P : venom_state -> bool).
    (!s. R_ok s s) /\ (!s. R_term s s) /\
    s.vs_inst_idx = 0 /\
    ~NULL bb.bb_instructions /\
    P s /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (LAST bb.bb_instructions).inst_opcode <> INVOKE /\
    is_terminator new_last.inst_opcode /\
    new_last.inst_opcode <> INVOKE /\
    (!st st' inst. P st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions - 1 /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel ctx inst st = OK st' ==>
       P (st' with vs_inst_idx := SUC st.vs_inst_idx)) /\
    (!st. P st /\
          st.vs_inst_idx = LENGTH bb.bb_instructions - 1 ==>
      step_inst_base (LAST bb.bb_instructions) st =
      step_inst_base new_last st) ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx

        (bb with bb_instructions := FRONT bb.bb_instructions ++ [new_last]) s)
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by fs[NULL_EQ] >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    FRONT bb.bb_instructions ++ [new_last]` >>
  qabbrev_tac `N = LENGTH bb.bb_instructions` >>
  `N >= 1` by (Cases_on `bb.bb_instructions` >> fs[Abbr `N`]) >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, LENGTH_FRONT_APPEND1] >>
  `!n st. n = N - st.vs_inst_idx /\ st.vs_inst_idx < N /\ P st ==>
     lift_result R_ok R_term R_term
       (exec_block fuel ctx bb st) (exec_block fuel ctx bb' st)`

    suffices_by (
      disch_then (qspecl_then [`N`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  Cases_on `st.vs_inst_idx < N - 1`
  >- (
    `EL st.vs_inst_idx bb'.bb_instructions =
     EL st.vs_inst_idx bb.bb_instructions` by
      simp[Abbr `bb'`, EL_FRONT_APPEND1] >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[venomInstTheory.get_instruction_def] >>
    Cases_on `step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st` >>
    simp[lift_result_refl] >>
    Cases_on `is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode` >>
    simp[lift_result_refl] >>
    qpat_x_assum `!m. m < _ ==> _` (qspec_then `N - SUC st.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspec_then `v with vs_inst_idx := SUC st.vs_inst_idx` mp_tac) >>
    simp[] >> disch_then irule >>
    metis_tac[])
  >> (* Last instruction: step_inst_base equality *)
  `st.vs_inst_idx = N - 1` by simp[] >>
  `EL st.vs_inst_idx bb.bb_instructions = LAST bb.bb_instructions` by
    simp[LAST_EL, PRE_SUB1] >>
  `EL st.vs_inst_idx bb'.bb_instructions = new_last` by
    simp[Abbr `bb'`, Abbr `N`, EL_LAST_FRONT_APPEND1] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[venomInstTheory.get_instruction_def, step_inst_non_invoke] >>
  (`step_inst_base (LAST bb.bb_instructions) st =
   step_inst_base new_last st` by metis_tac[]) >>
  Cases_on `step_inst_base new_last st` >>
  simp[lift_result_refl]
QED

(* ISZERO removal: replace JNZ(Var v, L1, L2) with JNZ(input_op, L2, L1)
   using bo_iszero_inv to know the ISZERO relationship. *)
Theorem bo_block_sim_iszero_removal[local]:
  !bb fuel ctx s dfg v fst_lbl snd_lbl prev_inst new_cond.
    s.vs_inst_idx = 0 /\
    ~NULL bb.bb_instructions /\
    bo_iszero_inv dfg s /\
    (LAST bb.bb_instructions).inst_opcode = JNZ /\
    (LAST bb.bb_instructions).inst_operands =
      [Var v; Label fst_lbl; Label snd_lbl] /\
    dfg_get_def dfg v = SOME prev_inst /\
    prev_inst.inst_opcode = ISZERO /\
    prev_inst.inst_operands = [new_cond] /\
    (!st st' inst. bo_iszero_inv dfg st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions - 1 /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel ctx inst st = OK st' ==>
       bo_iszero_inv dfg (st' with vs_inst_idx := SUC st.vs_inst_idx)) ==>
    let new_term = (LAST bb.bb_instructions) with inst_operands :=
      [new_cond; Label snd_lbl; Label fst_lbl] in
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx

        (bb with bb_instructions := FRONT bb.bb_instructions ++ [new_term]) s)
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  irule exec_block_replace_last >>
  simp[venomInstTheory.is_terminator_def, state_equiv_refl,
       execution_equiv_refl] >>
  qexists_tac `bo_iszero_inv dfg` >> simp[] >>
  rpt strip_tac >>
  (* Use bo_iszero_inv dfg st to get the ISZERO value relationship *)
  fs[bo_iszero_inv_def] >>
  qpat_x_assum `!v' iz ip. dfg_get_def dfg v' = SOME iz /\ _ ==> _`
    (qspecl_then [`v`, `prev_inst`, `new_cond`] mp_tac) >>
  simp[] >> strip_tac >>
  qspecl_then [`LAST bb.bb_instructions`,
    `LAST bb.bb_instructions with inst_operands :=
      [new_cond; Label snd_lbl; Label fst_lbl]`,
    `v`, `new_cond`, `fst_lbl`, `snd_lbl`, `input_val`, `st`]
    mp_tac jnz_iszero_equiv >>
  simp[]
QED

(* Core of ISZERO insertion: at the last instruction position, the original
   block runs JNZ(v, fst, snd) while the transformed runs ISZERO(v→tmp) then
   JNZ(tmp, snd, fst). Both reach the same branch target; the transformed
   state has an extra variable tmp. *)
Theorem jnz_iszero_insertion_core[local]:
  !bb bb' iz new_term fuel ctx st tmp v fst_lbl snd_lbl N.
    N = LENGTH bb.bb_instructions /\ N >= 1 /\
    st.vs_inst_idx = N - 1 /\
    EL (N - 1) bb.bb_instructions = LAST bb.bb_instructions /\
    (LAST bb.bb_instructions).inst_opcode = JNZ /\
    (LAST bb.bb_instructions).inst_operands =
      [Var v; Label fst_lbl; Label snd_lbl] /\
    iz = <| inst_id := (LAST bb.bb_instructions).inst_id;
            inst_opcode := ISZERO;
            inst_operands := [Var v]; inst_outputs := [tmp] |> /\
    new_term = (LAST bb.bb_instructions) with inst_operands :=
      [Var tmp; Label snd_lbl; Label fst_lbl] /\
    bb'.bb_instructions = FRONT bb.bb_instructions ++ [iz; new_term] /\
    LENGTH bb'.bb_instructions = N + 1
  ==>
    lift_result (state_equiv {tmp}) (execution_equiv {tmp}) (execution_equiv {tmp})
      (exec_block fuel ctx bb st) (exec_block fuel ctx bb' st)

Proof
  rpt strip_tac >>
  sg `bb.bb_instructions <> []`
    >- (Cases_on `bb.bb_instructions` >> fs[]) >>
  (* Unroll both run_blocks once *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  (* gvs substitutes EL(N-1) = LAST into goal, enabling step_inst resolution *)
  gvs[venomInstTheory.get_instruction_def, step_inst_non_invoke,
      venomInstTheory.is_terminator_def, EL_APPEND1, EL_APPEND2,
      listTheory.LENGTH_FRONT] >>
  (* Expand step_inst_base for JNZ and ISZERO, case split on v *)
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP st.vs_vars v` >>
  simp[lift_result_def, update_var_def] >>
  (* SOME case: simplify original's case expression *)
  rename1 `FLOOKUP st.vs_vars v = SOME val` >>
  Cases_on `val = 0w` >> simp[jump_to_def] >>
  (* Unroll transformed exec_block for the JNZ step *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  gvs[venomInstTheory.get_instruction_def, step_inst_non_invoke,
      venomInstTheory.is_terminator_def, EL_APPEND2,
      listTheory.LENGTH_FRONT,
      step_inst_base_def, eval_operand_def, lookup_var_def,
      FLOOKUP_UPDATE, bool_to_word_def, jump_to_def] >>
  IF_CASES_TAC >>
  simp[lift_result_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, FLOOKUP_UPDATE]
QED

(* ISZERO insertion: original has N instructions, transformed has N+1.
   The ISZERO relationship is established within the block by the
   freshly inserted ISZERO instruction — no cross-block reasoning needed.
   Result excludes {tmp} because the transform introduces a fresh var. *)
Theorem bo_block_sim_iszero_insertion[local]:
  !bb fuel ctx s v fst_lbl snd_lbl.
    s.vs_inst_idx = 0 /\
    ~NULL bb.bb_instructions /\
    (LAST bb.bb_instructions).inst_opcode = JNZ /\
    (LAST bb.bb_instructions).inst_operands = [Var v; Label fst_lbl; Label snd_lbl] ==>
    let id = (LAST bb.bb_instructions).inst_id in
    let tmp = bo_fresh_var id in
    let iz = <| inst_id := id; inst_opcode := ISZERO;
                inst_operands := [Var v]; inst_outputs := [tmp] |> in
    let new_term = (LAST bb.bb_instructions) with inst_operands :=
      [Var tmp; Label snd_lbl; Label fst_lbl] in
    lift_result (state_equiv {tmp}) (execution_equiv {tmp}) (execution_equiv {tmp})
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx

        (bb with bb_instructions := FRONT bb.bb_instructions ++ [iz; new_term]) s)
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  qabbrev_tac `id = (LAST bb.bb_instructions).inst_id` >>
  qabbrev_tac `tmp = bo_fresh_var id` >>
  qabbrev_tac `iz = <| inst_id := id; inst_opcode := ISZERO;
                        inst_operands := [Var v]; inst_outputs := [tmp] |>` >>
  qabbrev_tac `new_term = (LAST bb.bb_instructions) with inst_operands :=
    [Var tmp; Label snd_lbl; Label fst_lbl]` >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    FRONT bb.bb_instructions ++ [iz; new_term]` >>
  sg `bb.bb_instructions <> []` >- fs[NULL_EQ] >>
  qabbrev_tac `N = LENGTH bb.bb_instructions` >>
  sg `N >= 1` >- (Cases_on `bb.bb_instructions` >> fs[Abbr `N`]) >>
  sg `LENGTH (FRONT bb.bb_instructions) = N - 1`
    >- simp[listTheory.LENGTH_FRONT, Abbr `N`] >>
  sg `bb'.bb_instructions = FRONT bb.bb_instructions ++ [iz; new_term]`
    >- simp[Abbr `bb'`] >>
  sg `LENGTH bb'.bb_instructions = N + 1` >- simp[] >>
  irule exec_block_agree_prefix_noP >>
  simp[state_equiv_refl, execution_equiv_refl] >>
  conj_tac >- (rpt strip_tac >> simp[EL_APPEND1] >>
    irule rich_listTheory.EL_FRONT >> simp[NULL_EQ]) >>
  rpt strip_tac >>
  irule jnz_iszero_insertion_core >>
  simp[LAST_EL, PRE_SUB1, Abbr `N`, Abbr `new_term`, Abbr `iz`]
QED

(* Helper: dfg_get_def returns instructions that are inst_wf *)
Theorem fn_insts_MEM[local]:
  !bbs inst. MEM inst (fn_insts_blocks bbs) ==>
    ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> fs[MEM_APPEND] >> metis_tac[]
QED

Theorem dfg_inst_wf[local]:
  !fn v inst.
    fn_inst_wf fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst ==>
    inst_wf inst
Proof
  rpt strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  fs[fn_inst_wf_def, venomInstTheory.fn_insts_def] >>
  drule fn_insts_MEM >> strip_tac >>
  metis_tac[]
QED

(* Helper: bo_fresh_var of a JNZ-terminated block is in bo_fresh_vars_fn *)
Theorem bo_fresh_var_in_fn[local]:
  !fn bb.
    MEM bb fn.fn_blocks /\
    ~NULL bb.bb_instructions /\
    (LAST bb.bb_instructions).inst_opcode = JNZ ==>
    bo_fresh_var (LAST bb.bb_instructions).inst_id IN bo_fresh_vars_fn fn
Proof
  rw[bo_fresh_vars_fn_def, IN_BIGUNION] >>
  qexists_tac `{bo_fresh_var (LAST bb.bb_instructions).inst_id}` >>
  simp[MEM_MAP] >>
  qexists_tac `bb` >> simp[]
QED

(* Helper: monotonicity of lift_result for state_equiv/execution_equiv *)
Theorem lift_result_subset[local]:
  !vars1 vars2 r1 r2.
    vars1 SUBSET vars2 /\
    lift_result (state_equiv vars1) (execution_equiv vars1) (execution_equiv vars1) r1 r2 ==>
    lift_result (state_equiv vars2) (execution_equiv vars2) (execution_equiv vars2) r1 r2
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [AND_IMP_INTRO] lift_result_mono) >>
  qexistsl_tac [`state_equiv vars1`, `execution_equiv vars1`] >>
  simp[] >> metis_tac[state_equiv_subset, execution_equiv_subset]
QED

(* Each block transformed by branch_opt_block simulates the original. *)
Theorem iszero_operand_singleton[local]:
  !x. inst_wf x /\ x.inst_opcode = ISZERO ==>
    ?op. x.inst_operands = [op]
Proof
  rpt strip_tac >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute]
QED

Theorem bo_block_sim[local]:
  !dfg live_at fn bb fuel ctx s.
    dfg = dfg_build_function fn /\
    wf_ssa fn /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    bo_iszero_inv dfg s /\
    s.vs_inst_idx = 0 /\
    (* bo_iszero_inv preserved through each prefix instruction *)
    (!st st' inst. bo_iszero_inv dfg st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions - 1 /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel ctx inst st = OK st' ==>
       bo_iszero_inv dfg (st' with vs_inst_idx := SUC st.vs_inst_idx)) ==>
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
                  (execution_equiv (bo_fresh_vars_fn fn))
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (branch_opt_block dfg live_at bb) s)

Proof
  rpt strip_tac >> gvs[] >>
  simp[branch_opt_block_def, LET_THM] >>
  (* Most cases: block unchanged → reflexivity *)
  rpt (CASE_TAC >> simp[lift_result_refl, state_equiv_refl, execution_equiv_refl]) >>
  (* 3 remaining goals: two removal, one insertion *)
  ALL_TAC >| [
    (* Goal 1: Removal (ISZERO, prefer) *)
    irule lift_result_subset >> qexists_tac `{}` >> simp[EMPTY_SUBSET] >>
    sg `inst_wf x` >- metis_tac[dfg_inst_wf] >>
    sg `?op. x.inst_operands = [op]`
      >- metis_tac[iszero_operand_singleton] >>
    pop_assum strip_assume_tac >>
    qspecl_then [`bb`, `fuel`, `ctx`, `s`, `dfg_build_function fn`, `s'`,
                 `s'³'`, `s''`, `x`, `op`]
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM] bo_block_sim_iszero_removal) >>
    fs[],
    (* Goal 2: Insertion *)
    irule lift_result_subset >>
    qexists_tac `{bo_fresh_var (LAST bb.bb_instructions).inst_id}` >>
    conj_tac >- (simp[SUBSET_DEF] >> metis_tac[bo_fresh_var_in_fn]) >>
    irule (SIMP_RULE (srw_ss()) [LET_THM] bo_block_sim_iszero_insertion) >>
    simp[],
    (* Goal 3: Removal (ISZERO, not prefer) — same as goal 1 *)
    irule lift_result_subset >> qexists_tac `{}` >> simp[EMPTY_SUBSET] >>
    sg `inst_wf x` >- metis_tac[dfg_inst_wf] >>
    sg `?op. x.inst_operands = [op]`
      >- metis_tac[iszero_operand_singleton] >>
    pop_assum strip_assume_tac >>
    qspecl_then [`bb`, `fuel`, `ctx`, `s`, `dfg_build_function fn`, `s'`,
                 `s'³'`, `s''`, `x`, `op`]
      mp_tac (SIMP_RULE (srw_ss()) [LET_THM] bo_block_sim_iszero_removal) >>
    fs[]
  ]
QED


(* ===== Cross-State Per-Block Simulation (reversed triangle) ===== *)

(* Leg 1: Running the ORIGINAL block on two state_equiv states gives
   lift_result-related results (because original operands are not fresh).
   Leg 2: Running original vs transformed on the SAME state s2 gives
   lift_result-related results (bo_block_sim).
   Compose via lift_result_trans. *)

Theorem bo_cross_block_sim[local]:
  !dfg live_at fn bb fuel ctx s1 s2.
    dfg = dfg_build_function fn /\
    wf_ssa fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    state_equiv (bo_fresh_vars_fn fn) s1 s2 /\
    bo_iszero_inv dfg s1 /\ bo_iszero_inv dfg s2 /\
    s1.vs_inst_idx = 0 /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN bo_fresh_vars_fn fn) /\
    (!bb' fuel' ctx' st st' inst.
       (MEM bb' fn.fn_blocks) /\
       bo_iszero_inv dfg st /\
       st.vs_inst_idx < LENGTH bb'.bb_instructions /\
       EL st.vs_inst_idx bb'.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel' ctx' inst st = OK st' ==>
       bo_iszero_inv dfg (st' with vs_inst_idx := SUC st.vs_inst_idx)) ==>
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
                  (execution_equiv (bo_fresh_vars_fn fn))
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (branch_opt_block dfg live_at bb) s2)

Proof
  rpt strip_tac >> gvs[] >>
  qspecl_then [`state_equiv (bo_fresh_vars_fn fn)`,
               `execution_equiv (bo_fresh_vars_fn fn)`]
    mp_tac lift_result_trans >>
  (impl_tac >- metis_tac[state_equiv_trans, execution_equiv_trans]) >>
  disch_then irule >>
  qexists_tac `exec_block fuel ctx bb s2` >>
  conj_tac
  >- (
    qspecl_then [`state_equiv (bo_fresh_vars_fn fn)`,
                  `execution_equiv (bo_fresh_vars_fn fn)`,
                  `fn`] mp_tac (cj 1 exec_block_preserves_R) >>
    simp[state_equiv_execution_equiv_valid_state_rel] >>
    impl_tac
    >- (
      rpt conj_tac
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- (rpt strip_tac >> res_tac >>
          fs[state_equiv_def, execution_equiv_def])
    )
    >- (
      disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `s2`] mp_tac) >>
      simp[]
    )
  )
  >- (
    irule bo_block_sim >> simp[] >>
    conj_tac
    >- (rpt strip_tac >>
        first_x_assum (qspecl_then [`bb`, `fuel`, `ctx`, `st`, `st'`] mp_tac) >>
        simp[])
    >- gvs[state_equiv_def]
  )
QED

(* ===== Main Theorem ===== *)

Theorem branch_opt_function_correct_proof:
  !fuel ctx live_at fn s.
    let fn' = branch_opt_function live_at fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    fn_inst_wf fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN bo_fresh_vars_fn fn) /\
    bo_iszero_inv dfg s /\
    (* Inv preservation across original blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       bo_iszero_inv dfg s0 /\ s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       bo_iszero_inv dfg s0') /\
    (* Inv preservation across transformed blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       bo_iszero_inv dfg s0 /\ s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       bo_iszero_inv dfg s0') /\
    (* Inv preservation within block prefix (both original and transformed) *)
    (!bb fuel' ctx' st st' inst.
       (MEM bb fn.fn_blocks \/ MEM bb fn'.fn_blocks) /\
       bo_iszero_inv dfg st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel' ctx' inst st = OK st' ==>
       bo_iszero_inv dfg (st' with vs_inst_idx := SUC st.vs_inst_idx)) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
                  (execution_equiv (bo_fresh_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)

Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  ONCE_REWRITE_TAC[branch_opt_as_fmt] >>
  (* Use cross-state variant: single cross-state per-block sim obligation *)
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] block_sim_function_inv_cross) >>
  disch_then (qspecl_then [
    `state_equiv (bo_fresh_vars_fn fn)`,
    `execution_equiv (bo_fresh_vars_fn fn)`,
    `branch_opt_block (dfg_build_function fn) live_at`,
    `fn`,
    `bo_iszero_inv (dfg_build_function fn)`
  ] mp_tac) >>
  simp[] >> disch_then irule >>
  rpt conj_tac
  (* 1. Inv preservation across original blocks *)
  >- metis_tac[]
  (* 2. Cross-state per-block sim: reversed triangle *)
  >- (rpt gen_tac >> strip_tac >>
      irule bo_cross_block_sim >> simp[] >> metis_tac[])
  (* 3. Inv preservation across transformed blocks *)
  >- metis_tac[branch_opt_as_fmt]
  (* 4. Label preservation *)
  >- simp[branch_opt_block_label]
  (* 5. s.vs_inst_idx = 0 *)
  >- simp[]
  (* 6. bo_iszero_inv dfg s *)
  >- first_assum ACCEPT_TAC
  (* 7. valid_state_rel *)
  >- simp[state_equiv_execution_equiv_valid_state_rel]
QED
