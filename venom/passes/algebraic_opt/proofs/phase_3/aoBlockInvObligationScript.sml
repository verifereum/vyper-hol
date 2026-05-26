(* Block-level invariant obligations for algebraic optimization.
 *
 * Obligations for block_sim_function_error_bb in
 * ao_phases123_run_blocks_sim_inv (algebraicOptProofsScript.sml):
 *
 *   1-4. block_inv preserved through exec_block
 *   5-6. Initial state establishment
 *
 * block_inv s = ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
 *               ao_iszero_chain_inv targets s /\
 *               ao_chains_defined targets s /\
 *               range_sound (df_widen_at NONE ra s.vs_current_bb 0) s /\
 *               MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
 *
 * The ao_dfg_inv preservation is already proved inline via
 * ao_dfg_inv_exec_block_preserved. These obligations handle the
 * remaining components.
 *)

Theory aoBlockInvObligation
Ancestors
  algebraicOptDefs aoResolveObligation aoRangeObligation
  stateEquiv venomWf venomExecSemantics venomExecProofs
  analysisSimDefs rangeAnalysisProofs
  passSharedDefs cfgDefs cfgHelpers cfgAnalysisProps
  venomInst venomInstProps venomState
Libs
  pairLib BasicProvers

(* ===== Block-level preservation helpers ===== *)

Triviality mem_bb_mem_fn_insts[local]:
  !inst bb fn0.
    MEM inst bb.bb_instructions /\ MEM bb fn0.fn_blocks ==>
    MEM inst (fn_insts fn0)
Proof
  rpt strip_tac >> simp[fn_insts_def] >>
  Induct_on `fn0.fn_blocks` >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >>
  qpat_x_assum `_ = fn0.fn_blocks` (SUBST_ALL_TAC o SYM) >>
  gvs[fn_insts_blocks_def, listTheory.MEM_APPEND] >>
  first_x_assum (qspec_then `fn0 with fn_blocks := v` mp_tac) >>
  simp[]
QED

Triviality all_distinct_flat_mem[local]:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

Triviality all_distinct_flat_disjoint[local]:
  !ls l1 l2.
    ALL_DISTINCT (FLAT ls) /\ MEM l1 ls /\ MEM l2 ls /\ l1 <> l2 ==>
    !x. MEM x l1 ==> ~MEM x l2
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[listTheory.ALL_DISTINCT_APPEND]
  >- (fs[listTheory.MEM_FLAT] >> metis_tac[])
  >- (fs[listTheory.MEM_FLAT] >> metis_tac[])
  >- metis_tac[]
QED

Triviality ssa_outputs_unique[local]:
  !ls a b x.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) ls)) /\
    MEM a ls /\ MEM b ls /\
    MEM x a.inst_outputs /\ MEM x b.inst_outputs ==>
    a = b
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND]
  >- (fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
  >- (fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
  >- metis_tac[]
QED

Triviality ssa_same_output_same_inst[local]:
  !fn0 bb i j x.
    ssa_form fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    j < LENGTH bb.bb_instructions /\
    MEM x (EL i bb.bb_instructions).inst_outputs /\
    MEM x (EL j bb.bb_instructions).inst_outputs ==>
    i = j
Proof
  rpt strip_tac >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn0)` by
    (irule mem_bb_mem_fn_insts >> qexists_tac `bb` >> simp[] >>
     irule listTheory.EL_MEM >> simp[]) >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn0)` by
    (irule mem_bb_mem_fn_insts >> qexists_tac `bb` >> simp[] >>
     irule listTheory.EL_MEM >> simp[]) >>
  `EL i bb.bb_instructions = EL j bb.bb_instructions` by
    (fs[ssa_form_def] >> metis_tac[ssa_outputs_unique]) >>
  irule inst_ids_el_eq >> fs[wf_function_def] >>
  metis_tac[]
QED

(* ===== Chain structure helpers ===== *)

Triviality chain_last_step[local]:
  !acc inst v ch.
    (!v' ch'. ALOOKUP acc v' = SOME ch' ==>
       0 < LENGTH ch' /\ EL (LENGTH ch' - 1) ch' = Var v') ==>
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME ch ==>
    0 < LENGTH ch /\ EL (LENGTH ch - 1) ch = Var v
Proof
  rpt strip_tac >>
  qpat_x_assum `ALOOKUP _ _ = SOME _` mp_tac >>
  simp[ao_compute_iszero_step_def, LET_THM] >>
  every_case_tac >> simp[] >> every_case_tac >> simp[] >>
  strip_tac >> gvs[listTheory.LENGTH_SNOC, listTheory.EL_LENGTH_SNOC] >>
  metis_tac[]
QED

Triviality chain_var_is_iszero_output_foldl[local]:
  !insts acc v chain k x.
    (!v' ch. ALOOKUP acc v' = SOME ch ==>
       0 < LENGTH ch /\ EL (LENGTH ch - 1) ch = Var v') /\
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    0 < k /\ k < LENGTH chain /\
    EL k chain = Var x ==>
    (?inst'. MEM inst' insts /\
             inst'.inst_opcode = ISZERO /\
             inst'.inst_operands = [EL (k - 1) chain] /\
             inst'.inst_outputs = [x]) \/
    (?v' chain'. ALOOKUP acc v' = SOME chain' /\
                 0 < k /\ k < LENGTH chain' /\
                 EL k chain' = Var x /\
                 EL (k - 1) chain' = EL (k - 1) chain)
Proof
  Induct_on `insts` >> rpt strip_tac
  >- (DISJ2_TAC >> qexistsl_tac [`v`, `chain`] >> gvs[])
  >- (first_x_assum
        (qspecl_then [`ao_compute_iszero_step acc h`, `v`,
                      `chain`, `k`, `x`] mp_tac) >>
      impl_tac
      >- (gvs[Once listTheory.FOLDL] >>
          rpt gen_tac >> strip_tac >>
          metis_tac[chain_last_step]) >>
      strip_tac
      >- (DISJ1_TAC >> qexists_tac `inst'` >>
          simp[listTheory.MEM])
      >- (qpat_x_assum `ALOOKUP _ v' = SOME _` mp_tac >>
          simp[ao_compute_iszero_step_def, LET_THM] >>
          every_case_tac >> simp[] >> every_case_tac >>
          simp[] >> strip_tac >> fs[] >>
          TRY (DISJ2_TAC >> qexistsl_tac [`v'`, `chain'`] >>
               simp[] >> NO_TAC) >>
          gvs[listTheory.LENGTH_SNOC] >>
          TRY (`k = 1` by DECIDE_TAC >> gvs[] >>
               DISJ1_TAC >> qexists_tac `h` >>
               simp[] >> NO_TAC) >>
          qmatch_asmsub_rename_tac
            `ALOOKUP acc acc_var = SOME acc_chain` >>
          Cases_on `k = LENGTH acc_chain`
          >- (DISJ1_TAC >> qexists_tac `h` >>
              gvs[listTheory.MEM, listTheory.EL_SNOC,
                  listTheory.EL_LENGTH_SNOC] >>
              res_tac >> gvs[])
          >- (DISJ2_TAC >> qexistsl_tac [`acc_var`, `acc_chain`] >>
              `k < LENGTH acc_chain` by DECIDE_TAC >>
              gvs[listTheory.EL_SNOC])))
QED

Theorem chain_var_is_iszero_output:
  !fn0 targets v chain k x.
    targets = ao_compute_fn_iszero_targets fn0 /\
    ALOOKUP targets v = SOME chain /\
    0 < k /\ k < LENGTH chain /\
    EL k chain = Var x ==>
    ?inst'. MEM inst' (fn_insts fn0) /\
            inst'.inst_opcode = ISZERO /\
            inst'.inst_operands = [EL (k - 1) chain] /\
            inst'.inst_outputs = [x]
Proof
  rpt strip_tac >>
  gvs[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  `!v' ch. ALOOKUP ([]:(string # operand list) list) v' = SOME ch ==>
     0 < LENGTH ch /\ EL (LENGTH ch - 1) ch = Var v'` by simp[] >>
  drule_all chain_var_is_iszero_output_foldl >> simp[]
QED

(* ===== Step preservation ===== *)

Triviality eval_operand_vars_labels[local]:
  !op s s'.
    (!x. lookup_var x s' = lookup_var x s) /\
    s'.vs_labels = s.vs_labels ==>
    eval_operand op s' = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Triviality chain_evals_preserved_by_step[local]:
  !fn0 targets inst fuel ctx s s'.
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    MEM inst (fn_insts fn0) /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    ao_chains_defined targets s /\
    step_inst fuel ctx inst s = OK s' /\
    (!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE) ==>
    !v chain k. ALOOKUP targets v = SOME chain /\ k < LENGTH chain ==>
      eval_operand (EL k chain) s' = eval_operand (EL k chain) s
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `EL k chain`
  >- simp[eval_operand_def]
  >- (rename1 `EL k chain = Var x` >>
      `lookup_var x s' = lookup_var x s` suffices_by
        simp[eval_operand_def] >>
      irule step_preserves_non_output_vars >> simp[] >>
      qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
      strip_tac >>
      `?w. eval_operand (Var x) s = SOME w` by
        (fs[ao_chains_defined_def] >> metis_tac[]) >>
      fs[eval_operand_def] >>
      `lookup_var x s = NONE` by (first_x_assum irule >> simp[]) >>
      gvs[])
  >- (simp[eval_operand_def] >>
      drule step_inst_preserves_labels_always >> simp[])
QED

Triviality chain_inv_step_any[local]:
  !fn0 targets inst fuel ctx s s'.
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    MEM inst (fn_insts fn0) /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined targets s /\
    step_inst fuel ctx inst s = OK s' /\
    (!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE) ==>
    ao_iszero_chain_inv targets s'
Proof
  rpt strip_tac >>
  irule ao_iszero_chain_inv_step_preserved >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >>
  simp[] >> metis_tac[chain_evals_preserved_by_step]
QED

Triviality chains_defined_step_any[local]:
  !fn0 targets inst fuel ctx s s'.
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    MEM inst (fn_insts fn0) /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    ao_chains_defined targets s /\
    step_inst fuel ctx inst s = OK s' /\
    (!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE) ==>
    ao_chains_defined targets s'
Proof
  rpt strip_tac >>
  irule ao_chains_defined_step_preserved >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >>
  simp[] >> metis_tac[chain_evals_preserved_by_step]
QED

Triviality eval_operand_inst_idx[local]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Triviality ao_iszero_chain_inv_inst_idx[local]:
  !targets s n.
    ao_iszero_chain_inv targets s ==>
    ao_iszero_chain_inv targets (s with vs_inst_idx := n)
Proof
  simp[ao_iszero_chain_inv_def, eval_operand_inst_idx]
QED

Triviality ao_chains_defined_inst_idx[local]:
  !targets s n.
    ao_chains_defined targets s ==>
    ao_chains_defined targets (s with vs_inst_idx := n)
Proof
  simp[ao_chains_defined_def, eval_operand_inst_idx]
QED

Triviality chain_evals_preserved_by_terminator[local]:
  !targets inst fuel ctx s s'.
    is_terminator inst.inst_opcode /\
    inst_wf inst /\
    step_inst fuel ctx inst s = OK s' ==>
    !v chain k. ALOOKUP targets v = SOME chain /\ k < LENGTH chain ==>
      eval_operand (EL k chain) s' = eval_operand (EL k chain) s
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `EL k chain`
  >- simp[eval_operand_def]
  >- (rename1 `Var x` >>
      `lookup_var x s' = lookup_var x s` suffices_by
        simp[eval_operand_def] >>
      irule step_terminator_preserves_vars >> metis_tac[])
  >- (simp[eval_operand_def] >>
      drule step_inst_preserves_labels_always >> simp[])
QED

Triviality chain_inv_terminator[local]:
  !targets inst fuel ctx s s'.
    ao_iszero_chain_inv targets s /\
    is_terminator inst.inst_opcode /\
    inst_wf inst /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_iszero_chain_inv targets s'
Proof
  rpt strip_tac >>
  irule ao_iszero_chain_inv_step_preserved >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >>
  simp[] >> metis_tac[chain_evals_preserved_by_terminator]
QED

Triviality chains_defined_terminator[local]:
  !targets inst fuel ctx s s'.
    ao_chains_defined targets s /\
    is_terminator inst.inst_opcode /\
    inst_wf inst /\
    step_inst fuel ctx inst s = OK s' ==>
    ao_chains_defined targets s'
Proof
  rpt strip_tac >>
  irule ao_chains_defined_step_preserved >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s`] >>
  simp[] >> metis_tac[chain_evals_preserved_by_terminator]
QED

(* ===== Main exec_block preservation ===== *)

Triviality output_none_preserved_step[local]:
  !fn0 bb fuel ctx s s_mid x i.
    ssa_form fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s = OK s_mid /\
    (!x i. s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
           MEM x (EL i bb.bb_instructions).inst_outputs ==>
           lookup_var x s = NONE) /\
    SUC s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
    MEM x (EL i bb.bb_instructions).inst_outputs ==>
    lookup_var x (s_mid with vs_inst_idx := SUC s.vs_inst_idx) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `i <> s.vs_inst_idx` by DECIDE_TAC >>
  qspecl_then [`fn0`, `bb`, `i`, `s.vs_inst_idx`, `x`]
    assume_tac ssa_same_output_same_inst >>
  `~MEM x (EL s.vs_inst_idx bb.bb_instructions).inst_outputs` by
    (strip_tac >> gvs[]) >>
  `lookup_var x s = NONE` by
    (first_x_assum (qspecl_then [`x`, `i`] mp_tac) >> simp[]) >>
  qspecl_then [`fuel`, `ctx`, `EL s.vs_inst_idx bb.bb_instructions`,
               `s`, `s_mid`]
    mp_tac step_preserves_non_output_vars >> simp[] >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >>
  strip_tac >> gvs[lookup_var_def]
QED

Theorem ao_chain_inv_exec_block_preserved:
  !fn0 dfg targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    wf_function fn0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb fn0.fn_blocks /\
    ao_iszero_chain_inv targets s /\
    ao_chains_defined targets s /\
    (!x i. s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
           MEM x (EL i bb.bb_instructions).inst_outputs ==>
           lookup_var x s = NONE) /\
    exec_block fuel ctx bb s = OK v ==>
    ao_iszero_chain_inv targets v
Proof
  rpt gen_tac >> strip_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`] >> irule listTheory.EL_MEM >> simp[]) >>
  `inst_wf inst` by
    (fs[listTheory.EVERY_MEM] >> res_tac) >>
  `MEM inst (fn_insts fn0)` by
    metis_tac[mem_bb_mem_fn_insts] >>
  `!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`x`, `s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `inst`]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_mid` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (`ao_iszero_chain_inv targets s_mid` by
        metis_tac[chain_inv_terminator] >>
      Cases_on `s_mid.vs_halted` >> simp[] >>
      strip_tac >> gvs[])
  >- (`ao_iszero_chain_inv targets s_mid` by
        metis_tac[chain_inv_step_any] >>
      `ao_chains_defined targets s_mid` by
        metis_tac[chains_defined_step_any] >>
      strip_tac >>
      `s_mid.vs_inst_idx = s.vs_inst_idx` by
        metis_tac[step_inst_preserves_inst_idx] >>
      `ao_iszero_chain_inv targets
        (s_mid with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[ao_iszero_chain_inv_inst_idx] >>
      `ao_chains_defined targets
        (s_mid with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[ao_chains_defined_inst_idx] >>
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`bb`,
        `s_mid with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      gvs[Abbr `inst`] >>
      disch_then irule >>
      metis_tac[output_none_preserved_step])
QED

Theorem ao_chains_defined_exec_block_preserved:
  !fn0 dfg targets bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn0 /\
    wf_function fn0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb fn0.fn_blocks /\
    ao_chains_defined targets s /\
    (!x i. s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\
           MEM x (EL i bb.bb_instructions).inst_outputs ==>
           lookup_var x s = NONE) /\
    exec_block fuel ctx bb s = OK v ==>
    ao_chains_defined targets v
Proof
  rpt gen_tac >> strip_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`] >> irule listTheory.EL_MEM >> simp[]) >>
  `inst_wf inst` by
    (fs[listTheory.EVERY_MEM] >> res_tac) >>
  `MEM inst (fn_insts fn0)` by
    metis_tac[mem_bb_mem_fn_insts] >>
  `!x. MEM x inst.inst_outputs ==> lookup_var x s = NONE` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`x`, `s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `inst`]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_mid` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (`ao_chains_defined targets s_mid` by
        metis_tac[chains_defined_terminator] >>
      Cases_on `s_mid.vs_halted` >> simp[] >>
      strip_tac >> gvs[])
  >- (`ao_chains_defined targets s_mid` by
        metis_tac[chains_defined_step_any] >>
      strip_tac >>
      `s_mid.vs_inst_idx = s.vs_inst_idx` by
        metis_tac[step_inst_preserves_inst_idx] >>
      `ao_chains_defined targets
        (s_mid with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[ao_chains_defined_inst_idx] >>
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`bb`,
        `s_mid with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      gvs[Abbr `inst`] >>
      disch_then irule >>
      metis_tac[output_none_preserved_step])
QED

(* ===== Successor CFG ===== *)

Triviality cfg_successor_in_dfs_pre[local]:
  !fn0 bb fuel ctx s v.
    wf_function fn0 /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    exec_block fuel ctx bb s = OK v ==>
    MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `v`]
       mp_tac exec_block_current_bb_in_succs >>
     disch_then match_mp_tac >>
     simp[] >>
     fs[bb_well_formed_def] >> rpt strip_tac >>
     CCONTR_TAC >>
     `i < LENGTH bb.bb_instructions` by DECIDE_TAC >>
     res_tac >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn0)` by fs[wf_function_def] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn0) bb.bb_label)` by
    (irule bb_succs_in_cfg_succs >> simp[]) >>
  `set (cfg_analyze fn0).cfg_dfs_pre =
   {lbl | cfg_reachable_of (cfg_analyze fn0) lbl}` by
    metis_tac[cfg_analyze_reachable_sets] >>
  `cfg_reachable_of (cfg_analyze fn0) bb.bb_label` by
    (fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?entry_bb. entry_block fn0 = SOME entry_bb` by
    (Cases_on `fn0.fn_blocks` >>
     gvs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  `cfg_path (cfg_analyze fn0) entry_bb.bb_label bb.bb_label` by
    metis_tac[cfg_analyze_semantic_reachability] >>
  `cfg_path (cfg_analyze fn0) entry_bb.bb_label v.vs_current_bb` by
    (simp[cfg_path_def] >>
     match_mp_tac (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES_RIGHT1)) >>
     qexists_tac `bb.bb_label` >>
     fs[cfg_path_def]) >>
  `cfg_reachable_of (cfg_analyze fn0) v.vs_current_bb` by
    metis_tac[cfg_analyze_semantic_reachability] >>
  fs[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem ao_block_inv_successor:
  !fn0 dfg ra bb fuel ctx s v.
    dfg = dfg_build_function fn0 /\
    ra = range_analyze fn0 /\
    wf_function fn0 /\
    ssa_form fn0 /\
    EVERY inst_wf (fn_insts fn0) /\
    MEM bb fn0.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn0).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
    range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
    ao_dfg_inv dfg (s with vs_inst_idx := 0) /\
    exec_block fuel ctx bb s = OK v /\
    range_sound (df_widen_at NONE ra v.vs_current_bb 0) v ==>
    range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
    MEM v.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  rpt strip_tac
  >- simp[]
  >- (`EVERY inst_wf bb.bb_instructions` by
        metis_tac[mem_bb_mem_fn_insts, listTheory.EVERY_MEM] >>
      metis_tac[cfg_successor_in_dfs_pre])
QED

(* ===== Initial state ===== *)

Triviality chain_el_step_output[local]:
  !acc inst v chain k.
    ALOOKUP (ao_compute_iszero_step acc inst) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    (?x. EL k chain = Var x /\ MEM x inst.inst_outputs) \/
    (?v' chain' k'. ALOOKUP acc v' = SOME chain' /\
       0 < k' /\ k' < LENGTH chain' /\ EL k' chain' = EL k chain)
Proof
  rpt gen_tac >>
  simp[ao_compute_iszero_step_def, LET_THM] >>
  every_case_tac >> simp[] >>
  strip_tac >> gvs[listTheory.LENGTH_SNOC] >>
  TRY (DISJ2_TAC >> qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  TRY (qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  Cases_on `h = v` >> gvs[] >>
  TRY (DISJ2_TAC >> qexistsl_tac [`v`, `chain`, `k`] >> simp[] >> NO_TAC) >>
  Cases_on `k` >>
  gvs[listTheory.EL_restricted, listTheory.HD,
      listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  TRY (Cases_on `n` >>
       gvs[listTheory.HD, listTheory.EL_restricted] >> NO_TAC) >>
  rename1 `SUC m` >>
  Cases_on `SUC m = LENGTH x` >>
  gvs[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
  DISJ2_TAC >>
  qexistsl_tac [`s`, `x`, `SUC m`] >> gvs[]
QED

Triviality chain_el_foldl_output[local]:
  !insts acc v chain k.
    ALOOKUP (FOLDL ao_compute_iszero_step acc insts) v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    (?x inst. EL k chain = Var x /\ MEM inst insts /\
              MEM x inst.inst_outputs) \/
    (?v' ch' k'. ALOOKUP acc v' = SOME ch' /\
       0 < k' /\ k' < LENGTH ch' /\ EL k' ch' = EL k chain)
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> qexistsl_tac [`v`, `chain`, `k`] >> simp[])
  >- (first_x_assum
        (qspecl_then [`ao_compute_iszero_step acc h`,
                      `v`, `chain`, `k`] mp_tac) >>
      impl_tac >- gvs[Once listTheory.FOLDL] >>
      strip_tac
      >- (DISJ1_TAC >> metis_tac[listTheory.MEM])
      >- (metis_tac[chain_el_step_output, listTheory.MEM]))
QED

Triviality ao_handle_offset_inst_outputs[local]:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  rpt strip_tac >> simp[ao_handle_offset_inst_def] >>
  every_case_tac >> simp[]
QED

Triviality fn0_output_is_fn_output_helper[local]:
  !blocks inst x.
    MEM inst (fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) blocks)) /\
    MEM x inst.inst_outputs ==>
    ?inst'. MEM inst' (fn_insts_blocks blocks) /\ MEM x inst'.inst_outputs
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >>
  gvs[fn_insts_blocks_def, listTheory.MEM_APPEND, listTheory.MEM_MAP]
  >- (qexists_tac `y` >>
      gvs[ao_handle_offset_inst_outputs, listTheory.MEM_APPEND])
  >- (first_x_assum drule_all >> strip_tac >>
      qexists_tac `inst'` >> simp[listTheory.MEM_APPEND])
QED

Triviality fn0_output_is_fn_output[local]:
  !fn fn0 inst x.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    MEM inst (fn_insts fn0) /\ MEM x inst.inst_outputs ==>
    ?inst'. MEM inst' (fn_insts fn) /\ MEM x inst'.inst_outputs
Proof
  rpt strip_tac >> gvs[fn_insts_def] >>
  irule fn0_output_is_fn_output_helper >> metis_tac[]
QED

Theorem ao_chain_inv_initial:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn /\ wf_function fn /\
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x s = NONE) ==>
    ao_iszero_chain_inv targets s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ao_iszero_chain_inv_def] >> rpt strip_tac >>
  `0 < k + 1 /\ k + 1 < LENGTH chain` by simp[] >>
  qpat_x_assum `ALOOKUP _ v = SOME chain` mp_tac >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  strip_tac >>
  drule_all chain_el_foldl_output >> strip_tac
  >> fs[fn_insts_def] >>
  drule fn0_output_is_fn_output_helper >>
  disch_then drule >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `eval_operand (Var _) _ = _` mp_tac >>
  REWRITE_TAC[eval_operand_def] >> gvs[]
QED

Theorem ao_chains_defined_initial:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    (!v chain k. ALOOKUP targets v = SOME chain /\ k < LENGTH chain ==>
      ?w. eval_operand (EL k chain) s = SOME w) ==>
    ao_chains_defined targets s
Proof
  rpt strip_tac >> gvs[ao_chains_defined_def] >>
  rpt strip_tac >> res_tac >> metis_tac[]
QED

Theorem ao_cfg_initial:
  !fn0 s.
    wf_function fn0 /\
    fn_entry_label fn0 = SOME s.vs_current_bb ==>
    MEM s.vs_current_bb (cfg_analyze fn0).cfg_dfs_pre
Proof
  rpt strip_tac >>
  fs[fn_entry_label_def, entry_block_def, cfg_analyze_def] >>
  gvs[wf_function_def, fn_has_entry_def] >>
  Cases_on `fn0.fn_blocks` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label) <> [] /\
   HD (SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label)) = h.bb_label` by
    (irule dfs_pre_walk_entry_hd >> simp[]) >>
  Cases_on `SND (dfs_pre_walk (build_succs (h::t)) [] h.bb_label)` >> gvs[]
QED

Theorem ao_range_sound_initial:
  !fn0 ra s.
    ra = range_analyze fn0 /\
    wf_function fn0 /\
    fn_entry_label fn0 = SOME s.vs_current_bb /\
    (df_widen_at NONE ra s.vs_current_bb 0 = NONE \/
     df_widen_at NONE ra s.vs_current_bb 0 = SOME FEMPTY) ==>
    range_sound (df_widen_at NONE ra s.vs_current_bb 0) s
Proof
  rpt strip_tac >> gvs[range_sound_fempty, range_sound_bottom]
QED
