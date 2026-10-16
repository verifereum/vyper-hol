(* Block-level invariant obligations for algebraic optimization.
 *
 * TOP-LEVEL (helpers for ao_phase3_correct):
 *   chain_var_is_iszero_output       — chain structure lemma
 *   ao_chain_defined_prefix_initial  — chain-definedness at function entry
 *   ao_cfg_initial                   — entry block is in the DFS order
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

(* ===== Successor CFG ===== *)

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

Triviality chain_el_is_output[local]:
  !fn fn0 targets v chain k.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ALOOKUP targets v = SOME chain /\
    0 < k /\ k < LENGTH chain ==>
    ?x inst. EL k chain = Var x /\
             MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `ALOOKUP _ _ = SOME _` mp_tac >>
  simp[ao_compute_fn_iszero_targets_def,
       ao_compute_iszero_targets_def, fn_insts_def] >>
  strip_tac >>
  drule_all chain_el_foldl_output >> strip_tac >> gvs[] >>
  drule fn0_output_is_fn_output_helper >>
  disch_then drule >> strip_tac >>
  metis_tac[]
QED

Theorem ao_chain_defined_prefix_initial:
  !fn fn0 targets s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    targets = ao_compute_fn_iszero_targets fn0 /\
    ssa_form fn /\ wf_function fn /\
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x s = NONE) ==>
    ao_chain_defined_prefix targets s
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [ao_chain_defined_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `j2 = 0`
  >- (`j1 = 0` by DECIDE_TAC >> fs[])
  >- (`0 < j2` by DECIDE_TAC >>
      qspecl_then [`fn`, `fn0`, `targets`, `v`, `chain`, `j2`]
        mp_tac chain_el_is_output >>
      impl_tac >- simp[] >>
      strip_tac >>
      `lookup_var x s = NONE` by (first_x_assum irule >> metis_tac[]) >>
      fs[eval_operand_def])
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

