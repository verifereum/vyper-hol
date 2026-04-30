(* dftCorrectnessFinalScript.sml
   Final proofs for DFT pass correctness.
   Depends on dftCorrectnessTheory (truncated to proven theorems).
*)

Theory dftCorrectnessFinal
Ancestors
  dftCorrectness dftCanonicalDep dftPermSim dftPipelineInvar
  dftTopoSort dftStructural dftFrontEquiv dftBlockSim
  dftWf venomWf venomState venomInst venomEffects
  venomExecSemantics venomExecProps venomInstProps
  stateEquiv stateEquivProps passSimulationDefs passSimulationProofs
  crossBlockSimProps passSharedProps passSharedDefs passSharedFrame
  analysisSimDefs analysisSimProofsBase dftDefs dftHelpers
  dftCompleteness dftIdempotent dftContraHelpers dftScheduleFixed
  sorting list rich_list combin arithmetic finite_map relation
Libs
  pairLib

(* ===== Small helpers ===== *)

Theorem EVERY_MEM_imp:
  !P l x. EVERY P l /\ MEM x l ==> P x
Proof
  Induct_on `l` >> simp[] >> metis_tac[]
QED

Theorem from_block_MEM_body_filter:
  !bi x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) ==>
         from_block bi x
Proof
  rpt strip_tac >>
  fs[MEM_FILTER] >>
  simp[from_block_def] >>
  qexists_tac `x` >> simp[]
QED

Theorem MEM_body_filter_imp_pseudo_filter:
  !l x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) l) ==>
         MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) l)
Proof
  rpt strip_tac >> fs[MEM_FILTER]
QED

Theorem from_block_MEM_filter:
  !bi. EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)
Proof
  rpt gen_tac >> simp[EVERY_MEM, MEM_FILTER, from_block_def] >>
  rpt strip_tac >>
  qexists_tac `i` >> simp[]
QED

Theorem from_block_every_cross_bi:
  !bi bi' x.
    EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi') /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi') ==>
    from_block bi x
Proof
  rpt strip_tac >>
  `MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi')`
    by metis_tac[MEM_body_filter_imp_pseudo_filter] >>
  metis_tac[EVERY_MEM_imp]
QED

Theorem from_block_every_body_bi:
  !bi x.
    EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) ==>
    from_block bi x
Proof
  rpt strip_tac >>
  `MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi)`
    by metis_tac[MEM_body_filter_imp_pseudo_filter] >>
  metis_tac[EVERY_MEM_imp]
QED

(* Cross-bi inst_id equivalence for canonical_dep *)
Theorem canonical_dep_cross_bi_equiv:
  !bi bi' x y x' y'.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi') /\
    EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi') /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi') /\
    MEM x' (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y' (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
    (canonical_dep bi x y <=> canonical_dep bi x' y')
Proof
  rpt strip_tac >>
  `from_block bi x` by metis_tac[from_block_every_cross_bi] >>
  `from_block bi y` by metis_tac[from_block_every_cross_bi] >>
  `from_block bi x'` by metis_tac[from_block_every_body_bi] >>
  `from_block bi y'` by metis_tac[from_block_every_body_bi] >>
  `in_np_body bi x /\ in_np_body bi y /\
   in_np_body bi x' /\ in_np_body bi y'`
    by metis_tac[from_block_imp_in_np_body_local] >>
  `set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands) /\
   set (operand_vars y.inst_operands) = set (operand_vars y'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_filtered_local] >>
  `set x.inst_outputs = set x'.inst_outputs /\
   set y.inst_outputs = set y'.inst_outputs`
    by metis_tac[from_block_same_inst_id_outputs_filtered_local] >>
  `(is_barrier x <=> is_barrier x') /\ (is_barrier y <=> is_barrier y')`
    by metis_tac[from_block_same_inst_id_barrier_filtered_local] >>
  `x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id` by simp[] >>
  mp_tac (Q.SPECL [`bi`, `x`, `y`, `x'`, `y'`] canonical_dep_inst_id_equiv) >>
  simp[]
QED

(* Unpack canonical_topo_inv *)
Theorem canonical_topo_inv_mem:
  !fn blocks bb.
    canonical_topo_inv fn blocks /\ MEM bb blocks ==>
    ?bb_orig. MEM bb_orig fn.fn_blocks /\ bb.bb_label = bb_orig.bb_label /\
      topo_sorted (canonical_dep bb_orig.bb_instructions)
        (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)
Proof
  simp[canonical_topo_inv_def] >> metis_tac[]
QED

(* Under wf_function, two blocks with same label are equal *)
Theorem wf_fn_blocks_same_label_eq:
  !fn bb1 bb2.
    wf_function fn /\ MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    bb1.bb_label = bb2.bb_label ==> bb1 = bb2
Proof
  simp[wf_function_def, fn_labels_def] >> metis_tac[all_distinct_map_mem_inj]
QED

(* FILTER with conj predicate equals nested FILTER *)
Theorem FILTER_conj_eq_nested:
  !P Q (l:'a list). FILTER (\x. P x /\ Q x) l = FILTER Q (FILTER P l)
Proof
  gen_tac >> gen_tac >> Induct_on `l` >> simp[] >>
  Cases_on `P h` >> Cases_on `Q h` >> simp[]
QED

(* topo_sorted preserved under FILTER predicate refinement *)
Theorem topo_sorted_FILTER_conj:
  !dep P Q l. topo_sorted dep (FILTER P l) ==>
    topo_sorted dep (FILTER (\x. P x /\ Q x) l)
Proof
  rpt strip_tac >>
  simp[FILTER_conj_eq_nested] >>
  match_mp_tac topo_sorted_FILTER >> simp[]
QED

(* Applying topo_sorted_FILTER_conj to block_body *)
Theorem topo_sorted_block_body_filter:
  !dep bb. topo_sorted dep (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    topo_sorted dep (block_body bb)
Proof
  simp[block_body_def] >>
  rpt strip_tac >>
  simp[FILTER_conj_eq_nested] >>
  match_mp_tac topo_sorted_FILTER >> simp[]
QED

(* ===== dft_fn_output_topo_sorted ===== *)

Theorem dft_fn_output_topo_sorted:
  !fn bb bb'.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    MEM bb' (dft_fn fn).fn_blocks /\
    bb.bb_label = bb'.bb_label ==>
    topo_sorted (canonical_dep bb.bb_instructions)
      (MAP (choose_original (block_body bb)) (block_body bb'))
Proof
  rpt strip_tac >>
  (* canonical_topo_inv from dft_fn *)
  `canonical_topo_inv fn (dft_fn fn).fn_blocks` by
    metis_tac[dft_fn_canonical_topo_inv] >>
  (* Get block_perm_of for bb' *)
  `all_blocks_perm_of fn (dft_fn fn).fn_blocks` by
    metis_tac[dft_fn_all_perm_of] >>
  `block_perm_of fn bb'` by
    (fs[all_blocks_perm_of_def, EVERY_MEM]) >>
  (* Unpack invariant for bb' — get bb_orig *)
  `?bb_orig. MEM bb_orig fn.fn_blocks /\
    bb'.bb_label = bb_orig.bb_label /\
    topo_sorted (canonical_dep bb_orig.bb_instructions)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions)` by
    metis_tac[canonical_topo_inv_mem] >>
  (* bb_orig = bb by label uniqueness *)
  `bb_orig = bb` by metis_tac[wf_fn_blocks_same_label_eq] >>
  gvs[] >>
  (* EVERY from_block + PERM + pseudo-filter from block_perm_of_elim *)
  `EVERY (\i. from_block bb.bb_instructions i)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions) /\
   PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))
        (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
   FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions =
   FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` by
    metis_tac[block_perm_of_elim] >>
  simp[] >>
  (* ALL_DISTINCT inst_ids for FILTER ~is_pseudo bb.bb_instructions *)
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (irule all_distinct_map_filter >> metis_tac[bb_inst_ids_distinct]) >>
  (* Bridge FILTER -> block_body via topo_sorted_FILTER *)
  `topo_sorted (canonical_dep bb.bb_instructions) (block_body bb')` by
    (irule topo_sorted_block_body_filter >> simp[]) >>
  (* EVERY from_block for FILTER ~is_pseudo bb.bb_instructions *)
  `EVERY (\i. from_block bb.bb_instructions i)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    metis_tac[from_block_MEM_filter] >>
  (* block_body elements are in FILTER ~pseudo/\~terminator *)
  `!i. MEM i (block_body bb') ==>
    MEM i (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb'.bb_instructions)` by
    simp[block_body_def] >>
  `!i. MEM i (block_body bb) ==>
    MEM i (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions)` by
    simp[block_body_def] >>
  (* Apply map_choose_original_topo_sorted_restricted *)
  (* irule produces conjuncts in reverse order: cross-bi, witness, ALL_DISTINCT, topo_sorted *)
  irule map_choose_original_topo_sorted_restricted >>
  rpt conj_tac
  >- (* canonical_dep cross-bi equivalence via inst_id *)
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bb.bb_instructions`,`bb'.bb_instructions`,
       `x`,`y`,`x'`,`y'`] canonical_dep_cross_bi_equiv) >>
     simp[block_body_def, MEM_FILTER] >>
     rewrite_tac[FILTER_FILTER] >>
     simp[MEM_FILTER])
  >- (* witness: choose_original finds corresponding inst *)
    (rpt strip_tac >>
     qspecl_then [`fn`,`bb`,`bb'`,`i`] mp_tac block_body_from_block >>
     simp[] >> strip_tac >>
     qexists `j` >> simp[])
  >- (* ALL_DISTINCT *)
    metis_tac[block_body_all_distinct]
  >- (* topo_sorted *)
    simp[]
QED

(* ===== Per-block simulation ===== *)

Theorem block_body_canonical_equiv:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    topo_sorted (canonical_dep bb.bb_instructions)
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    (?e1 e2. run_insts fuel ctx (block_body bb) s = Error e1 /\
             run_insts fuel ctx (block_body bb') s = Error e2) \/
    run_insts fuel ctx (block_body bb) s =
    run_insts fuel ctx (block_body bb') s
Proof
  rpt strip_tac >>
  qabbrev_tac `l1 = block_body bb` >>
  qabbrev_tac `l2_raw = block_body bb'` >>
  qabbrev_tac `l2 = MAP (choose_original l1) l2_raw` >>
  `run_insts fuel ctx l2_raw s = run_insts fuel ctx l2 s` by
    (simp[Abbr `l2`] >>
     irule run_insts_pointwise_equiv >> simp[LENGTH_MAP] >>
     rpt strip_tac >>
     irule map_choose_original_step_equiv >>
     simp[Abbr `l1`] >> conj_asm1_tac
     >- (rpt strip_tac >> simp[Abbr `l2_raw`] >>
         metis_tac[block_body_from_block])
     >> metis_tac[block_body_all_distinct]) >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `PERM l1 l2` by
    (simp[Abbr `l2`, Abbr `l1`] >> metis_tac[block_body_choose_perm]) >>
  `ALL_DISTINCT l1` by
    (simp[Abbr `l1`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!k. k < LENGTH bb.bb_instructions /\ is_terminator (EL k bb.bb_instructions).inst_opcode ==>
       k = PRE (LENGTH bb.bb_instructions)` by fs[bb_well_formed_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) l1` by
    simp[Abbr `l1`, block_body_def, EVERY_MEM, MEM_FILTER] >>
  `!x. MEM x l1 ==> from_block bb.bb_instructions x` by
    (gen_tac >> strip_tac >>
     simp[from_block_def] >>
     qexists_tac `x` >> simp[] >>
     pop_assum mp_tac >> simp[Abbr `l1`, block_body_def, MEM_FILTER]) >>
  `!x. MEM x l1 ==> MEM x bb.bb_instructions /\ ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode` by
    (gen_tac >> strip_tac >>
     pop_assum mp_tac >> simp[Abbr `l1`, block_body_def, MEM_FILTER]) >>
  `!x y. MEM x l1 /\ MEM y l1 /\ x <> y ==>
         DISJOINT (set (inst_defs x)) (set (inst_defs y))` by
    metis_tac[ssa_disjoint_defs] >>
  qabbrev_tac `fbi = FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `dep = \x y. canonical_dep bb.bb_instructions x y /\ MEM x fbi /\ MEM y fbi` >>
  `!x. MEM x l1 ==> MEM x fbi` by
    (gen_tac >> strip_tac >>
     pop_assum mp_tac >> simp[Abbr `l1`, Abbr `fbi`, block_body_def, MEM_FILTER]) >>
  `!x. MEM x fbi ==> MEM x l1` by
    (gen_tac >> strip_tac >>
     pop_assum mp_tac >> simp[Abbr `l1`, Abbr `fbi`, block_body_def, MEM_FILTER] >>
     metis_tac[]) >>
  `topo_sorted (full_dep (build_full_eda bb.bb_instructions)) l1` by
    (simp[Abbr `l1`] >> metis_tac[block_body_topo_sorted]) >>
  `!i j. i < j /\ j < LENGTH l1 ==>
         ~canonical_dep bb.bb_instructions (EL i l1) (EL j l1)` by
    (rpt strip_tac >>
     `i < LENGTH l1` by decide_tac >>
     `MEM (EL i l1) l1 /\ MEM (EL j l1) l1` by metis_tac[EL_MEM] >>
     `from_block bb.bb_instructions (EL i l1) /\ from_block bb.bb_instructions (EL j l1)` by metis_tac[] >>
     `~full_dep (build_full_eda bb.bb_instructions) (EL i l1) (EL j l1)` by
       metis_tac[topo_sorted_def] >>
     metis_tac[canonical_dep_imp_full_dep_local]) >>
  `topo_sorted dep l1` by
    simp[topo_sorted_def, Abbr `dep`] >>
  `topo_sorted (canonical_dep bb.bb_instructions) l2` by
    simp[Abbr `l2`, Abbr `l1`, Abbr `l2_raw`] >>
  `!i j. i < j /\ j < LENGTH l2 ==>
         ~canonical_dep bb.bb_instructions (EL i l2) (EL j l2)` by
    metis_tac[topo_sorted_def] >>
  `topo_sorted dep l2` by
    simp[topo_sorted_def, Abbr `dep`] >>
  `topo_sorted (TC dep) l1` by
    (irule topo_sorted_tc_closed >> simp[Abbr `dep`]) >>
  `topo_sorted (TC dep) l2` by
    (irule topo_sorted_tc_closed >>
     simp[Abbr `dep`] >>
     `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
     simp[] >> metis_tac[PERM_MEM_EQ]) >>
  `!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
         ~TC dep x y /\ ~TC dep y x ==> ef_commutes x y` by
    (rpt strip_tac >>
     qspecl_then [`bb.bb_instructions`, `x`, `y`] mp_tac
       canonical_tc_incomp_ef_commutes_body_restricted >>
     simp[Abbr `dep`, Abbr `fbi`] >>
     metis_tac[MEM_FILTER]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) l1` by
    simp[Abbr `l1`, block_body_def, EVERY_MEM, MEM_FILTER] >>
  `!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
         TC dep b y \/ TC dep y b` by
    (rpt strip_tac >>
     qspecl_then [`bb.bb_instructions`, `b`, `y`] mp_tac
       canonical_dep_barrier_tc_connected_restricted >>
     simp[Abbr `dep`, Abbr `fbi`] >>
     metis_tac[MEM_FILTER]) >>
  qspecl_then [`l1`, `l2`, `dep`, `fuel`, `ctx`, `s`]
    mp_tac run_insts_topo_full_lift_ef >>
  simp[] >>
  simp[Abbr `l1`] >>
  qpat_x_assum `run_insts fuel ctx l2_raw s = _`
    (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]) >>
  simp[Abbr `l2_raw`]
QED

(* front_full_equiv with canonical_dep precondition *)
Theorem front_full_equiv_canonical:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    topo_sorted (canonical_dep bb.bb_instructions)
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (FRONT bb.bb_instructions) s)
      (run_insts fuel ctx (FRONT bb'.bb_instructions) s)
Proof
  rpt strip_tac >>
  imp_res_tac block_perm_of_elim >>
  simp[pseudos_prefix_front_decomposition, GSYM block_body_def, run_insts_append] >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  Cases_on `run_insts fuel ctx phis s` >> simp[lift_result_def]
  >- (drule_all block_body_canonical_equiv >>
      disch_then (qspecl_then [`fuel`,`ctx`,`v`] strip_assume_tac) >>
      gvs[lift_result_def] >> irule lift_result_refl)
  >- simp[execution_equiv_refl]
  >- simp[revert_equiv_def]
  >- simp[execution_equiv_refl]
QED

(* Per-block lift using canonical_dep *)
Theorem block_perm_of_exec_block_lift_canonical:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    topo_sorted (canonical_dep bb.bb_instructions)
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    ((?e. exec_block fuel ctx bb (s with vs_inst_idx := 0) = Error e) /\
     (?e. exec_block fuel ctx bb' (s with vs_inst_idx := 0) = Error e)) \/
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := 0))
      (exec_block fuel ctx bb' (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by
    (qpat_assum `wf_function _`
       (strip_assume_tac o REWRITE_RULE[wf_function_def]) >>
     res_tac) >>
  drule_all block_perm_of_same_last >> strip_tac >>
  drule_all block_perm_of_same_length >> strip_tac >>
  drule_all front_full_equiv_canonical >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] assume_tac) >>
  irule exec_block_front_lr_lift >> asm_rewrite_tac[]
QED

(* ===== DFT preserves fn_pseudos_prefix ===== *)

Theorem pseudos_prefix_filter_append:
  !l1 l2 bb.
    (!x. MEM x l1 ==> is_pseudo x.inst_opcode) /\
    (!x. MEM x l2 ==> ~is_pseudo x.inst_opcode) ==>
    pseudos_prefix (bb with bb_instructions := l1 ++ l2)
Proof
  simp[pseudos_prefix_def] >> rpt strip_tac >>
  Cases_on `j < LENGTH l1` >- (
    `i < LENGTH l1` by decide_tac >>
    simp[EL_APPEND1] >>
    `MEM (EL i l1) l1` by metis_tac[MEM_EL] >>
    metis_tac[]) >>
  `j - LENGTH l1 < LENGTH l2` by (
    fs[LENGTH_APPEND] >> decide_tac) >>
  `EL j (l1 ++ l2) = EL (j - LENGTH l1) l2` by simp[EL_APPEND2] >>
  `MEM (EL (j - LENGTH l1) l2) l2` by metis_tac[MEM_EL] >>
  metis_tac[]
QED

Theorem dft_block_pseudos_prefix:
  !order bb. pseudos_prefix (dft_block order bb)
Proof
  rw[dft_block_def, LET_THM] >>
  irule pseudos_prefix_filter_append >> simp[MEM_FILTER] >>
  rpt strip_tac >>
  `eda_wf (build_full_eda bb.bb_instructions) bb.bb_instructions` by
    simp[build_full_eda_wf] >>
  `EVERY (\i. MEM i bb.bb_instructions)
         (entry_instructions bb.bb_instructions order
            (build_full_eda bb.bb_instructions))` by
    simp[entry_instructions_mem] >>
  imp_res_tac schedule_output_from_block
QED

Theorem dft_process_one_preserves_pseudos_prefix:
  !cfg lr fn st lbl.
    EVERY pseudos_prefix st.dls_blocks ==>
    EVERY pseudos_prefix (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  irule every_map_replace >> simp[] >>
  irule dft_block_pseudos_prefix
QED

Theorem dft_loop_step_preserves_pseudos_prefix:
  !cfg lr fn trip.
    EVERY pseudos_prefix (FST trip).dls_blocks ==>
    EVERY pseudos_prefix (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_pseudos_prefix >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem funpow_dft_loop_preserves_pseudos_prefix:
  !n cfg lr fn trip.
    EVERY pseudos_prefix (FST trip).dls_blocks ==>
    EVERY pseudos_prefix (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_preserves_pseudos_prefix >>
  first_x_assum irule >> simp[]
QED

Theorem dft_fn_pseudos_prefix:
  !fn. fn_pseudos_prefix fn ==> fn_pseudos_prefix (dft_fn fn)
Proof
  rpt strip_tac >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  simp[fn_pseudos_prefix_def] >>
  rewrite_tac[GSYM EVERY_MEM] >>
  irule funpow_dft_loop_preserves_pseudos_prefix >>
  simp[fn_pseudos_prefix_def, EVERY_MEM] >>
  fs[fn_pseudos_prefix_def]
QED

(* ===== Function-level: run_blocks lift_result ===== *)

val run_blocks_SUC = let
  val rb = run_blocks_def
  val (vars, _) = strip_forall (concl rb)
  val [sv,fv,fnv,cv] = vars
  val inst = SPECL [sv, mk_comb(``SUC``, fv), fnv, cv] rb
in SIMP_RULE (srw_ss()) [] inst |> GENL [sv, fv, fnv, cv] end;

Theorem dft_fn_run_blocks_lift:
  !fuel ctx fn s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dft_fn fn) s)
Proof
  MAP_EVERY qid_spec_tac [`s`, `fn`] >>
  Induct_on `fuel`
  >- (rpt strip_tac >> simp[run_blocks_def, lift_result_def])
  >> rpt strip_tac >>
  ONCE_REWRITE_TAC [run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (* NONE: both NONE *)
    (`lookup_block s.vs_current_bb (dft_fn fn).fn_blocks = NONE` by
       metis_tac[dft_fn_lookup_block_none] >>
     simp[lift_result_def])
  >> (* SOME bb *)
  simp[] >> rename1 `SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `?bb'. lookup_block s.vs_current_bb (dft_fn fn).fn_blocks = SOME bb'` by
    metis_tac[dft_fn_lookup_block] >>
  `MEM bb' (dft_fn fn).fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb'.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `bb.bb_label = bb'.bb_label` by simp[] >>
  `block_perm_of fn bb'` by metis_tac[dft_fn_lookup_perm_of] >>
  `bb_well_formed bb` by
    (qpat_assum `wf_function fn`
       (strip_assume_tac o REWRITE_RULE[wf_function_def]) >>
     res_tac) >>
  `bb_well_formed bb'` by metis_tac[dft_fn_blocks_well_formed] >>
  `pseudos_prefix bb` by
    (fs[fn_pseudos_prefix_def] >> metis_tac[EVERY_MEM]) >>
  `pseudos_prefix bb'` by
    (`fn_pseudos_prefix (dft_fn fn)` by metis_tac[dft_fn_pseudos_prefix] >>
     fs[fn_pseudos_prefix_def] >> metis_tac[EVERY_MEM]) >>
  `topo_sorted (canonical_dep bb.bb_instructions)
    (MAP (choose_original (block_body bb)) (block_body bb'))` by
    metis_tac[dft_fn_output_topo_sorted] >>
  drule_all block_perm_of_exec_block_lift_canonical >> simp[] >>
  strip_tac >>
  Cases_on `exec_block fuel ctx bb (s with vs_inst_idx := 0)` >>
  Cases_on `exec_block fuel ctx bb' (s with vs_inst_idx := 0)` >>
  (* Use the universally-quantified disjunction: instantiate s'' = s *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[] >>
  rpt strip_tac >>
  gvs[lift_result_def, exec_result_distinct] >>
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  IF_CASES_TAC >> gvs[lift_result_def, execution_equiv_refl, revert_equiv_def] >>
  first_x_assum irule >> simp[]
QED

(* ===== Function-level: run_function lift_result ===== *)

Theorem dft_fn_entry_label:
  !fn. fn_entry_label (dft_fn fn) = fn_entry_label fn
Proof
  gen_tac >>
  Cases_on `fn.fn_blocks` >- (
    Cases_on `(dft_fn fn).fn_blocks` >- (
      simp[fn_entry_label_def, entry_block_def]) >>
    assume_tac (Q.SPEC `fn` dft_fn_labels_map) >>
    gvs[MAP_EQ_NIL]) >>
  Cases_on `(dft_fn fn).fn_blocks` >- (
    assume_tac (Q.SPEC `fn` dft_fn_labels_map) >>
    gvs[MAP_EQ_NIL]) >>
  simp[fn_entry_label_def, entry_block_def] >>
  assume_tac (Q.SPEC `fn` dft_fn_labels_map) >> gvs[]
QED

Theorem dft_fn_run_function_lift:
  !fuel ctx fn s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)
Proof
  rpt strip_tac >>
  simp[run_function_def] >>
  `fn_entry_label (dft_fn fn) = fn_entry_label fn` by
    simp[dft_fn_entry_label] >>
  simp[] >>
  Cases_on `fn_entry_label fn` >> simp[lift_result_def] >>
  irule dft_fn_run_blocks_lift >> simp[]
QED

(* ===== Fuel determinism ===== *)

Theorem run_function_fuel_determ:
  !fuel fuel' ctx fn s.
    terminates (run_function fuel ctx fn s) /\
    terminates (run_function fuel' ctx fn s) ==>
    run_function fuel ctx fn s = run_function fuel' ctx fn s
Proof
  rpt strip_tac >>
  simp[run_function_def] >>
  Cases_on `fn_entry_label fn` >> gvs[run_function_def, terminates_def] >>
  `!e. run_blocks fuel ctx fn
       (s with <| vs_current_bb := x; vs_inst_idx := 0 |>) <> Error e` by
    (gvs[run_function_def] >>
     Cases_on `run_blocks fuel ctx fn
       (s with <| vs_current_bb := x; vs_inst_idx := 0 |>)` >>
     gvs[terminates_def]) >>
  `!e. run_blocks fuel' ctx fn
       (s with <| vs_current_bb := x; vs_inst_idx := 0 |>) <> Error e` by
    (gvs[run_function_def] >>
     Cases_on `run_blocks fuel' ctx fn
       (s with <| vs_current_bb := x; vs_inst_idx := 0 |>)` >>
     gvs[terminates_def]) >>
  Cases_on `fuel <= fuel'`
  >- metis_tac[fuel_mono |> CONJUNCTS |> last]
  >> (`fuel' <= fuel` by simp[] >> metis_tac[fuel_mono |> CONJUNCTS |> last])
QED

(* ===== Pass-level correctness ===== *)

Theorem dft_pass_correct:
  !fn ctx s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    pass_correct (state_equiv {}) (execution_equiv {}) revert_equiv
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (dft_fn fn) s)
Proof
  rpt strip_tac >>
  match_mp_tac passSimulationProofsTheory.lift_result_implies_pass_correct_proof >>
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) >>
  conj_tac >- metis_tac[dft_fn_run_function_lift] >>
  conj_tac >- metis_tac[run_function_fuel_determ] >>
  metis_tac[run_function_fuel_determ]
QED


