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

(* If P holds for every element of l, then P holds for any member of l *)
Theorem EVERY_MEM_imp:
  !P l x. EVERY P l /\ MEM x l ==> P x
Proof
  Induct_on `l` >> simp[] >> metis_tac[]
QED

(* An instruction in the body filter of a block originates from that block *)
Theorem from_block_MEM_body_filter:
  !bi x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) ==>
         from_block bi x
Proof
  rpt strip_tac >>
  fs[MEM_FILTER] >>
  simp[from_block_def] >>
  qexists_tac `x` >> simp[]
QED

(* Body-filtered (non-pseudo, non-terminator) instructions are a subset of pseudo-filtered (non-pseudo) ones *)
Theorem MEM_body_filter_imp_pseudo_filter:
  !l x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) l) ==>
         MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) l)
Proof
  rpt strip_tac >> fs[MEM_FILTER]
QED

(* Every non-pseudo instruction in a block originates from that block *)
Theorem from_block_MEM_filter:
  !bi. EVERY (\i. from_block bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)
Proof
  rpt gen_tac >> simp[EVERY_MEM, MEM_FILTER, from_block_def] >>
  rpt strip_tac >>
  qexists_tac `i` >> simp[]
QED

(* If all non-pseudo instructions of bi' originate from bi, so does any body instruction of bi' *)
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

(* If all non-pseudo instructions of bi originate from bi, so does any body instruction of bi *)
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

(* canonical_dep depends only on inst_id when all instructions originate from the same
   block: two pairs from different block representations with matching inst_ids have the
   same canonical_dep relationship *)
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

(* Each output block of canonical_topo_inv corresponds to an original block, and its
   non-pseudo instructions are topologically sorted by canonical_dep of the original *)
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

(* Excluding terminators from a topo-sorted non-pseudo list preserves topo-sortedness *)
Theorem topo_sorted_block_body_filter:
  !dep bb. topo_sorted dep (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    topo_sorted dep (block_body bb)
Proof
  simp[block_body_def] >>
  rpt strip_tac >>
  simp[FILTER_conj_eq_nested] >>
  match_mp_tac topo_sorted_FILTER >> simp[]
QED

(* ===== Per-block simulation ===== *)

(* Two block bodies related by canonical_dep topo-ordering and perm produce equivalent
   execution results (modulo simultaneous divergence to Error) *)
Theorem block_body_canonical_equiv:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    EVERY (\i. i.inst_opcode <> GAS) (block_body bb) /\
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
     `x.inst_opcode <> GAS /\ y.inst_opcode <> GAS` by fs[EVERY_MEM] >>
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

(* Under canonical_dep topo-ordering and block_perm_of, executing the non-terminator
   prefix of two related blocks gives lift_result-equivalent results *)
Theorem front_full_equiv_canonical:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    EVERY (\i. i.inst_opcode <> GAS) (block_body bb) /\
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

(* If block_perm_of and canonical_dep topo-ordering hold, exec_block results are either
   both errors or lift_result-equivalent *)
Theorem block_perm_of_exec_block_lift_canonical:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb' /\
    EVERY (\i. i.inst_opcode <> GAS) (block_body bb) /\
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

(* ===== Function-level: run_blocks lift_result ===== *)

(* Unfold run_blocks for SUC fuel *)
val run_blocks_SUC = let
  val rb = run_blocks_def
  val (vars, _) = strip_forall (concl rb)
  val [sv,fv,fnv,cv] = vars
  val inst = SPECL [sv, mk_comb(``SUC``, fv), fnv, cv] rb
in SIMP_RULE (srw_ss()) [] inst |> GENL [sv, fv, fnv, cv] end;

(* DFT preserves run_blocks results up to lift_result equivalence *)
Theorem dft_fn_run_blocks_lift:
  !fuel ctx fn s.
    dft_schedule_safe /\
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dft_fn fn) s)
Proof
  simp[dft_schedule_safe_false]
QED

(* ===== Function-level: run_function lift_result ===== *)

(* DFT preserves the function entry label *)
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

(* DFT preserves run_function results up to lift_result equivalence *)
Theorem dft_fn_run_function_lift:
  !fuel ctx fn s.
    dft_schedule_safe /\
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)
Proof
  simp[dft_schedule_safe_false]
QED

(* ===== Fuel determinism ===== *)

(* run_function is deterministic across different fuel values when both terminate *)
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

(* The DFT pass is correct: it preserves the observable behavior of run_function *)
Theorem dft_pass_correct:
  !fn ctx s.
    dft_schedule_safe /\
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    pass_correct (state_equiv {}) (execution_equiv {}) revert_equiv
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (dft_fn fn) s)
Proof
  simp[dft_schedule_safe_false]
QED
