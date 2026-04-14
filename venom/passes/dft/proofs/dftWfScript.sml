(*
 * DFT Pass — Well-Formedness Preservation
 *
 * Key results:
 *   terminator_not_dep_target — no instruction depends on terminator
 *   schedule_terminator_last — terminator is emitted last by schedule
 *
 * Used by dftCorrectness to prove dft_block_well_formed.
 *)

Theory dftWf
Ancestors
  dftCompleteness dftStructural dftDefs venomWf
  dftTopoSort dftScheduleFixed dftIdempotent dftPipelineInvar
  allocaRemapSSA venomInst
  list rich_list sorting
  finite_map pred_set pair arithmetic

(* ================================================================
   Section 1: No instruction depends on the terminator
   ================================================================ *)

(* The terminator (LAST bi) is never a dep of any non-pseudo instruction.
   Proof: eda_topo_compatible says every dep is at a strictly earlier index.
   LAST bi is at the maximum index PRE(LENGTH bi). If LAST bi were a dep of
   some instruction, that instruction would need to be at an index > PRE(LENGTH bi),
   which is impossible since indices are < LENGTH bi. *)
Theorem terminator_not_dep_target:
  !bi eda order i.
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    ~is_pseudo (LAST bi).inst_opcode /\
    eda_wf eda bi /\
    MEM i bi /\ ~is_pseudo i.inst_opcode ==>
    ~MEM (LAST bi).inst_id
      (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  gvs[MEM_MAP] >>
  rename1 `MEM d (inst_all_deps bi order eda i)` >>
  `MEM d bi` by metis_tac[inst_all_deps_mem] >>
  (* eda_topo_compatible gives d at earlier index than i *)
  `~is_pseudo d.inst_opcode` by (
    `?kd. kd < LENGTH bi /\ EL kd bi = d` by metis_tac[MEM_EL] >>
    spose_not_then assume_tac >>
    (* d is pseudo but d.inst_id = (LAST bi).inst_id. Since ALL_DISTINCT
       on inst_ids, d and LAST bi are at the same index, hence d = LAST bi.
       But LAST bi is not pseudo — contradiction. *)
    `LAST bi = EL (PRE (LENGTH bi)) bi` by simp[LAST_EL] >>
    `PRE (LENGTH bi) < LENGTH bi` by (Cases_on `bi` >> gvs[]) >>
    `(EL kd bi).inst_id = (EL (PRE (LENGTH bi)) bi).inst_id` by gvs[] >>
    `EL kd (MAP (\x. x.inst_id) bi) = EL (PRE (LENGTH bi)) (MAP (\x. x.inst_id) bi)` by
      simp[EL_MAP] >>
    `kd = PRE (LENGTH bi)` by (
      qspecl_then [`MAP (\x. x.inst_id) bi`, `kd`, `PRE (LENGTH bi)`] mp_tac
        ALL_DISTINCT_EL_IMP >> simp[]) >>
    gvs[]) >>
  (* eda_topo_compatible: d is at earlier index than i *)
  `?id j. id < j /\ j < LENGTH bi /\ id < LENGTH bi /\
          EL id bi = d /\ EL j bi = i` by (
    gvs[eda_topo_compatible_def]) >>
  (* d.inst_id = (LAST bi).inst_id, so d is at index PRE(LENGTH bi) *)
  `PRE (LENGTH bi) < LENGTH bi` by (Cases_on `bi` >> gvs[]) >>
  `(EL id bi).inst_id = (EL (PRE (LENGTH bi)) bi).inst_id` by
    gvs[LAST_EL] >>
  `EL id (MAP (\x. x.inst_id) bi) =
   EL (PRE (LENGTH bi)) (MAP (\x. x.inst_id) bi)` by simp[EL_MAP] >>
  `id = PRE (LENGTH bi)` by (
    qspecl_then [`MAP (\x. x.inst_id) bi`, `id`, `PRE (LENGTH bi)`] mp_tac
      ALL_DISTINCT_EL_IMP >> simp[]) >>
  (* id = PRE(LENGTH bi) < j < LENGTH bi → contradiction *)
  gvs[]
QED

(* ================================================================
   Section 2: DFS emits bottom-of-stack element last
   ================================================================ *)

(* Predicate: no stack item has the given inst_id *)
Definition id_not_in_stack_def:
  id_not_in_stack tid [] = T /\
  id_not_in_stack tid (DfsProcess i :: rest) =
    (i.inst_id <> tid /\ id_not_in_stack tid rest) /\
  id_not_in_stack tid (DfsEmit i :: rest) =
    (i.inst_id <> tid /\ id_not_in_stack tid rest)
End

Triviality id_not_in_stack_append[simp]:
  !l1 l2 tid.
    id_not_in_stack tid (l1 ++ l2) <=>
    id_not_in_stack tid l1 /\ id_not_in_stack tid l2
Proof
  Induct >> simp[id_not_in_stack_def] >>
  Cases >> simp[id_not_in_stack_def] >> metis_tac[]
QED

Triviality id_not_in_map_process[simp]:
  !l tid.
    id_not_in_stack tid (MAP DfsProcess l) <=>
    EVERY (\i. i.inst_id <> tid) l
Proof
  Induct >> simp[id_not_in_stack_def]
QED

(* flip_operands preserves inst_id *)
Triviality flip_id[simp]:
  (flip_operands i).inst_id = i.inst_id
Proof
  simp[flip_operands_def] >>
  CASE_TAC >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >> rw[] >> simp[]
QED

(* Children of any instruction don't have the terminator's id *)
Triviality children_no_tid:
  !bi order eda offspring_map top tid.
    MEM top bi ==> ~is_pseudo top.inst_opcode ==>
    eda_wf eda bi ==>
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM tid (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) ==>
    EVERY (\x. x.inst_id <> tid)
      (sort_children bi order eda offspring_map top
         (inst_all_deps bi order eda top))
Proof
  rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM x (inst_all_deps bi order eda top)` by
    metis_tac[sort_children_mem] >>
  spose_not_then assume_tac >> gvs[] >>
  first_x_assum (qspec_then `top` mp_tac) >> simp[] >>
  simp[MEM_MAP] >> qexists_tac `x` >> simp[]
QED

(* The children + DfsEmit pushed by processing a non-pseudo instruction
   don't contain tid *)
Triviality pushed_no_tid:
  !bi order eda offspring_map top tid.
    MEM top bi ==> ~is_pseudo top.inst_opcode ==>
    top.inst_id <> tid ==>
    eda_wf eda bi ==>
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM tid (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) ==>
    let sorted = sort_children bi order eda offspring_map top
                   (inst_all_deps bi order eda top) in
    let inst' = if is_flippable top.inst_opcode /\
                   sorted <> inst_all_deps bi order eda top
                then flip_operands top else top in
    id_not_in_stack tid
      (MAP DfsProcess sorted ++ [DfsEmit inst'])
Proof
  rpt strip_tac >> simp[LET_THM, id_not_in_stack_def] >>
  conj_tac
  >- (drule children_no_tid >> rpt (disch_then drule) >>
      strip_tac >> gvs[id_not_in_map_process])
  >> (rw[] >> simp[])
QED

(* Invariant for the DFS FUNPOW. tid = (LAST bi).inst_id.
   Either:
   (A) DfsProcess with inst_id = tid is at stack bottom, not visited,
       and no other stack item has tid
   (B) DfsEmit with inst_id = tid is at stack bottom, and no other
       stack item has tid
   (C) tid has been emitted as LAST output, and stack is empty *)
Definition bottom_inv_def:
  bottom_inv tid state <=>
    (?prefix inst.
       state.ds_stack = prefix ++ [DfsProcess inst] /\
       inst.inst_id = tid /\
       ~is_pseudo inst.inst_opcode /\
       id_not_in_stack tid prefix /\
       ~MEM tid state.ds_visited) \/
    (?prefix inst.
       state.ds_stack = prefix ++ [DfsEmit inst] /\
       inst.inst_id = tid /\
       id_not_in_stack tid prefix) \/
    (state.ds_output <> [] /\
     (LAST state.ds_output).inst_id = tid /\
     state.ds_stack = [])
End

(* Helper: when the stack top is processed (not the bottom item),
   the bottom item is preserved and new items above don't contain tid.
   This factors the common case analysis for Phases A, B, and C. *)

(* dfs_step preserves bottom_inv — helper for pushed items *)
Triviality pushed_stack_no_tid:
  !bi order eda offspring_map top tid rest.
    MEM top bi /\ ~is_pseudo top.inst_opcode /\
    top.inst_id <> tid /\ eda_wf eda bi /\
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM tid (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) /\
    id_not_in_stack tid rest ==>
    id_not_in_stack tid
      (MAP DfsProcess
         (sort_children bi order eda offspring_map top
            (inst_all_deps bi order eda top)) ++
       [DfsEmit (if is_flippable top.inst_opcode /\
          sort_children bi order eda offspring_map top
            (inst_all_deps bi order eda top) <>
          inst_all_deps bi order eda top
        then flip_operands top else top)] ++ rest)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bi`,`order`,`eda`,`offspring_map`,`top`,`tid`]
            pushed_no_tid) >>
  simp[LET_THM]
QED

(* dfs_step preserves bottom_inv when tid is not a dep target.
   Key: asm_rewrite_tac[dfs_step_def] resolves case on ds_stack
   using the stack equality from bottom_inv. *)
Theorem dfs_step_preserves_bottom_inv:
  !bi order eda offspring_map state tid.
    bottom_inv tid state ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM tid (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) ==>
    eda_wf eda bi ==>
    (!inst. MEM (DfsProcess inst) state.ds_stack /\
            ~MEM inst.inst_id state.ds_visited /\
            ~is_pseudo inst.inst_opcode ==>
            MEM inst bi) ==>
    bottom_inv tid (dfs_step bi order eda offspring_map T state)
Proof
  rpt strip_tac >> fs[bottom_inv_def]
  >- suspend "phaseA"
  >- suspend "phaseB"
  >> suspend "phaseC"
QED

(* Phase A: DfsProcess inst at bottom, inst.inst_id = tid.
   prefix=[]: inst at top → Phase B (DfsEmit at bottom).
   prefix=hd::pfx: process hd at top, bottom inst preserved. *)
Resume dfs_step_preserves_bottom_inv[phaseA]:
  Cases_on `prefix`
  (* prefix=[]: inst is at stack top, transitions to Phase B *)
  >- (gvs[id_not_in_stack_def] >>
      asm_rewrite_tac[dfs_step_def] >> simp[LET_THM] >>
      conj_tac
      >- (IF_CASES_TAC >> simp[])
      >> (irule children_no_tid >> simp[]))
  (* prefix=hd::pfx: process hd, bottom stays *)
  >> (rename1 `hd :: pfx` >>
      Cases_on `hd`
      (* DfsProcess at top: top is processed, bottom inst stays *)
      >- (gvs[id_not_in_stack_def] >>
          rename1 `DfsProcess top` >>
          asm_rewrite_tac[dfs_step_def] >> simp[] >>
          IF_CASES_TAC >> gvs[] >>
          IF_CASES_TAC >> gvs[] >>
          rewrite_tac[LET_THM] >> BETA_TAC >>
          `MEM top bi` by (
            qpat_x_assum `!inst'. _ ==> MEM inst' bi`
              (qspec_then `top` mp_tac) >> simp[]) >>
          conj_tac
          >- (irule children_no_tid >> simp[])
          >> (simp[id_not_in_stack_def] >> rw[] >> simp[]))
      (* DfsEmit at top: simp resolves entirely *)
      >> (gvs[id_not_in_stack_def] >>
          asm_rewrite_tac[dfs_step_def] >> simp[]))
QED

(* Phase B: DfsEmit inst at bottom, inst.inst_id = tid *)
Resume dfs_step_preserves_bottom_inv[phaseB]:
  Cases_on `prefix`
  >- (gvs[id_not_in_stack_def] >>
      asm_rewrite_tac[dfs_step_def] >> simp[id_not_in_stack_def])
  >> (rename1 `hd :: pfx` >>
      Cases_on `hd`
      (* DfsProcess at top *)
      >- (gvs[id_not_in_stack_def] >>
          rename1 `DfsProcess top` >>
          asm_rewrite_tac[dfs_step_def] >> simp[] >>
          IF_CASES_TAC >> gvs[] >>
          IF_CASES_TAC >> gvs[] >>
          rewrite_tac[LET_THM] >> BETA_TAC >>
          `MEM top bi` by (
            qpat_x_assum `!inst'. _ ==> MEM inst' bi`
              (qspec_then `top` mp_tac) >> simp[]) >>
          conj_tac
          >- (irule children_no_tid >> simp[])
          >> (simp[id_not_in_stack_def] >> rw[] >> simp[]))
      (* DfsEmit at top *)
      >> (gvs[id_not_in_stack_def] >>
          asm_rewrite_tac[dfs_step_def] >> simp[]))
QED

(* Phase C: already emitted, stack empty — dfs_step does nothing *)
Resume dfs_step_preserves_bottom_inv[phaseC]:
  gvs[dfs_step_def]
QED

Finalise dfs_step_preserves_bottom_inv

(* The stack items hypothesis is also preserved by dfs_step *)
Theorem dfs_step_stack_from_bi:
  !bi order eda offspring_map state.
    eda_wf eda bi ==>
    (!inst. MEM (DfsProcess inst) state.ds_stack /\
            ~MEM inst.inst_id state.ds_visited /\
            ~is_pseudo inst.inst_opcode ==> MEM inst bi) ==>
    (!inst. MEM (DfsProcess inst)
              (dfs_step bi order eda offspring_map T state).ds_stack /\
            ~MEM inst.inst_id
              (dfs_step bi order eda offspring_map T state).ds_visited /\
            ~is_pseudo inst.inst_opcode ==>
            MEM inst bi)
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM _ (dfs_step _ _ _ _ _ _).ds_stack` mp_tac >>
  qpat_x_assum `~MEM _ (dfs_step _ _ _ _ _ _).ds_visited` mp_tac >>
  Cases_on `state.ds_stack`
  >- (asm_rewrite_tac[dfs_step_def] >> simp[])
  >> rename1 `_ = hd :: rest` >>
     Cases_on `hd`
  >- suspend "DfsProcess"
  >> suspend "DfsEmit"
QED

Resume dfs_step_stack_from_bi[DfsProcess]:
  rename1 `_ = DfsProcess top :: _` >>
  asm_rewrite_tac[dfs_step_def] >> simp[] >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  (* visited / pseudo cases may be closed by gvs already *)
  simp[LET_THM, MEM_APPEND, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum irule >> gvs[MEM] >> NO_TAC) >>
  drule inst_all_deps_mem >>
  disch_then (qspecl_then [`order`, `top`, `inst`] mp_tac) >>
  gvs[sort_children_mem]
QED

Resume dfs_step_stack_from_bi[DfsEmit]:
  rename1 `_ = DfsEmit top :: _` >>
  asm_rewrite_tac[dfs_step_def] >> simp[]
QED

Finalise dfs_step_stack_from_bi

(* FUNPOW preservation *)
(* Auxiliary: stack_from_bi is preserved by FUNPOW dfs_step *)
Triviality funpow_stack_from_bi:
  !n bi order eda offspring_map state.
    eda_wf eda bi ==>
    (!inst. MEM (DfsProcess inst) state.ds_stack /\
            ~MEM inst.inst_id state.ds_visited /\
            ~is_pseudo inst.inst_opcode ==> MEM inst bi) ==>
    (!inst. MEM (DfsProcess inst)
              (FUNPOW (dfs_step bi order eda offspring_map T) n state).ds_stack /\
            ~MEM inst.inst_id
              (FUNPOW (dfs_step bi order eda offspring_map T) n state).ds_visited /\
            ~is_pseudo inst.inst_opcode ==> MEM inst bi)
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  `!inst. MEM (DfsProcess inst)
            (FUNPOW (dfs_step bi order eda offspring_map T) n state).ds_stack /\
          ~MEM inst.inst_id
            (FUNPOW (dfs_step bi order eda offspring_map T) n state).ds_visited /\
          ~is_pseudo inst.inst_opcode ==> MEM inst bi` by (
    last_x_assum (qspecl_then [`bi`, `order`, `eda`, `offspring_map`, `state`] mp_tac) >>
    simp[]) >>
  qspecl_then [`bi`, `order`, `eda`, `offspring_map`,
               `FUNPOW (dfs_step bi order eda offspring_map T) n state`]
    mp_tac dfs_step_stack_from_bi >> simp[]
QED

Theorem funpow_preserves_bottom_inv:
  !n bi order eda offspring_map state tid.
    bottom_inv tid state ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM tid (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) ==>
    eda_wf eda bi ==>
    (!inst. MEM (DfsProcess inst) state.ds_stack /\
            ~MEM inst.inst_id state.ds_visited /\
            ~is_pseudo inst.inst_opcode ==> MEM inst bi) ==>
    bottom_inv tid
      (FUNPOW (dfs_step bi order eda offspring_map T) n state)
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dfs_step_preserves_bottom_inv >> simp[] >>
  `bottom_inv tid (FUNPOW (dfs_step bi order eda offspring_map T) n state)` by (
    last_x_assum
      (qspecl_then [`bi`,`order`,`eda`,`offspring_map`,`state`,`tid`] mp_tac) >>
    simp[]) >>
  simp[] >>
  qspecl_then [`n`,`bi`,`order`,`eda`,`offspring_map`,`state`]
    mp_tac funpow_stack_from_bi >> simp[]
QED

(* Final: schedule output ends with terminator *)
Theorem schedule_terminator_last:
  !bi order eda offspring_map.
    eda_wf eda bi ==>
    eda_topo_compatible bi eda order ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    bi <> [] ==>
    ~is_pseudo (LAST bi).inst_opcode ==>
    (!i. MEM i bi /\ ~is_pseudo i.inst_opcode ==>
         ~MEM (LAST bi).inst_id
           (MAP (\d. d.inst_id) (inst_all_deps bi order eda i))) ==>
    let entries = entry_instructions bi order eda in
    entries <> [] ==>
    LAST entries = LAST bi ==>
    id_not_in_stack (LAST bi).inst_id
      (MAP DfsProcess (FRONT entries)) ==>
    let output = schedule_from_entries bi order eda offspring_map entries in
      output <> [] /\
      (LAST output).inst_id = (LAST bi).inst_id
Proof
  simp[LET_THM, schedule_from_entries_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  (* Initial state has bottom_inv *)
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `final = FUNPOW (dfs_step bi order eda offspring_map T)
    ((LENGTH bi + 1) * (LENGTH bi + 1))
    <| ds_stack := MAP DfsProcess entries;
       ds_output := []; ds_visited := [] |>` >>
  `bottom_inv (LAST bi).inst_id
     <| ds_stack := MAP DfsProcess entries;
        ds_output := []; ds_visited := [] |>` by suspend "init_inv" >>
  (* After FUNPOW steps, bottom_inv still holds *)
  `bottom_inv (LAST bi).inst_id final` by suspend "funpow_inv" >>
  (* Final state has empty stack *)
  `final.ds_stack = []` by suspend "stack_empty" >>
  (* From bottom_inv + empty stack: phase C holds *)
  gvs[bottom_inv_def, id_not_in_stack_def]
QED

Resume schedule_terminator_last[init_inv]:
  simp[bottom_inv_def] >> disj1_tac >>
  qexistsl_tac [`MAP DfsProcess (FRONT entries)`,
                 `LAST entries`] >>
  `entries = FRONT entries ++ [LAST entries]` by
    metis_tac[APPEND_FRONT_LAST] >>
  qpat_x_assum `entries = _` (fn th =>
    rewrite_tac[Once th]) >>
  simp[id_not_in_map_process]
QED

Resume schedule_terminator_last[funpow_inv]:
  qunabbrev_tac `final` >>
  irule funpow_preserves_bottom_inv >> simp[] >>
  rpt strip_tac >>
  `MEM inst entries` by (
    gvs[MEM_MAP] >> Cases_on `y` >> gvs[]) >>
  qunabbrev_tac `entries` >>
  imp_res_tac (SRULE [EVERY_MEM] entry_instructions_mem)
QED

Resume schedule_terminator_last[stack_empty]:
  qunabbrev_tac `final` >> qunabbrev_tac `entries` >>
  qspecl_then [`bi`, `order`, `eda`, `offspring_map`]
    mp_tac schedule_all_visited >>
  simp[LET_THM]
QED

Finalise schedule_terminator_last

(* ================================================================
   Section 3: eda_topo_compatible for original blocks
   ================================================================ *)

(* MEM in block implies MEM in fn_insts_blocks *)
(* fn_inst_ids_distinct + same inst_id in two blocks ==> same block *)
Triviality inst_in_unique_block:
  !bbs bb1 bb2 id.
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
                                      bb.bb_instructions) bbs)) /\
    MEM bb1 bbs /\ MEM bb2 bbs /\
    MEM id (MAP (\i. i.inst_id) bb1.bb_instructions) /\
    MEM id (MAP (\i. i.inst_id) bb2.bb_instructions) ==>
    bb1 = bb2
Proof
  rpt strip_tac >>
  qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
               `bbs`, `bb1`, `bb2`, `id`]
    mp_tac all_distinct_flat_map_unique >>
  simp[]
QED

(* ALL_DISTINCT of FLAT (MAP f l) implies ALL_DISTINCT of f x for MEM x l *)
Triviality all_distinct_flat_map_el:
  !f l x. ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l ==>
           ALL_DISTINCT (f x)
Proof
  gen_tac >> Induct >> simp[] >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem wf_fn_block_inst_ids_distinct:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  drule_all all_distinct_flat_map_el >> simp[]
QED

(* wf_ssa implies defs_before_uses for each block *)
Theorem wf_ssa_defs_before_uses:
  !fn bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    defs_before_uses bb.bb_instructions
Proof
  rw[wf_ssa_def, wf_function_def, defs_before_uses_def] >>
  rpt strip_tac >>
  rename1 `producing_inst _ var = SOME prod` >>
  (* Step 1: prod defines var in bb *)
  drule_all producing_inst_unique >> strip_tac >>
  (* Step 2: def_dominates_uses gives def_bb, def_inst *)
  qpat_x_assum `def_dominates_uses _` mp_tac >>
  simp[def_dominates_uses_def] >>
  disch_then (qspecl_then [`bb`, `EL j bb.bb_instructions`, `var`] mp_tac) >>
  (impl_tac >- simp[EL_MEM]) >>
  strip_tac >>
  (* Step 3: SSA uniqueness: prod = def_inst *)
  `MEM prod (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >> metis_tac[]) >>
  `MEM def_inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >> metis_tac[]) >>
  `prod = def_inst` by metis_tac[ssa_unique_output] >>
  gvs[] >>
  (* Step 4: Same block: def_bb = bb *)
  `def_bb = bb` by (
    qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
                 `fn.fn_blocks`, `def_bb`, `bb`, `def_inst.inst_id`]
      mp_tac all_distinct_flat_map_unique >>
    impl_tac >- (
      gvs[fn_inst_ids_distinct_def] >>
      simp[MEM_MAP] >> metis_tac[]) >>
    simp[]) >>
  gvs[] >>
  (* Step 5: same-block ordering gives i < j' with EL j' bi = EL j bi *)
  first_x_assum (K ALL_TAC) >> (* drop dominance *)
  rename1 `i' < j'` >>
  (* j' = j since inst IDs distinct within block *)
  `j' = j` by (
    `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by (
      qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
                   `fn.fn_blocks`, `bb`]
        mp_tac all_distinct_flat_map_el >>
      gvs[fn_inst_ids_distinct_def]) >>
    `(EL j' bb.bb_instructions).inst_id =
     (EL j bb.bb_instructions).inst_id` by gvs[] >>
    `EL j' (MAP (\i. i.inst_id) bb.bb_instructions) =
     EL j (MAP (\i. i.inst_id) bb.bb_instructions)` by
      gvs[EL_MAP] >>
    metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  qexists `i'` >> gvs[]
QED

(* Data deps from operands point backward (defs_before_uses gives ordering) *)
Triviality operand_dep_backward:
  !bi inst dep v.
    defs_before_uses bi /\
    MEM inst bi /\
    MEM (Var v) inst.inst_operands /\
    producing_inst bi v = SOME dep ==>
    ?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
          EL i bi = dep /\ EL j bi = inst
Proof
  rpt strip_tac >>
  `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
  gvs[defs_before_uses_def] >>
  first_x_assum (qspecl_then [`j`, `v`, `dep`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`i`, `j`] >> simp[]
QED

(* producing_inst result precedes the terminator (last position) *)
Triviality producing_inst_before_terminator:
  !bi v dep.
    bi <> [] /\
    is_terminator (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    producing_inst bi v = SOME dep /\
    ~is_terminator dep.inst_opcode ==>
    ?i. i < PRE (LENGTH bi) /\ EL i bi = dep
Proof
  rpt strip_tac >>
  drule_all producing_inst_unique >> strip_tac >>
  `?i. i < LENGTH bi /\ EL i bi = dep` by metis_tac[MEM_EL] >>
  qexists `i` >> simp[] >>
  spose_not_then assume_tac >>
  `i = PRE (LENGTH bi)` by simp[] >>
  gvs[LAST_EL]
QED

(* ================================================================
   Section 4: EDA deps point backward
   ================================================================ *)

(* compute_effect_deps: et' entries come from inst or old et *)
Triviality compute_effect_deps_et_update:
  !et inst deps et'.
    compute_effect_deps et inst = (deps, et') ==>
    (!eff w. FLOOKUP et'.et_last_write eff = SOME w ==>
       w = inst \/ FLOOKUP et.et_last_write eff = SOME w) /\
    (!eff rs r. FLOOKUP et'.et_all_reads eff = SOME rs /\ MEM r rs ==>
       r = inst \/ ?rs0. FLOOKUP et.et_all_reads eff = SOME rs0 /\ MEM r rs0)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compute_effect_deps_def, LET_THM] >>
  conj_tac
  >- (rpt strip_tac >> fs[read_foldl_last_write] >>
      drule write_foldl_last_write >> simp[])
  >> rpt strip_tac >>
  drule read_foldl_all_reads >> disch_then drule >> strip_tac >> gvs[] >>
  drule write_foldl_all_reads >> strip_tac >> gvs[]
QED

(* compute_effect_deps: all deps come from et entries *)
Triviality compute_effect_deps_from_et:
  !et inst deps et'.
    compute_effect_deps et inst = (deps, et') ==>
    !d. MEM d deps ==>
      (?eff. FLOOKUP et.et_last_write eff = SOME d) \/
      (?eff rs. FLOOKUP et.et_all_reads eff = SOME rs /\ MEM d rs)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compute_effect_deps_def, LET_THM] >>
  rpt strip_tac >>
  gvs[MEM_nub, MEM_APPEND, MEM_FLAT, MEM_MAP, MEM_FILTER,
      optionTheory.IS_SOME_EXISTS, et_get_reads_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

(* FOLDL invariant for build_eda: positional backward property.
   After processing prefix, deps point to earlier prefix elements,
   and et entries are from the prefix. *)
Triviality build_eda_foldl_backward:
  !suffix prefix acc et.
    (* et entries are from prefix *)
    (!eff w. FLOOKUP et.et_last_write eff = SOME w ==>
       ?i. i < LENGTH prefix /\ EL i prefix = w) /\
    (!eff rs r. FLOOKUP et.et_all_reads eff = SOME rs /\ MEM r rs ==>
       ?i. i < LENGTH prefix /\ EL i prefix = r) /\
    (* map deps point to earlier positions in prefix *)
    (!j deps dep. j < LENGTH prefix /\
       FLOOKUP acc (EL j prefix).inst_id = SOME deps /\ MEM dep deps ==>
       ?i. i < j /\ EL i prefix = dep) /\
    (* suffix is the rest of non_phis *)
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ suffix)) ==>
    let result = FST (FOLDL (\(acc_map, et) inst.
      let (deps, et') = compute_effect_deps et inst in
      (acc_map |+ (inst.inst_id, deps), et'))
      (acc, et) suffix) in
    !j deps dep. j < LENGTH (prefix ++ suffix) /\
      FLOOKUP result (EL j (prefix ++ suffix)).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i (prefix ++ suffix) = dep
Proof
  Induct
  (* base case: suffix = [] *)
  >- (rewrite_tac[APPEND_NIL, FOLDL, LET_THM, FST] >>
      rpt strip_tac >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> rename1 `h :: suffix`
  >> Cases_on `compute_effect_deps et h`
  >> rename1 `compute_effect_deps et h = (nd, ne)`
  >> simp[Once FOLDL, LET_THM]
  >> first_x_assum (qspecl_then
       [`prefix ++ [h]`, `acc |+ (h.inst_id, nd)`, `ne`] mp_tac)
  >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >> simp_tac std_ss [LENGTH_APPEND, LENGTH, ADD_CLAUSES]
  >> impl_tac
  >- (rpt conj_tac
      (* 1: et_last_write entries from prefix ++ [h] *)
      >- (rpt strip_tac >>
          drule_all compute_effect_deps_et_update >> strip_tac >>
          first_x_assum drule >> strip_tac
          >- (qexists `LENGTH prefix` >>
              simp[EL_APPEND2, EL_APPEND1])
          >> first_x_assum drule >> strip_tac >>
          qexists `i` >> simp[EL_APPEND1])
      (* 2: et_all_reads entries from prefix ++ [h] *)
      >- (rpt strip_tac >>
          drule_all compute_effect_deps_et_update >> strip_tac >>
          first_x_assum drule >> disch_then drule >> strip_tac
          >- (qexists `LENGTH prefix` >>
              simp[EL_APPEND2, EL_APPEND1])
          >> first_x_assum (qspecl_then [`eff`, `rs0`, `r`] mp_tac) >>
          simp[] >> strip_tac >>
          qexists `i` >> simp[EL_APPEND1])
      (* 3: map deps backward for prefix ++ [h] *)
      >- (rpt strip_tac >>
          Cases_on `j < LENGTH prefix`
          >- (fs[EL_APPEND1, FLOOKUP_UPDATE] >>
              `(EL j prefix).inst_id <> h.inst_id` by (
                spose_not_then assume_tac >>
                qpat_x_assum `ALL_DISTINCT _` mp_tac >>
                simp[MAP_APPEND, ALL_DISTINCT_APPEND, MEM_MAP] >>
                metis_tac[MEM_EL]) >>
              fs[] >> first_x_assum drule_all >> strip_tac >>
              qexists `i` >> simp[EL_APPEND1])
          >> `j = LENGTH prefix` by (
               `j < LENGTH prefix + 1` by fs[] >> simp[]) >>
          fs[EL_APPEND2, FLOOKUP_UPDATE] >>
          drule compute_effect_deps_from_et >>
          disch_then (qspec_then `dep` mp_tac) >> simp[] >>
          strip_tac
          >- (first_x_assum drule >> strip_tac >>
              qexists `i` >> simp[EL_APPEND1])
          >> first_x_assum (qspecl_then [`eff`, `rs`, `dep`] mp_tac) >>
          simp[] >> strip_tac >>
          qexists `i` >> simp[EL_APPEND1])
      (* 4: ALL_DISTINCT *)
      >> simp[])
  >> simp[]
QED

(* build_eda satisfies backward property on non_phis *)
Triviality build_eda_backward:
  !bi.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (build_eda bi) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM, build_eda_def] >> rpt strip_tac >>
  qspecl_then
    [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `[]`,
     `FEMPTY`, `empty_effect_track`]
    mp_tac build_eda_foldl_backward >>
  rewrite_tac[APPEND_NIL, LET_THM] >>
  simp[empty_effect_track_def, FLOOKUP_DEF] >>
  disch_then match_mp_tac >>
  fs[empty_effect_track_def, FLOOKUP_DEF]
QED

(* FILTER preserves relative order: if i < j in FILTER P l,
   the corresponding positions in l also satisfy i' < j'. *)
Triviality filter_el_mono:
  !P (l:'a list) i j. i < j /\ j < LENGTH (FILTER P l) ==>
    ?i' j'. i' < j' /\ j' < LENGTH l /\
            EL i' l = EL i (FILTER P l) /\ EL j' l = EL j (FILTER P l)
Proof
  gen_tac >> Induct >- simp[] >>
  rw[FILTER] >> rename1 `h :: t` >>
  Cases_on `P h` >> gvs[]
  >- ((* P h: FILTER = h :: FILTER P t *)
    Cases_on `i` >> gvs[]
    >- suspend "case_zero"
    >- suspend "case_suc")
  >> suspend "case_not_P"
QED

Resume filter_el_mono[case_zero]:
  `j - 1 < LENGTH (FILTER P t)` by
    (Cases_on `j` >> gvs[]) >>
  `MEM (EL (j - 1) (FILTER P t)) t` by
    (imp_res_tac EL_MEM >> fs[MEM_FILTER]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `n < LENGTH t` >>
  qexistsl [`0`, `n + 1`] >>
  Cases_on `j` >> gvs[EL_CONS, PRE_SUB1]
QED

Resume filter_el_mono[case_suc]:
  rename1 `SUC i' < j` >>
  first_x_assum (qspecl_then [`i'`, `j - 1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  rename [`i_t < j_t`, `j_t < LENGTH t`] >>
  qexistsl [`i_t + 1`, `j_t + 1`] >>
  simp[] >> Cases_on `j` >> gvs[EL_CONS, PRE_SUB1]
QED

Resume filter_el_mono[case_not_P]:
  first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[] >>
  strip_tac >>
  rename [`i_t < j_t`, `j_t < LENGTH t`] >>
  qexistsl [`i_t + 1`, `j_t + 1`] >> simp[GSYM ADD1]
QED

Finalise filter_el_mono

(* If p is in the prefix and h follows it in FILTER P non_phis,
   then p appears before h in non_phis (by filter_el_mono). *)
Triviality filter_last_prefix_before:
  !P non_phis prefix h suffix j.
    prefix ++ h :: suffix = FILTER P non_phis /\
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    prefix <> [] /\
    j < LENGTH non_phis /\
    (EL j non_phis).inst_id = h.inst_id ==>
    ?i. i < j /\ EL i non_phis = LAST prefix
Proof
  rpt strip_tac >>
  (* LAST prefix is at index PRE(LENGTH prefix) in prefix *)
  `?k. k < LENGTH prefix /\ EL k prefix = LAST prefix` by
    (qexists `PRE (LENGTH prefix)` >> Cases_on `prefix` >> gvs[LAST_EL]) >>
  (* Translate to indices in FILTER P non_phis *)
  `EL k (FILTER P non_phis) = LAST prefix` by
    (`EL k (prefix ++ h :: suffix) = EL k prefix` by simp[EL_APPEND1] >>
     metis_tac[]) >>
  `EL (LENGTH prefix) (FILTER P non_phis) = h` by
    (qpat_x_assum `_ = FILTER P non_phis` (SUBST1_TAC o SYM) >>
     simp[EL_APPEND2]) >>
  `LENGTH prefix < LENGTH (FILTER P non_phis)` by
    (`LENGTH (FILTER P non_phis) = LENGTH prefix + SUC (LENGTH suffix)`
       by metis_tac[LENGTH_APPEND, LENGTH] >> simp[]) >>
  (* filter_el_mono: k < LENGTH prefix → ∃i' j'. i' < j' in non_phis *)
  qspecl_then [`P`, `non_phis`, `k`, `LENGTH prefix`]
    mp_tac filter_el_mono >> simp[] >> strip_tac >>
  (* j' indexes h in non_phis; j = j' by ALL_DISTINCT *)
  `j = j'` by (
    `EL j (MAP (\i. i.inst_id) non_phis) =
     EL j' (MAP (\i. i.inst_id) non_phis)` by simp[EL_MAP] >>
    metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  qexists `i'` >> simp[]
QED

(* FOLDL invariant for add_chain_deps.
   matching = prefix ++ suffix (already processed ++ remaining).
   prev = LAST_OPTION prefix.
   All deps in acc point backward in non_phis. *)
(* Helper: one step of add_chain_deps preserves backward property.
   new_acc updates acc at h.inst_id with possibly LAST prefix prepended. *)
Triviality chain_dep_update_backward:
  !prefix h suffix non_phis acc.
    prefix ++ h :: suffix = FILTER P non_phis /\
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP acc (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) ==>
    let old_deps = case FLOOKUP acc h.inst_id of NONE => [] | SOME ds => ds;
        prev = if prefix = [] then NONE else SOME (LAST prefix);
        new_deps = case prev of
                     NONE => old_deps
                   | SOME p => if MEM p old_deps then old_deps
                               else p :: old_deps;
        new_acc = acc |+ (h.inst_id, new_deps)
    in
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP new_acc (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt strip_tac
  >> simp_tac std_ss [LET_THM]
  >> rpt strip_tac
  >> Cases_on `(EL j non_phis).inst_id = h.inst_id`
  >- (gvs[FLOOKUP_UPDATE] >>
      Cases_on `prefix = []` >> gvs[] >>
      Cases_on `FLOOKUP acc h.inst_id` >> gvs[] >>
      suspend "hit")
  >> gvs[FLOOKUP_UPDATE]
QED

Resume chain_dep_update_backward[hit]:
  markerLib.RESUME_TAC
  >> rpt strip_tac
  >> qpat_x_assum `_ = FILTER P _` mp_tac
  >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >> strip_tac
  (* Subgoal 1 (NONE): dep = LAST prefix *)
  >> TRY (irule filter_last_prefix_before >> metis_tac[] >> NO_TAC)
  (* Subgoal 2 (SOME x): case split on MEM in the if-then-else *)
  >> Cases_on `MEM (LAST prefix) x` >> gvs[]
  (* ¬MEM case remains; gvs mangled FILTER asm, recover h::suffix form *)
  >> qpat_x_assum `_ = FILTER P _` mp_tac
  >> rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac
  >> irule filter_last_prefix_before >> metis_tac[]
QED

Finalise chain_dep_update_backward

Triviality add_chain_deps_foldl_backward:
  !suffix prefix acc prev non_phis.
    (prefix ++ suffix = FILTER P non_phis) /\
    (prev = if prefix = [] then NONE else SOME (LAST prefix)) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP acc (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) ==>
    let result = FST (FOLDL
      (\(acc,prev) inst.
        let old_deps =
              case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds;
            new_deps =
              case prev of
                NONE => old_deps
              | SOME p => if MEM p old_deps then old_deps
                          else p::old_deps
        in (acc |+ (inst.inst_id, new_deps), SOME inst))
      (acc, prev) suffix) in
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP result (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  Induct
  >- (rewrite_tac[APPEND_NIL, FOLDL, LET_THM, FST] >>
      rpt strip_tac >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> rename1 `h :: suffix`
  >> simp[Once FOLDL, LET_THM]
  >> qmatch_goalsub_abbrev_tac `FOLDL _ (new_acc, SOME h) suffix`
  >> first_x_assum (qspecl_then
       [`prefix ++ [h]`, `new_acc`, `SOME h`, `non_phis`] mp_tac)
  >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >> simp[LAST_APPEND_CONS]
  >> impl_tac
  >- suspend "foldl_step"
  >> simp[]
QED

Resume add_chain_deps_foldl_backward[foldl_step]:
  conj_tac
  >- (qpat_x_assum `_ = FILTER P _` mp_tac >>
      rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[])
  >> simp[Abbr `new_acc`]
  >> match_mp_tac (SIMP_RULE std_ss [LET_THM] chain_dep_update_backward)
  >> metis_tac[]
QED

Finalise add_chain_deps_foldl_backward

(* add_chain_deps preserves backward property. *)
Triviality add_chain_deps_backward:
  !P bi eda.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP eda (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (add_chain_deps P bi eda) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM, add_chain_deps_def] >> rpt strip_tac >>
  qspecl_then
    [`FILTER P (FILTER (\i. ~is_pseudo i.inst_opcode) bi)`, `[]`,
     `eda`, `NONE`, `FILTER (\i. ~is_pseudo i.inst_opcode) bi`]
    mp_tac add_chain_deps_foldl_backward >>
  rewrite_tac[APPEND_NIL, LET_THM] >>
  simp[] >> disch_then drule_all >> simp[]
QED

(* Helper: updating acc at h preserves the backward property *)
Triviality barrier_dep_update_backward:
  !prefix h suffix last_bar acc.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ h :: suffix)) /\
    ~is_barrier h /\
    (!b. last_bar = SOME b ==>
       ?k. k < LENGTH prefix /\ EL k (prefix ++ h :: suffix) = b) /\
    (!j deps dep. j < LENGTH (prefix ++ h :: suffix) /\
       FLOOKUP acc (EL j (prefix ++ h :: suffix)).inst_id = SOME deps /\
       MEM dep deps ==> ?i. i < j /\ EL i (prefix ++ h :: suffix) = dep)
    ==>
    let old_deps = case FLOOKUP acc h.inst_id of NONE => [] | SOME ds => ds;
        new_deps = case last_bar of
                     NONE => old_deps
                   | SOME b => if MEM b old_deps then old_deps
                               else b :: old_deps;
        new_acc = acc |+ (h.inst_id, new_deps)
    in
    !j deps dep. j < LENGTH (prefix ++ h :: suffix) /\
      FLOOKUP new_acc (EL j (prefix ++ h :: suffix)).inst_id = SOME deps /\
      MEM dep deps ==> ?i. i < j /\ EL i (prefix ++ h :: suffix) = dep
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  Cases_on `(EL j (prefix ++ h :: suffix)).inst_id = h.inst_id`
  >- suspend "h_case"
  >> suspend "other_case"
QED

Resume barrier_dep_update_backward[other_case]:
  gvs[FLOOKUP_UPDATE] >>
  first_x_assum (qspecl_then [`j`, `deps`, `dep`] mp_tac) >> simp[]
QED

Resume barrier_dep_update_backward[h_case]:
  `j = LENGTH prefix` by (
    qspecl_then [`MAP (\i. i.inst_id) (prefix ++ h :: suffix)`,
                 `j`, `LENGTH prefix`] mp_tac ALL_DISTINCT_EL_IMP >>
    simp[EL_MAP, EL_LENGTH_APPEND_0] >> strip_tac >>
    first_x_assum irule >> fs[]) >>
  gvs[FLOOKUP_UPDATE, EL_APPEND2] >>
  Cases_on `last_bar` >> Cases_on `FLOOKUP acc h.inst_id`
  >- suspend "none_none"
  >- suspend "none_some"
  >- suspend "some_none"
  >> suspend "some_some"
QED

Resume barrier_dep_update_backward[none_none]:
  gvs[]
QED

Resume barrier_dep_update_backward[none_some]:
  gvs[] >> rename1 `FLOOKUP acc h.inst_id = SOME old_ds` >>
  first_x_assum (qspecl_then [`LENGTH prefix`, `old_ds`, `dep`] mp_tac) >>
  simp[EL_APPEND2]
QED

Resume barrier_dep_update_backward[some_none]:
  gvs[] >> qexists `k` >> simp[]
QED

Resume barrier_dep_update_backward[some_some]:
  gvs[] >> rename1 `FLOOKUP acc h.inst_id = SOME old_ds` >>
  Cases_on `MEM dep old_ds`
  >- (first_x_assum (qspecl_then [`LENGTH prefix`, `old_ds`, `dep`] mp_tac) >>
      simp[EL_APPEND2])
  >> qpat_x_assum `MEM dep (if _ then _ else _)` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  qexists `k` >> gvs[]
QED

Finalise barrier_dep_update_backward

(* add_deps_on_barrier backward: all added deps point backward.
   Helper: FOLDL induction on suffix of non_phis. *)
Triviality add_deps_on_barrier_foldl_backward:
  !suffix prefix nps last_bar acc.
    nps = prefix ++ suffix /\
    ALL_DISTINCT (MAP (\i. i.inst_id) nps) /\
    (!b. last_bar = SOME b ==>
       ?k. k < LENGTH prefix /\ EL k nps = b) /\
    (!j deps dep. j < LENGTH nps /\
       FLOOKUP acc (EL j nps).inst_id = SOME deps /\
       MEM dep deps ==> ?i. i < j /\ EL i nps = dep) ==>
    !j deps dep. j < LENGTH nps /\
      FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
        if is_barrier inst then (acc, SOME inst)
        else
          (acc |+ (inst.inst_id,
             case last_bar of
               NONE => (case FLOOKUP acc inst.inst_id of
                          NONE => [] | SOME ds => ds)
             | SOME b =>
                 if MEM b (case FLOOKUP acc inst.inst_id of
                             NONE => [] | SOME ds => ds)
                 then (case FLOOKUP acc inst.inst_id of
                         NONE => [] | SOME ds => ds)
                 else b :: (case FLOOKUP acc inst.inst_id of
                              NONE => [] | SOME ds => ds)),
           last_bar))
      (acc, last_bar) suffix)) (EL j nps).inst_id = SOME deps /\
      MEM dep deps ==> ?i. i < j /\ EL i nps = dep
Proof
  Induct
  >- (rewrite_tac[FOLDL, FST] >> rpt strip_tac >> metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  rename1 `h :: suffix'` >>
  simp[Once FOLDL] >>
  Cases_on `is_barrier h`
  >- suspend "barrier"
  >> suspend "non_barrier"
QED

Resume add_deps_on_barrier_foldl_backward[barrier]:
  (* Barrier case: acc unchanged, last_bar becomes SOME h *)
  simp[] >>
  first_x_assum (qspecl_then [`prefix ++ [h]`, `prefix ++ h :: suffix'`,
                              `SOME h`, `acc`] mp_tac) >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  impl_tac
  >- (qpat_x_assum `nps = _` SUBST_ALL_TAC >>
      rpt conj_tac >> simp[]
      >- (rpt strip_tac >>
          qexists `LENGTH prefix` >> simp[EL_APPEND2, EL_APPEND1]))
  >> simp[]
QED

Resume add_deps_on_barrier_foldl_backward[non_barrier]:
  simp[] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ (new_acc, last_bar) suffix'` >>
  first_x_assum (qspecl_then [`prefix ++ [h]`, `prefix ++ h :: suffix'`,
                              `last_bar`, `new_acc`] mp_tac) >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  impl_tac
  >- suspend "nb_impl"
  >> simp[]
QED

Resume add_deps_on_barrier_foldl_backward[nb_impl]:
  qpat_x_assum `nps = _` SUBST_ALL_TAC >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexists `k` >> simp[])
  >> simp[Abbr `new_acc`] >>
  rpt strip_tac >>
  irule (SRULE [LET_THM] (SIMP_RULE (srw_ss()) [] barrier_dep_update_backward)) >>
  fs[MAP_APPEND, MAP] >>
  qexistsl [`acc`, `deps`, `last_bar`] >> simp[]
QED

Finalise add_deps_on_barrier_foldl_backward

Triviality add_deps_on_barrier_backward:
  !bi eda.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP eda (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (add_deps_on_barrier bi eda) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM, add_deps_on_barrier_def] >> rpt strip_tac >>
  irule add_deps_on_barrier_foldl_backward >>
  simp[] >>
  qexistsl [`eda`, `deps`, `NONE`,
            `[]`, `FILTER (\i. ~is_pseudo i.inst_opcode) bi`] >>
  simp[]
QED

Triviality foldl_add_mem:
  !prev init x.
    MEM x (FOLDL (\ds (p:instruction). if MEM p ds then ds else p :: ds)
             init prev) ==>
    MEM x init \/ MEM x prev
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `MEM h init` >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* FOLDL lemma for add_deps_from_barrier backward property *)
Triviality add_deps_from_barrier_foldl_backward:
  !to_process prefix nps prev_insts acc.
    nps = prefix ++ to_process /\
    ALL_DISTINCT (MAP (\i. i.inst_id) nps) /\
    (!p. MEM p prev_insts ==>
       ?k. k < LENGTH prefix /\ EL k nps = p) /\
    (!j' deps' dep'. j' < LENGTH nps /\
       FLOOKUP acc (EL j' nps).inst_id = SOME deps' /\
       MEM dep' deps' ==> ?i'. i' < j' /\ EL i' nps = dep') ==>
    !j' deps' dep'. j' < LENGTH nps /\
      FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
        if is_barrier inst then
          let old_deps = case FLOOKUP acc inst.inst_id of
                           NONE => [] | SOME ds => ds in
          let new_deps = FOLDL (\ds p.
                if MEM p ds then ds else p :: ds) old_deps prev_insts in
          (acc |+ (inst.inst_id, new_deps), prev_insts ++ [inst])
        else
          (acc, prev_insts ++ [inst]))
      (acc, prev_insts) to_process)) (EL j' nps).inst_id = SOME deps' /\
      MEM dep' deps' ==> ?i'. i' < j' /\ EL i' nps = dep'
Proof
  Induct
  >- (rewrite_tac[APPEND_NIL, FOLDL, LET_THM, FST] >>
      rpt strip_tac >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> rename1 `h :: to_process`
  >> Cases_on `is_barrier h`
  (* Barrier case *)
  >- (simp[Once FOLDL, LET_THM] >>
      qmatch_goalsub_abbrev_tac `FOLDL _ (new_acc, new_prev) to_process` >>
      first_x_assum (qspecl_then
           [`prefix ++ [h]`, `nps`, `new_prev`, `new_acc`] mp_tac) >>
      rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[] >>
      (impl_tac >- suspend "barrier_step") >>
      simp[])
  (* Non-barrier case *)
  >> (simp[Once FOLDL, LET_THM] >>
      qmatch_goalsub_abbrev_tac `FOLDL _ (new_acc, new_prev) to_process` >>
      first_x_assum (qspecl_then
           [`prefix ++ [h]`, `nps`, `new_prev`, `new_acc`] mp_tac) >>
      rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[] >>
      (impl_tac >- suspend "non_barrier_step") >>
      simp[])
QED

Resume add_deps_from_barrier_foldl_backward[non_barrier_step]:
  simp[Abbr `new_prev`, Abbr `new_acc`] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (qpat_x_assum `!q. MEM q prev_insts ==> _`
        (qspec_then `p` mp_tac) >>
      simp[] >> strip_tac >> qexists `k` >> simp[])
  >> (gvs[] >> qexists `LENGTH prefix` >> simp[EL_LENGTH_APPEND])
QED

Resume add_deps_from_barrier_foldl_backward[barrier_step]:
  simp[Abbr `new_prev`, Abbr `new_acc`, LET_THM] >>
  conj_tac
  (* MEM conjunct — same pattern as non-barrier *)
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `_ \/ _` strip_assume_tac
      >- (qpat_x_assum `!q. MEM q prev_insts ==> _`
            (qspec_then `p` mp_tac) >>
          simp[] >> strip_tac >> qexists `k` >> simp[])
      >> (gvs[] >> qexists `LENGTH prefix` >> simp[EL_LENGTH_APPEND]))
  (* FLOOKUP conjunct *)
  >> suspend "flookup_conj"
QED

Resume add_deps_from_barrier_foldl_backward[flookup_conj]:
  rpt gen_tac >> strip_tac >>
  Cases_on `(EL j' (prefix ++ h::to_process)).inst_id = h.inst_id`
  >- (
    `j' = LENGTH prefix` by (
      gvs[] >>
      qspecl_then [`MAP (\i. i.inst_id) (prefix ++ h::to_process)`,
                   `j'`, `LENGTH prefix`] mp_tac ALL_DISTINCT_EL_IMP >>
      (impl_tac >- (
        RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
        simp[MAP_APPEND, MAP]
      )) >>
      simp[EL_MAP, EL_APPEND2]
    ) >>
    gvs[FLOOKUP_UPDATE] >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
    Cases_on `FLOOKUP acc h.inst_id` >> gvs[] >>
    drule foldl_add_mem >> disch_then strip_assume_tac >> gvs[] >>
    first_x_assum drule >> strip_tac >> qexists `k` >> simp[]
  )
  >> (
    gvs[FLOOKUP_UPDATE] >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
    first_x_assum (qspecl_then [`j'`, `deps'`, `dep'`] mp_tac) >> simp[]
  )
QED

Finalise add_deps_from_barrier_foldl_backward

(* add_deps_from_barrier backward: all added deps point backward *)
Triviality add_deps_from_barrier_backward:
  !bi eda.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP eda (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (add_deps_from_barrier bi eda) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM, add_deps_from_barrier_def] >> rpt strip_tac >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  qspecl_then [`nps`, `[]`, `nps`, `[]`, `eda`] mp_tac
    add_deps_from_barrier_foldl_backward >>
  simp[]
QED

(* add_barrier_deps backward *)
Triviality add_barrier_deps_backward:
  !bi eda.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) /\
    (!j deps dep. j < LENGTH non_phis /\
       FLOOKUP eda (EL j non_phis).inst_id = SOME deps /\
       MEM dep deps ==>
       ?i. i < j /\ EL i non_phis = dep) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (add_barrier_deps bi eda) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM, add_barrier_deps_def] >> rpt strip_tac >>
  irule (SRULE [LET_THM] add_deps_from_barrier_backward) >>
  simp[] >>
  qexistsl [`deps`, `add_deps_on_barrier bi eda`] >>
  simp[] >>
  MATCH_MP_TAC (SRULE [LET_THM] add_deps_on_barrier_backward) >>
  simp[]
QED

(* build_full_eda backward property *)
Triviality build_full_eda_backward:
  !bi.
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) bi in
    ALL_DISTINCT (MAP (\i. i.inst_id) non_phis) ==>
    !j deps dep. j < LENGTH non_phis /\
      FLOOKUP (build_full_eda bi) (EL j non_phis).inst_id = SOME deps /\
      MEM dep deps ==>
      ?i. i < j /\ EL i non_phis = dep
Proof
  rpt gen_tac >> simp[LET_THM] >> rpt strip_tac >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  (* Step 1: build_eda satisfies backward *)
  `!j deps dep. j < LENGTH nps /\
     FLOOKUP (build_eda bi) (EL j nps).inst_id = SOME deps /\
     MEM dep deps ==> ?i. i < j /\ EL i nps = dep` by
    (mp_tac (SRULE [LET_THM] build_eda_backward) >>
     disch_then (qspec_then `bi` mp_tac) >>
     simp[Abbr `nps`]) >>
  (* Step 2: add_abort_deps preserves backward *)
  `!j deps dep. j < LENGTH nps /\
     FLOOKUP (add_abort_deps bi (build_eda bi)) (EL j nps).inst_id = SOME deps /\
     MEM dep deps ==> ?i. i < j /\ EL i nps = dep` by
    (rewrite_tac[add_abort_deps_def] >>
     mp_tac (SRULE [LET_THM] add_chain_deps_backward) >>
     disch_then (qspecl_then
       [`\i. opcode_fail_class i.inst_opcode <> NoFail`, `bi`, `build_eda bi`] mp_tac) >>
     simp[Abbr `nps`]) >>
  (* Step 3: add_barrier_deps preserves backward *)
  `!j deps dep. j < LENGTH nps /\
     FLOOKUP (add_barrier_deps bi (add_abort_deps bi (build_eda bi)))
       (EL j nps).inst_id = SOME deps /\
     MEM dep deps ==> ?i. i < j /\ EL i nps = dep` by
    (mp_tac (SRULE [LET_THM] add_barrier_deps_backward) >>
     disch_then (qspecl_then [`bi`, `add_abort_deps bi (build_eda bi)`] mp_tac) >>
     simp[Abbr `nps`]) >>
  (* Step 4: add_alloca_deps preserves backward *)
  `!j deps dep. j < LENGTH nps /\
     FLOOKUP (build_full_eda bi) (EL j nps).inst_id = SOME deps /\
     MEM dep deps ==> ?i. i < j /\ EL i nps = dep` by
    (rewrite_tac[build_full_eda_def, add_alloca_deps_def] >>
     mp_tac (SRULE [LET_THM] add_chain_deps_backward) >>
     disch_then (qspecl_then
       [`\i. is_alloca_op i.inst_opcode`, `bi`,
        `add_barrier_deps bi (add_abort_deps bi (build_eda bi))`] mp_tac) >>
     simp[Abbr `nps`]) >>
  metis_tac[]
QED


(* EDA deps (from build_full_eda) point backward *)
Theorem eda_deps_backward:
  !bi inst dep deps.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    FLOOKUP (build_full_eda bi) inst.inst_id = SOME deps /\
    MEM dep deps /\ ~is_pseudo dep.inst_opcode ==>
    ?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
          EL i bi = dep /\ EL j bi = inst
Proof
  rpt strip_tac >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  (* inst is in non_phis *)
  `MEM inst nps` by simp[Abbr `nps`, MEM_FILTER] >>
  `?j_nps. j_nps < LENGTH nps /\ EL j_nps nps = inst` by
    metis_tac[MEM_EL] >>
  (* ALL_DISTINCT inst_ids for non_phis *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) nps)` by
    (simp[Abbr `nps`] >> irule all_distinct_map_filter >> simp[]) >>
  (* Apply build_full_eda_backward: dep at earlier position in nps *)
  mp_tac (SRULE [LET_THM] build_full_eda_backward) >>
  disch_then (qspec_then `bi` mp_tac) >>
  simp[Abbr `nps`] >> strip_tac >>
  first_x_assum (qspecl_then [`j_nps`, `deps`, `dep`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `i_nps < j_nps` >>
  (* Lift positions from nps to bi using filter_el_mono *)
  qspecl_then [`\i. ~is_pseudo i.inst_opcode`, `bi`, `i_nps`, `j_nps`]
    mp_tac filter_el_mono >>
  simp[] >> strip_tac >>
  qexistsl [`i'`, `j'`] >> simp[]
QED

(* Generalized: eda_topo_compatible from block properties alone.
   No dependency on fn or MEM bb fn.fn_blocks. *)
Theorem eda_topo_compatible_gen:
  !bi order.
    bi <> [] /\
    is_terminator (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    defs_before_uses bi ==>
    eda_topo_compatible bi (build_full_eda bi) order
Proof
  rpt strip_tac >>
  simp[eda_topo_compatible_def, inst_all_deps_def, LET_THM] >>
  rpt strip_tac >>
  gvs[MEM_nub, MEM_APPEND]
  (* data deps case *)
  >- (fs[inst_data_deps_def, LET_THM, MEM_nub] >>
      gvs[MEM_APPEND, MEM_MAP, MEM_FILTER]
      >- ((* var_deps case *)
        rename1 `MEM op inst.inst_operands` >>
        Cases_on `op` >> gvs[operand_producer_def] >>
        rename1 `producing_inst bi v` >>
        Cases_on `producing_inst bi v` >> gvs[] >>
        irule operand_dep_backward >>
        metis_tac[])
      >> (* order_deps case *)
      Cases_on `is_terminator inst.inst_opcode` >> gvs[MEM_FILTER, MEM_MAP] >>
      rename1 `IS_SOME (producing_inst bi w)` >>
      Cases_on `producing_inst bi w` >> gvs[] >>
      rename1 `producing_inst bi w = SOME dep` >>
      `~is_terminator dep.inst_opcode` by (
        spose_not_then assume_tac >>
        drule_all producing_inst_unique >> strip_tac >>
        `?k. k < LENGTH bi /\ EL k bi = dep` by metis_tac[MEM_EL] >>
        `k = PRE (LENGTH bi)` by metis_tac[] >>
        `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
        `j = PRE (LENGTH bi)` by metis_tac[] >>
        gvs[]) >>
      drule_all producing_inst_before_terminator >> strip_tac >>
      `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
      `j = PRE (LENGTH bi)` by metis_tac[] >>
      qexistsl [`i`, `j`] >> simp[])
  (* eda deps case *)
  >> (Cases_on `FLOOKUP (build_full_eda bi) inst.inst_id` >> gvs[] >>
      irule eda_deps_backward >> metis_tac[])
QED

(* Weaker: defs_before_uses only for non-pseudo users.
   Sufficient for eda_topo_compatible because it only quantifies
   over non-pseudo instructions. *)
(* non_pseudo_defs_before_uses = np_defs_before_uses from dftTopoSort *)
(* TODO: pure alias for np_defs_before_uses — consider using
   np_defs_before_uses directly and removing this indirection *)
Definition non_pseudo_defs_before_uses_def:
  non_pseudo_defs_before_uses = np_defs_before_uses
End

Triviality defs_before_implies_non_pseudo:
  !insts. defs_before_uses insts ==> non_pseudo_defs_before_uses insts
Proof
  rw[non_pseudo_defs_before_uses_def, defs_before_uses_def,
     np_defs_before_uses_def] >> metis_tac[]
QED

Triviality operand_dep_backward_weak:
  !bi inst dep v.
    non_pseudo_defs_before_uses bi /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\
    producing_inst bi v = SOME dep ==>
    ?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
          EL i bi = dep /\ EL j bi = inst
Proof
  rpt strip_tac >>
  `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
  gvs[non_pseudo_defs_before_uses_def, np_defs_before_uses_def] >>
  first_x_assum (qspecl_then [`j`, `v`, `dep`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`i`, `j`] >> simp[]
QED

(* eda_topo_compatible from non_pseudo_defs_before_uses
   — identical proof to eda_topo_compatible_gen but weaker hypothesis *)
Theorem eda_topo_compatible_gen_weak:
  !bi order.
    bi <> [] /\
    is_terminator (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    non_pseudo_defs_before_uses bi ==>
    eda_topo_compatible bi (build_full_eda bi) order
Proof
  rpt strip_tac >>
  simp[eda_topo_compatible_def, inst_all_deps_def, LET_THM] >>
  rpt strip_tac >>
  gvs[MEM_nub, MEM_APPEND]
  (* data deps case *)
  >- (fs[inst_data_deps_def, LET_THM, MEM_nub] >>
      gvs[MEM_APPEND, MEM_MAP, MEM_FILTER]
      >- ((* var_deps case *)
        rename1 `MEM op inst.inst_operands` >>
        Cases_on `op` >> gvs[operand_producer_def] >>
        rename1 `producing_inst bi v` >>
        Cases_on `producing_inst bi v` >> gvs[] >>
        irule operand_dep_backward_weak >>
        metis_tac[])
      >> (* order_deps case *)
      Cases_on `is_terminator inst.inst_opcode` >> gvs[MEM_FILTER, MEM_MAP] >>
      rename1 `IS_SOME (producing_inst bi w)` >>
      Cases_on `producing_inst bi w` >> gvs[] >>
      rename1 `producing_inst bi w = SOME dep` >>
      `~is_terminator dep.inst_opcode` by (
        spose_not_then assume_tac >>
        drule_all producing_inst_unique >> strip_tac >>
        `?k. k < LENGTH bi /\ EL k bi = dep` by metis_tac[MEM_EL] >>
        `k = PRE (LENGTH bi)` by metis_tac[] >>
        `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
        `j = PRE (LENGTH bi)` by metis_tac[] >>
        gvs[]) >>
      drule_all producing_inst_before_terminator >> strip_tac >>
      `?j. j < LENGTH bi /\ EL j bi = inst` by metis_tac[MEM_EL] >>
      `j = PRE (LENGTH bi)` by metis_tac[] >>
      qexistsl [`i`, `j`] >> simp[])
  (* eda deps case *)
  >> (Cases_on `FLOOKUP (build_full_eda bi) inst.inst_id` >> gvs[] >>
      irule eda_deps_backward >> metis_tac[])
QED

(* Combined: eda_topo_compatible for original block — corollary of gen *)
Theorem eda_topo_compatible_original:
  !fn bb order.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    eda_topo_compatible bb.bb_instructions
      (build_full_eda bb.bb_instructions) order
Proof
  rpt strip_tac >>
  irule eda_topo_compatible_gen >>
  `bb_well_formed bb` by (gvs[wf_function_def, EVERY_MEM]) >>
  gvs[bb_well_formed_def] >>
  conj_tac >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[]) >>
  irule wf_ssa_defs_before_uses >> metis_tac[]
QED


