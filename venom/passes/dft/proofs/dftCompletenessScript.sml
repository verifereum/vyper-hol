(*
 * DFT DFS Completeness
 *
 * Key result:
 *   schedule_output_complete — all non-pseudo ids are in schedule output
 *
 * Strategy: measure = stack_size + unvisited * (n+1) strictly decreases
 *   at each non-idle step. After budget = (n+1)^2 steps, measure = 0,
 *   meaning stack empty + all non-pseudos visited. Combined with
 *   dfs_topo_inv (visited + not pending -> in output), completeness follows.
 *)

Theory dftCompleteness
Ancestors
  dftTopoSort dftScheduleFixed dftStructural dftDefs
  venomInst
  list rich_list sorting
  finite_map pred_set pair arithmetic
  combin option
Libs
  BasicProvers markerLib

(* ===== ds_visited only grows ===== *)

Triviality dfs_step_visited_mono:
  !bi order eda om fl state id.
    MEM id state.ds_visited ==>
    MEM id (dfs_step bi order eda om fl state).ds_visited
Proof
  rpt strip_tac >>
  simp[dfs_step_def] >>
  EVERY_CASE_TAC >> gvs[LET_THM]
QED

Triviality funpow_visited_mono:
  !n bi order eda om fl state id.
    MEM id state.ds_visited ==>
    MEM id (FUNPOW (dfs_step bi order eda om fl) n state).ds_visited
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> irule dfs_step_visited_mono >> simp[]
QED

(* ===== dfs_step visits the top DfsProcess ===== *)

Triviality dfs_step_visits_top_process:
  !bi order eda om fl state inst rest.
    state.ds_stack = DfsProcess inst :: rest ==>
    MEM inst.inst_id (dfs_step bi order eda om fl state).ds_visited
Proof
  rpt strip_tac >>
  simp[dfs_step_def] >>
  Cases_on `MEM inst.inst_id state.ds_visited` >> simp[] >>
  Cases_on `is_pseudo inst.inst_opcode` >> simp[] >>
  simp[LET_THM]
QED

(* ===== When visiting a non-pseudo, children are pushed ===== *)

Triviality dfs_step_pushes_children:
  !bi order eda om fl state inst rest.
    state.ds_stack = DfsProcess inst :: rest /\
    ~MEM inst.inst_id state.ds_visited /\
    ~is_pseudo inst.inst_opcode ==>
    !dep. MEM dep (inst_all_deps bi order eda inst) ==>
          MEM (DfsProcess dep)
            (dfs_step bi order eda om fl state).ds_stack
Proof
  rpt strip_tac >>
  simp[dfs_step_def, LET_THM, MEM_APPEND, MEM_MAP] >>
  disj1_tac >> metis_tac[sort_children_mem]
QED

(* ===== Count of unvisited non-pseudos ===== *)

Definition unvisited_count_def:
  unvisited_count bi visited =
    LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode /\
                        ~MEM i.inst_id visited) bi)
End

Triviality unvisited_count_le:
  !bi visited. unvisited_count bi visited <= LENGTH bi
Proof
  rw[unvisited_count_def] >> irule LENGTH_FILTER_LEQ
QED

(* Monotonicity: more visited => smaller or equal count *)
Triviality unvisited_count_mono:
  !bi v1 v2.
    (!x. MEM x v1 ==> MEM x v2) ==>
    unvisited_count bi v2 <= unvisited_count bi v1
Proof
  rw[unvisited_count_def] >>
  irule LENGTH_FILTER_LEQ_MONO >>
  simp[] >> metis_tac[]
QED

(* Adding an already-visited id doesn't change count *)
Triviality unvisited_add_visited:
  !bi visited id.
    MEM id visited ==>
    unvisited_count bi (id :: visited) = unvisited_count bi visited
Proof
  rw[unvisited_count_def] >>
  AP_TERM_TAC >>
  simp[FILTER_EQ] >> metis_tac[]
QED

(* Adding a new non-pseudo id decreases count by exactly 1.
   Why: ALL_DISTINCT ids means inst is the unique element with that id,
   so FILTER removes exactly one element. *)
(* General list lemma: removing one unique-keyed element from FILTER
   decreases length by exactly 1 *)
Triviality filter_remove_unique_key:
  !P f l x.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ P x ==>
    LENGTH (FILTER (\y. P y /\ f y <> f x) l) + 1 =
    LENGTH (FILTER P l)
Proof
  Induct_on `l` >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_MAP]
  (* x is the head *)
  >- (simp[] >>
      `FILTER (\y. P y /\ f y <> f h) l = FILTER P l` suffices_by simp[] >>
      simp[FILTER_EQ] >> rpt strip_tac >>
      gvs[MEM_MAP] >> metis_tac[])
  (* x is in tail *)
  >> `f h <> f x` by (gvs[MEM_MAP] >> metis_tac[]) >>
  Cases_on `P h` >> simp[] >>
  first_x_assum (qspecl_then [`P`, `f`, `x`] mp_tac) >> simp[]
QED

Triviality unvisited_add_new:
  !bi visited inst.
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    ~MEM inst.inst_id visited /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    unvisited_count bi (inst.inst_id :: visited) + 1 =
    unvisited_count bi visited
Proof
  Induct_on `bi` >> simp[unvisited_count_def] >>
  rpt gen_tac >> strip_tac >> gvs[ALL_DISTINCT_MAP]
  (* inst is head *)
  >- (simp[] >>
      `FILTER (\i. ~is_pseudo i.inst_opcode /\ i.inst_id <> h.inst_id /\
                   ~MEM i.inst_id visited) bi =
       FILTER (\i. ~is_pseudo i.inst_opcode /\ ~MEM i.inst_id visited) bi` by
        (simp[FILTER_EQ] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
      simp[])
  (* inst is in tail *)
  >> `h.inst_id <> inst.inst_id` by (gvs[MEM_MAP] >> metis_tac[]) >>
  `unvisited_count bi (inst.inst_id :: visited) + 1 =
   unvisited_count bi visited` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `unvisited_count _ _ + 1 = _`
    (mp_tac o PURE_REWRITE_RULE[unvisited_count_def]) >>
  simp[unvisited_count_def] >> IF_CASES_TAC >> simp[]
QED

(* ===== sort_children preserves length ===== *)

Triviality sort_children_length:
  !bi order eda om parent children.
    LENGTH (sort_children bi order eda om parent children) = LENGTH children
Proof
  rw[sort_children_def] >>
  `PERM (MAPi (\i c. (i,c)) children)
        (QSORT _ (MAPi (\i c. (i,c)) children))` by
    simp[sortingTheory.QSORT_PERM] >>
  imp_res_tac sortingTheory.PERM_LENGTH >>
  simp[LENGTH_MAP, indexedListsTheory.LENGTH_MAPi]
QED

(* ===== deps count bounded by block length ===== *)

(* Pigeonhole: ALL_DISTINCT list whose elements are all MEM of another list
   has length <= that list *)
Triviality all_distinct_subset_length:
  !l1 l2. ALL_DISTINCT l1 /\ (!x. MEM x l1 ==> MEM x l2) ==>
           LENGTH l1 <= LENGTH l2
Proof
  rpt strip_tac >>
  `CARD (set l1) = LENGTH l1` by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set l2) <= LENGTH l2` by simp[CARD_LIST_TO_SET] >>
  `set l1 SUBSET set l2` by simp[SUBSET_DEF] >>
  `FINITE (set l2)` by simp[] >>
  `CARD (set l1) <= CARD (set l2)` by metis_tac[CARD_SUBSET] >>
  simp[]
QED

Triviality inst_all_deps_length_bound:
  !bi order eda inst.
    eda_wf eda bi ==>
    LENGTH (inst_all_deps bi order eda inst) <= LENGTH bi
Proof
  rpt strip_tac >>
  irule all_distinct_subset_length >> conj_tac
  >- (rpt strip_tac >> metis_tac[inst_all_deps_mem])
  >> simp[inst_all_deps_def, LET_THM, all_distinct_nub]
QED

(* ===== DFS measure ===== *)

Definition dfs_measure_def:
  dfs_measure bi state =
    LENGTH state.ds_stack +
    unvisited_count bi state.ds_visited * (LENGTH bi + 1)
End

(* ===== dfs_step strictly decreases measure when stack non-empty ===== *)

Theorem dfs_step_measure_dec:
  !bi order eda om fl state.
    state.ds_stack <> [] /\
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    dfs_good_state bi state ==>
    dfs_measure bi (dfs_step bi order eda om fl state) <
    dfs_measure bi state
Proof
  rpt strip_tac >>
  Cases_on `state.ds_stack` >> gvs[] >>
  Cases_on `h` >> rename1 `_ :: t`
  (* DfsProcess *)
  >- (rename1 `DfsProcess inst` >>
      Cases_on `MEM inst.inst_id state.ds_visited`
      >- simp[dfs_step_def, dfs_measure_def]
      >> Cases_on `is_pseudo inst.inst_opcode`
      >- suspend "pseudo"
      >> suspend "non_pseudo")
  (* DfsEmit *)
  >> suspend "emit"
QED

Resume dfs_step_measure_dec[pseudo]:
  simp[dfs_step_def, dfs_measure_def] >>
  `unvisited_count bi (inst.inst_id :: state.ds_visited) <=
   unvisited_count bi state.ds_visited` by
    (irule unvisited_count_mono >> simp[]) >>
  `(LENGTH bi + 1) * unvisited_count bi (inst.inst_id::state.ds_visited) <=
   (LENGTH bi + 1) * unvisited_count bi state.ds_visited` by simp[] >>
  decide_tac
QED

Resume dfs_step_measure_dec[non_pseudo]:
  simp[dfs_step_def, LET_THM, dfs_measure_def] >>
  `MEM inst bi` by gvs[dfs_good_state_def, EVERY_DEF] >>
  `LENGTH (sort_children bi order eda om inst
             (inst_all_deps bi order eda inst)) =
   LENGTH (inst_all_deps bi order eda inst)` by
    simp[sort_children_length] >>
  `LENGTH (inst_all_deps bi order eda inst) <= LENGTH bi` by
    (irule inst_all_deps_length_bound >> simp[]) >>
  `unvisited_count bi (inst.inst_id :: state.ds_visited) + 1 =
   unvisited_count bi state.ds_visited` by
    (irule unvisited_add_new >> simp[]) >>
  (* Substitute count = c'+1, then linearize multiplication *)
  pop_assum (SUBST1_TAC o SYM) >>
  simp[LEFT_ADD_DISTRIB]
QED

Resume dfs_step_measure_dec[emit]:
  simp[dfs_step_def, dfs_measure_def]
QED

Finalise dfs_step_measure_dec

(* ===== Measure reaches 0 after enough steps ===== *)

(* General measure lemma: if each non-idle step with non-empty stack
   strictly decreases the measure, and idle steps only happen at measure 0,
   then after enough steps measure = 0.

   We split into: step decreases when stack non-empty, and
   stack empty => measure = 0 (maintained as invariant). *)
Triviality funpow_idle:
  !n (f:'a -> 'a) s. f s = s ==> FUNPOW f n s = s
Proof
  Induct >> simp[FUNPOW]
QED

(* Measure 0 means stack empty and all non-pseudos visited *)
Triviality measure_zero_imp_visited:
  !bi state inst.
    dfs_measure bi state = 0 /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
    MEM inst.inst_id state.ds_visited
Proof
  rw[dfs_measure_def] >>
  gvs[unvisited_count_def] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode /\ ~MEM i.inst_id state.ds_visited) bi
   = []` by (Cases_on `FILTER _ bi` >> gvs[]) >>
  gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  first_x_assum (qspec_then `inst` mp_tac) >> simp[]
QED

Triviality measure_zero_imp_stack_empty:
  !bi state.
    dfs_measure bi state = 0 ==> state.ds_stack = []
Proof
  rw[dfs_measure_def] >> Cases_on `state.ds_stack` >> gvs[]
QED

(* General abstract lemma: if f either decreases the measure or is idle,
   and idle ⟹ measure=0, then after n ≥ measure(s) steps, measure=0.
   Proof by complete induction on n. *)
Triviality measure_decreases_to_zero:
  !n (f:'a -> 'a) (m:'a -> num) s.
    (!x. m x > 0 ==> m (f x) < m x) /\
    (!x. m (f x) >= m x ==> f x = x) /\
    m s <= n ==>
    m (FUNPOW f n s) = 0
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `n`
  >- (gvs[] >> Cases_on `m s` >> gvs[])
  >> rename1 `SUC k` >>
  Cases_on `m s = 0`
  >- (`f s = s` by (first_x_assum (qspec_then `s` mp_tac) >> simp[]) >>
      `FUNPOW f (SUC k) s = s` by (irule funpow_idle >> simp[]) >>
      simp[])
  >> `m (f s) < m s` by (first_x_assum match_mp_tac >> simp[]) >>
  simp[FUNPOW]
QED

(* Key helper: non-entry non-pseudos are deps of something.
   This is the contrapositive of entry_instructions_def:
   if inst is non-pseudo and NOT in entry_instructions,
   then inst.inst_id appears as a dep of some other non-pseudo. *)
Triviality all_distinct_map_inj:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==>
             x = y
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  `EL n (MAP f l) = EL n' (MAP f l)` by simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

Triviality non_entry_is_dep:
  !bi order eda inst.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    ~MEM inst (entry_instructions bi order eda) ==>
    ?parent. MEM parent bi /\ ~is_pseudo parent.inst_opcode /\
             MEM inst (inst_all_deps bi order eda parent)
Proof
  rpt strip_tac >>
  gvs[entry_instructions_def, LET_THM, MEM_FILTER] >>
  gvs[MEM_FLAT, MEM_MAP, MEM_nub, MEM_FILTER] >>
  qexists `i` >> simp[] >>
  `MEM d bi` by metis_tac[inst_all_deps_mem] >>
  metis_tac[all_distinct_map_inj]
QED

(* ===== Coverage invariant ===== *)

(* Every unvisited non-pseudo is either directly on the stack as DfsProcess,
   or is a dep of some unvisited non-pseudo (which will eventually be visited,
   pushing the dep onto the stack). *)
Definition dfs_coverage_def:
  dfs_coverage bi order eda state <=>
    !inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
           ~MEM inst.inst_id state.ds_visited ==>
      MEM (DfsProcess inst) state.ds_stack \/
      ?parent. MEM parent bi /\ ~is_pseudo parent.inst_opcode /\
               MEM inst (inst_all_deps bi order eda parent) /\
               ~MEM parent.inst_id state.ds_visited
End

(* Coverage + stack empty => all non-pseudos visited.
   Proof: by contradiction using eda_topo_compatible to get infinite
   ascending index chain, contradicting finiteness. *)
(* No unvisited non-pseudo at index k when coverage holds and stack is empty.
   Proof by strong induction on LENGTH bi - k: coverage gives unvisited parent
   at later index j > k; IH at j gives contradiction. *)
Triviality no_unvisited_at_index:
  !bi order eda visited k.
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
            ~MEM inst.inst_id visited ==>
       ?parent. MEM parent bi /\ ~is_pseudo parent.inst_opcode /\
                MEM inst (inst_all_deps bi order eda parent) /\
                ~MEM parent.inst_id visited) /\
    k < LENGTH bi /\
    ~is_pseudo (EL k bi).inst_opcode ==>
    MEM (EL k bi).inst_id visited
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  qid_spec_tac `k` >>
  completeInduct_on `LENGTH bi - k` >> rpt strip_tac >>
  spose_not_then assume_tac >>
  (* By coverage: EL k bi has unvisited non-pseudo parent *)
  last_assum (qspec_then `EL k bi` mp_tac) >>
  (impl_tac >- simp[EL_MEM]) >>
  disch_then strip_assume_tac >>
  (* eda_topo_compatible: parent at later index than dep *)
  `?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
         EL i bi = EL k bi /\ EL j bi = parent` by
    (fs[eda_topo_compatible_def] >>
     first_x_assum (qspecl_then [`parent`, `EL k bi`] mp_tac) >>
     simp[EL_MEM]) >>
  `i = k` by
    (`EL i (MAP (\i. i.inst_id) bi) = EL k (MAP (\i. i.inst_id) bi)` by
       simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  gvs[]
QED

(* Coverage + empty stack => all non-pseudos visited. *)
Triviality coverage_stack_empty_imp_visited:
  !bi order eda state.
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    dfs_coverage bi order eda state /\
    state.ds_stack = [] ==>
    unvisited_count bi state.ds_visited = 0
Proof
  rpt strip_tac >> simp[unvisited_count_def] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  (* Get index for the unvisited element *)
  `?k. k < LENGTH bi /\ EL k bi = i` by metis_tac[MEM_EL] >>
  (* coverage + stack=[] gives parent clause *)
  `!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
          ~MEM inst.inst_id state.ds_visited ==>
     ?parent. MEM parent bi /\ ~is_pseudo parent.inst_opcode /\
              MEM inst (inst_all_deps bi order eda parent) /\
              ~MEM parent.inst_id state.ds_visited` by
    (gvs[dfs_coverage_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  qspecl_then [`bi`, `order`, `eda`, `state.ds_visited`, `k`]
    mp_tac no_unvisited_at_index >> gvs[]
QED

(* Coverage preserved by dfs_step *)
(* Helper: use coverage assumption for a specific inst *)
Triviality use_coverage:
  !bi order eda state inst.
    dfs_coverage bi order eda state /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    ~MEM inst.inst_id state.ds_visited ==>
    MEM (DfsProcess inst) state.ds_stack \/
    ?parent. MEM parent bi /\ ~is_pseudo parent.inst_opcode /\
             MEM inst (inst_all_deps bi order eda parent) /\
             ~MEM parent.inst_id state.ds_visited
Proof
  simp[dfs_coverage_def]
QED

Triviality good_state_process_mem:
  !bi state top rest.
    dfs_good_state bi state /\
    state.ds_stack = DfsProcess top :: rest ==>
    MEM top bi
Proof
  rpt strip_tac >> gvs[dfs_good_state_def]
QED

Theorem dfs_step_preserves_coverage:
  !bi order eda om fl state.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    dfs_good_state bi state /\
    dfs_coverage bi order eda state ==>
    dfs_coverage bi order eda (dfs_step bi order eda om fl state)
Proof
  rpt strip_tac >>
  CONV_TAC (PURE_REWRITE_CONV [dfs_coverage_def]) >>
  rpt gen_tac >> strip_tac >>
  `~MEM inst.inst_id state.ds_visited` by
    (strip_tac >> imp_res_tac dfs_step_visited_mono >> gvs[]) >>
  drule_all use_coverage >>
  disch_then assume_tac >>
  Cases_on `state.ds_stack`
  >- suspend "empty_stack"
  >> Cases_on `h`
  >- (rename1 `DfsProcess top :: rest` >>
      Cases_on `MEM top.inst_id state.ds_visited`
      >- suspend "process_visited"
      >> Cases_on `is_pseudo top.inst_opcode`
      >- suspend "process_pseudo"
      >> suspend "process_nonpseudo")
  >> suspend "emit"
QED

(* --- empty_stack: dfs_step = identity --- *)
Resume dfs_step_preserves_coverage[empty_stack]:
  simp[dfs_step_def] >> gvs[] >> metis_tac[]
QED

(* --- process_visited: top already visited, pop, visited unchanged --- *)
Resume dfs_step_preserves_coverage[process_visited]:
  simp[dfs_step_def] >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  >- (gvs[MEM] >> disj1_tac >> simp[])
  >> disj2_tac >> metis_tac[]
QED

(* --- process_pseudo: top is pseudo, pop, mark visited --- *)
Resume dfs_step_preserves_coverage[process_pseudo]:
  simp[dfs_step_def] >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  (* on-stack: inst ∈ DfsProcess top :: rest *)
  >- (gvs[MEM] (* splits inst=top | inst∈rest; inst=top gives F *) >>
      disj1_tac >> simp[])
  (* has-parent: parent.inst_id ≠ top.inst_id by pseudo/non-pseudo *)
  >> disj2_tac >> qexists `parent` >> simp[] >>
  `MEM top bi` by metis_tac[good_state_process_mem] >>
  strip_tac >>
  `parent = top` by metis_tac[all_distinct_map_inj] >>
  gvs[]
QED

(* --- process_nonpseudo: top is non-pseudo, push children, mark visited --- *)
Resume dfs_step_preserves_coverage[process_nonpseudo]:
  `MEM top bi` by
    (qpat_x_assum `dfs_good_state _ _` mp_tac >>
     qpat_x_assum `state.ds_stack = _` mp_tac >>
     metis_tac[good_state_process_mem]) >>
  simp[dfs_step_def, LET_THM] >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  (* on-stack: inst ∈ DfsProcess top :: rest *)
  >- (gvs[MEM]
      (* inst = top: top.inst_id is visited by dfs_step, contradiction *)
      >- metis_tac[dfs_step_visits_top_process]
      (* inst ∈ rest: still on stack *)
      >> disj1_tac >> simp[])
  (* has parent *)
  >> Cases_on `parent.inst_id = top.inst_id`
  (* parent = top: inst pushed as child *)
  >- (`parent = top` by metis_tac[all_distinct_map_inj] >>
      gvs[] >> disj1_tac >>
      simp[MEM_MAP] >>
      metis_tac[sort_children_mem])
  (* parent ≠ top: parent still unvisited *)
  >> disj2_tac >> qexists `parent` >> simp[]
QED

(* --- emit: DfsEmit, pop, visited unchanged --- *)
Resume dfs_step_preserves_coverage[emit]:
  rename1 `DfsEmit top :: rest` >>
  simp[dfs_step_def] >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac
  >- (gvs[MEM] >> disj1_tac >> simp[])
  >> disj2_tac >> metis_tac[]
QED

Finalise dfs_step_preserves_coverage

(* Coverage holds for initial entry_instructions state *)
Triviality entry_instructions_coverage:
  !bi order eda.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    dfs_coverage bi order eda
      <| ds_stack := MAP DfsProcess (entry_instructions bi order eda);
         ds_output := []; ds_visited := [] |>
Proof
  simp[dfs_coverage_def] >> rpt strip_tac >>
  Cases_on `MEM inst (entry_instructions bi order eda)`
  >- (disj1_tac >> simp[MEM_MAP] >> qexists `inst` >> simp[])
  >> disj2_tac >>
  drule_all non_entry_is_dep >> strip_tac >>
  qexists `parent` >> simp[]
QED

(* DFS-specific: measure reaches 0 using coverage invariant.
   Coverage + stack=[] => unvisited=0, so measure=0 when idle.
   Combined with dfs_step_measure_dec, measure strictly decreases
   at each non-idle step. *)
Theorem measure_reaches_zero:
  !n bi order eda om fl state.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    dfs_good_state bi state /\
    dfs_coverage bi order eda state /\
    dfs_measure bi state <= n ==>
    dfs_measure bi
      (FUNPOW (dfs_step bi order eda om fl) n state) = 0
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[dfs_measure_def]
  >> Cases_on `dfs_measure bi state = 0`
  >- (`state.ds_stack = []` by metis_tac[measure_zero_imp_stack_empty] >>
      simp[funpow_dfs_step_idle])
  >> `state.ds_stack <> []` by
       (CCONTR_TAC >>
        `unvisited_count bi state.ds_visited = 0` by
          metis_tac[coverage_stack_empty_imp_visited] >>
        gvs[dfs_measure_def]) >>
  `dfs_measure bi (dfs_step bi order eda om fl state) <
   dfs_measure bi state` by
    (irule dfs_step_measure_dec >> simp[]) >>
  simp[FUNPOW] >>
  first_x_assum (qspecl_then [`bi`, `order`, `eda`, `om`, `fl`,
    `dfs_step bi order eda om fl state`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt conj_tac
      >- (irule dfs_step_preserves_good >> simp[])
      >- (irule dfs_step_preserves_coverage >> simp[])
      >> decide_tac)
  >> simp[]
QED

(* ===== entries are a subset of non-pseudos of bi ===== *)

Triviality entry_instructions_length:
  !bi order eda.
    LENGTH (entry_instructions bi order eda) <= LENGTH bi
Proof
  rw[entry_instructions_def, LET_THM] >>
  irule LESS_EQ_TRANS >>
  qexists `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` >>
  simp[LENGTH_FILTER_LEQ]
QED

(* ===== Main completeness: all non-pseudos visited after budget ===== *)

Theorem schedule_all_visited:
  !bi order eda offspring_map.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    let entries = entry_instructions bi order eda in
    let final = FUNPOW (dfs_step bi order eda offspring_map T)
                       ((LENGTH bi + 1) * (LENGTH bi + 1))
                       <| ds_stack := MAP DfsProcess entries;
                          ds_output := []; ds_visited := [] |> in
    (!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
            MEM inst.inst_id final.ds_visited) /\
    final.ds_stack = []
Proof
  rpt strip_tac >> simp[LET_THM] >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `init = <| ds_stack := MAP DfsProcess entries;
                          ds_output := []; ds_visited := [] |>` >>
  qmatch_goalsub_abbrev_tac `FUNPOW f budget init` >>
  (* Show measure reaches 0 *)
  `dfs_measure bi (FUNPOW f budget init) = 0` by
    suspend "measure_zero" >>
  conj_tac
  >- (rpt strip_tac >> drule_all measure_zero_imp_visited >> simp[])
  >> metis_tac[measure_zero_imp_stack_empty]
QED

Resume schedule_all_visited[measure_zero]:
  simp[Abbr `f`] >>
  qspecl_then [`budget`, `bi`, `order`, `eda`, `offspring_map`, `T`,
               `init`] mp_tac measure_reaches_zero >>
  simp[Abbr `budget`, Abbr `init`, Abbr `entries`] >>
  impl_tac
  >- (rpt conj_tac
      >- (irule init_dfs_state_good >> simp[entry_instructions_mem])
      >- (irule entry_instructions_coverage >> simp[])
      >> simp[dfs_measure_def, LENGTH_MAP, unvisited_count_def, MEM] >>
      `LENGTH (entry_instructions bi order eda) <= LENGTH bi` by
        simp[entry_instructions_length] >>
      `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bi) <= LENGTH bi` by
        simp[LENGTH_FILTER_LEQ] >>
      irule LESS_EQ_TRANS >>
      qexists `LENGTH bi + LENGTH bi * (LENGTH bi + 1)` >>
      conj_tac
      >- (irule LESS_EQ_LESS_EQ_MONO >>
          conj_tac >- simp[] >>
          irule LESS_MONO_MULT >> simp[])
      >> rewrite_tac[EXP_2] >>
      simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB])
  >> simp[]
QED

Finalise schedule_all_visited

(* ===== FUNPOW preserves dfs_topo_inv ===== *)

Triviality funpow_preserves_topo_inv:
  !n bi order eda om fl state.
    dfs_topo_inv bi order eda state /\
    dfs_good_state bi state /\
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    dfs_topo_inv bi order eda
      (FUNPOW (dfs_step bi order eda om fl) n state)
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (irule dfs_step_preserves_good >> simp[])
  >> irule dfs_step_preserves_topo >> simp[]
QED

(* ===== Combining: all non-pseudo ids in schedule output ===== *)

Theorem schedule_output_complete:
  !bi order eda offspring_map.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    !inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
           MEM inst.inst_id
             (MAP (\i. i.inst_id)
                (schedule_from_entries bi order eda offspring_map
                   (entry_instructions bi order eda)))
Proof
  rpt strip_tac >>
  simp[schedule_from_entries_def, LET_THM] >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `budget = (LENGTH bi + 1) * (LENGTH bi + 1)` >>
  qabbrev_tac `init = <| ds_stack := MAP DfsProcess entries;
                          ds_output := []; ds_visited := [] |>` >>
  qabbrev_tac `final = FUNPOW (dfs_step bi order eda offspring_map T)
                               budget init` >>
  (* All non-pseudos visited and stack empty *)
  `MEM inst.inst_id final.ds_visited /\ final.ds_stack = []` by
    (simp[Abbr `final`, Abbr `init`, Abbr `budget`] >>
     drule_all schedule_all_visited >>
     simp[LET_THM]) >>
  (* dfs_topo_inv holds at final state *)
  `dfs_topo_inv bi order eda final` by
    suspend "topo_inv" >>
  (* dfs_topo_inv: visited /\ ~pending => in output. Stack empty => not pending. *)
  `stack_emit_ids final.ds_stack = []` by simp[stack_emit_ids_def] >>
  gvs[dfs_topo_inv_def] >>
  first_x_assum irule >> simp[]
QED

Triviality stack_emit_ids_map_process:
  !l. stack_emit_ids (MAP DfsProcess l) = []
Proof
  Induct >> simp[stack_emit_ids_def]
QED

Triviality stack_well_ordered_map_process:
  !l resolved bi order eda.
    stack_well_ordered (MAP DfsProcess l) resolved bi order eda
Proof
  Induct >> simp[stack_well_ordered_def, stack_emit_ids_map_process]
QED

Triviality stack_pos_ordered_map_process:
  !l bi. stack_pos_ordered bi (MAP DfsProcess l)
Proof
  Induct >> simp[stack_pos_ordered_def, stack_emit_ids_map_process]
QED

Resume schedule_output_complete[topo_inv]:
  simp[Abbr `final`, Abbr `budget`] >>
  irule funpow_preserves_topo_inv >> simp[Abbr `init`] >>
  conj_tac
  >- (irule init_dfs_state_good >>
      simp[Abbr `entries`, entry_instructions_mem])
  >> simp[dfs_topo_inv_def, output_producer_before_def, output_eda_before_def,
          stack_well_ordered_map_process, stack_pos_ordered_map_process,
          stack_emit_ids_map_process]
QED

Finalise schedule_output_complete

