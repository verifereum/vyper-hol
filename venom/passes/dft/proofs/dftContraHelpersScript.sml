Theory dftContraHelpers
Ancestors
  dftCanonicalDep dftFrontEquiv dftStructural dftPermSim
  venomInst venomWf stateEquiv stateEquivProps
  dftWf dftTopoSort dftDefs dftPipelineInvar arithmetic
  dftIdempotent allocaRemapSSA
  relation list rich_list sorting pred_set

(* If ALL_DISTINCT (MAP inst_id l) and two elements have same inst_id, then their indices are equal *)
Triviality all_distinct_inst_id_el_eq[local]:
  !l j k.
    ALL_DISTINCT (MAP (\q. q.inst_id) l) /\ j < LENGTH l /\ k < LENGTH l /\
    (EL j l).inst_id = (EL k l).inst_id ==> j = k
Proof
  rpt strip_tac >>
  `j < LENGTH (MAP (\q. q.inst_id) l) /\ k < LENGTH (MAP (\q. q.inst_id) l)` by simp[LENGTH_MAP] >>
  `EL j (MAP (\q. q.inst_id) l) = (EL j l).inst_id /\
   EL k (MAP (\q. q.inst_id) l) = (EL k l).inst_id` by simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

Triviality orig_data_dep_contra[local]:
  !fn bi fl bb i j i' j' v.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\ bi = bb.bb_instructions /\
    fl = FILTER (\q. ~is_pseudo q.inst_opcode) bi /\
    i < j /\ j < LENGTH fl /\
    i' < j' /\ j' < LENGTH bi /\ EL i' bi = EL i fl /\ EL j' bi = EL j fl /\
    defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    MEM (Var v) (EL i fl).inst_operands /\ MEM v (EL j fl).inst_outputs ==>
    F
Proof
  rpt strip_tac >>
  `MEM (EL j' bi) bi` by simp[EL_MEM] >>
  `MEM v (EL j' bi).inst_outputs` by metis_tac[] >>
  `producing_inst bi v = SOME (EL j' bi)` by (
    irule producing_inst_unique_definer >> simp[] >>
    rpt strip_tac >>
    metis_tac[all_distinct_flat_map_unique]) >>
  `?m. m < i' /\ EL m bi = EL j' bi` by (
    `MEM (Var v) (EL i' bi).inst_operands` by metis_tac[] >>
    `i' < LENGTH bi` by decide_tac >>
    fs[defs_before_uses_def] >>
    metis_tac[]) >>
  `m = j'` by (
    `m < LENGTH bi` by decide_tac >>
    `EL m (MAP (\i. i.inst_id) bi) = EL j' (MAP (\i. i.inst_id) bi)` by simp[EL_MAP] >>
    metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  decide_tac
QED

(* If MAP f l = pfx ++ [f (EL i l)] ++ sfx and ALL_DISTINCT, then i = LENGTH pfx *)
Triviality all_distinct_map_el_append[local]:
  !l (f: 'a -> 'b) pfx sfx i.
    ALL_DISTINCT (MAP f l) /\ i < LENGTH l /\
    MAP f l = pfx ++ [f (EL i l)] ++ sfx ==> i = LENGTH pfx
Proof
  rpt strip_tac >> drule ALL_DISTINCT_EL_APPEND >> disch_then (qspecl_then [`pfx`,`sfx`,`i`] mp_tac) >> simp[LENGTH_MAP, EL_MAP]
QED

(* from_barrier_dep contradiction: if i < j and EL i fl is a barrier
   with from_barrier_dep, then (EL j fl).inst_id is in the prefix before
   (EL i fl).inst_id, meaning j < i. Contradiction. *)
Theorem orig_from_barrier_contra:
  !bi fl i j.
    i < j /\ j < LENGTH fl /\
    ALL_DISTINCT (MAP (\q. q.inst_id) fl) /\
    fl = FILTER (\q. ~is_pseudo q.inst_opcode) bi /\
    is_barrier (EL i fl) /\
    from_barrier_dep bi (EL i fl) (EL j fl) ==>
    F
Proof
  rpt strip_tac >>
  `i < LENGTH fl` by decide_tac >>
  drule (iffLR from_barrier_dep_def) >> rpt strip_tac >>
  `MAP (\q. q.inst_id) fl = pfx ++ [(EL i fl).inst_id] ++ sfx` by metis_tac[] >>
  `i = LENGTH pfx` by metis_tac[all_distinct_map_el_append] >>
  `?k. k < LENGTH pfx /\ EL k pfx = (EL j fl).inst_id` by metis_tac[MEM_EL] >>
  `k < LENGTH fl` by decide_tac >>
  `(EL k fl).inst_id = (EL j fl).inst_id` by (
    `EL k (MAP (\q. q.inst_id) fl) = (EL k fl).inst_id` by simp[EL_MAP] >>
    `EL k (pfx ++ [(EL i fl).inst_id] ++ sfx) = EL k pfx` by simp[rich_listTheory.EL_APPEND1] >>
    metis_tac[]) >>
  `j = k` by metis_tac[all_distinct_inst_id_el_eq] >>
  decide_tac
QED

(* on_barrier_dep contradiction: if i < j and EL i fl is NOT a barrier
   with on_barrier_dep, the LAST barrier in the prefix before EL i fl
   has (EL j fl).inst_id. Since that LAST barrier is in the prefix at
   index k < LENGTH pfx = i, we get j = k < i. Contradiction. *)
Theorem orig_on_barrier_contra:
  !bi fl i j.
    i < j /\ j < LENGTH fl /\
    ALL_DISTINCT (MAP (\q. q.inst_id) fl) /\
    fl = FILTER (\q. ~is_pseudo q.inst_opcode) bi /\
    ~is_barrier (EL i fl) /\
    on_barrier_dep bi (EL i fl) (EL j fl) ==>
    F
Proof
  rpt strip_tac >>
  `i < LENGTH fl` by decide_tac >>
  drule (iffLR on_barrier_dep_def) >> rpt strip_tac >>
  `fl = pfx ++ [mid] ++ sfx` by metis_tac[] >>
  `MAP (\q. q.inst_id) fl = MAP (\q. q.inst_id) pfx ++ [mid.inst_id] ++ MAP (\q. q.inst_id) sfx` by simp[MAP_APPEND] >>
  `MAP (\q. q.inst_id) fl = MAP (\q. q.inst_id) pfx ++ [(EL i fl).inst_id] ++ MAP (\q. q.inst_id) sfx` by metis_tac[] >>
  `i = LENGTH pfx` by metis_tac[all_distinct_map_el_append, LENGTH_MAP] >>
  `MEM (LAST (FILTER is_barrier pfx)) (FILTER is_barrier pfx)` by metis_tac[LAST_MEM] >>
  `MEM (LAST (FILTER is_barrier pfx)) pfx` by metis_tac[MEM_FILTER] >>
  `?k. k < LENGTH pfx /\ EL k pfx = LAST (FILTER is_barrier pfx)` by metis_tac[MEM_EL] >>
  `EL k fl = EL k pfx` by metis_tac[rich_listTheory.EL_APPEND1, APPEND_ASSOC] >>
  `(EL k fl).inst_id = (EL j fl).inst_id` by metis_tac[] >>
  `k < LENGTH fl` by decide_tac >>
  `j = k` by metis_tac[all_distinct_inst_id_el_eq] >>
  decide_tac
QED

(* FILTER preserves element order: if i < j in FILTER P l,
   then the corresponding positions in l also satisfy n < m.
   Direct induction proof. *)
Theorem FILTER_preserves_order:
  !P l i j.
    i < j /\ j < LENGTH (FILTER P l) ==>
    ?n m. n < m /\ n < LENGTH l /\ m < LENGTH l /\
          EL n l = EL i (FILTER P l) /\ EL m l = EL j (FILTER P l)
Proof
  rpt strip_tac >> drule_all filter_el_mono >>
  rpt strip_tac >>
  qexistsl_tac [`i'`,`j'`] >> simp[] >> decide_tac
QED

(* Specialized version for instruction lists: if i < j in the filtered
   non-pseudo list, and we know ALL_DISTINCT inst_ids in bi, then the
   bi-level indices are also ordered. *)
Theorem filter_preserves_inst_order:
  !bi fl i j.
    ALL_DISTINCT (MAP (\q. q.inst_id) bi) /\
    fl = FILTER (\q. ~is_pseudo q.inst_opcode) bi /\
    i < j /\ j < LENGTH fl ==>
    ?n m. n < m /\ n < LENGTH bi /\ m < LENGTH bi /\
          EL n bi = EL i fl /\ EL m bi = EL j fl
Proof
  rpt strip_tac >>
  `?n m. n < m /\ n < LENGTH bi /\ m < LENGTH bi /\ EL n bi = EL i fl /\ EL m bi = EL j fl`
    by (qspecl_then [`(\q. ~is_pseudo q.inst_opcode)`,`bi`,`i`,`j`] mp_tac FILTER_preserves_order >>
      simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `m`] >> simp[]
QED

(* Data dep contradiction for the filtered list case.
   If EL j fl defines v used by EL i fl with i < j, and defs_before_uses
   holds in bi, then by def_dominates_uses the def must come before the use
   in bi. But FILTER preserves order so i < j means use comes before def
   in bi too. Contradiction. *)
Theorem orig_data_dep_contra_filtered:
  !fn bi fl bb i j v.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\ bi = bb.bb_instructions /\
    fl = FILTER (\q. ~is_pseudo q.inst_opcode) bi /\
    i < j /\ j < LENGTH fl /\
    ALL_DISTINCT (MAP (\q. q.inst_id) bi) /\
    defs_before_uses bi /\
    ALL_DISTINCT (FLAT (MAP (\q. q.inst_outputs) bi)) /\
    MEM (Var v) (EL i fl).inst_operands /\ MEM v (EL j fl).inst_outputs ==>
    F
Proof
  rpt strip_tac >>
  `?n m. n < m /\ n < LENGTH bi /\ m < LENGTH bi /\ EL n bi = EL i fl /\ EL m bi = EL j fl`
    by metis_tac[filter_preserves_inst_order] >>
  `MEM (EL m bi) bi` by simp[EL_MEM] >>
  `MEM v (EL m bi).inst_outputs` by metis_tac[] >>
  `producing_inst bi v = SOME (EL m bi)` by (
    irule producing_inst_unique_definer >> simp[] >>
    rpt strip_tac >> metis_tac[all_distinct_flat_map_unique]) >>
  `?p. p < n /\ EL p bi = EL m bi` by (
    `MEM (Var v) (EL n bi).inst_operands` by metis_tac[] >>
    `n < LENGTH bi` by decide_tac >>
    fs[defs_before_uses_def] >>
    metis_tac[]) >>
  `p = m` by (
    `p < LENGTH bi` by decide_tac >>
    `EL p (MAP (\q. q.inst_id) bi) = EL m (MAP (\q. q.inst_id) bi)` by simp[EL_MAP] >>
    metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  decide_tac
QED
