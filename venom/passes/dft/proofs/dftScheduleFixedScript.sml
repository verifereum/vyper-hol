(*
 * DFT Schedule Fixed — proved utility lemmas.
 *
 * Note: schedule_pipeline_eq was proved FALSE.
 * The DFS tiebreaking depends on build_eda processing order,
 * so the pipeline is NOT invariant under instruction permutation.
 *
 * Kept: subset_all_distinct_inj, dfs_step_idle, funpow_dfs_step_idle,
 *       from_block_inst_outputs, from_block_inst_id.
 *)

Theory dftScheduleFixed
Ancestors
  dftPipelineInvar dftStructural dftIdempotent dftDefs venomEffects
  passSharedDefs venomInst list rich_list sorting
  finite_map pred_set pair arithmetic

(* ================================================================
   Subset injectivity
   ================================================================ *)

Triviality subset_all_distinct_inj:
  !L (ls : instruction list).
    ALL_DISTINCT (MAP (\i. i.inst_id) L) /\
    (!x. MEM x ls ==> MEM x L) ==>
    INJ (\i:instruction. i.inst_id) (set ls) UNIV
Proof
  rpt strip_tac >>
  `!x y. MEM x ls /\ MEM y ls /\ (x.inst_id = y.inst_id) ==> (x = y)` by (
    rpt strip_tac >>
    `MEM x L /\ MEM y L` by metis_tac[] >>
    `?nx. nx < LENGTH L /\ (EL nx L = x)` by metis_tac[MEM_EL] >>
    `?ny. ny < LENGTH L /\ (EL ny L = y)` by metis_tac[MEM_EL] >>
    `EL nx (MAP (\i. i.inst_id) L) = x.inst_id` by simp[EL_MAP] >>
    `EL ny (MAP (\i. i.inst_id) L) = y.inst_id` by simp[EL_MAP] >>
    `nx < LENGTH (MAP (\i. i.inst_id) L)` by simp[] >>
    `ny < LENGTH (MAP (\i. i.inst_id) L)` by simp[] >>
    `EL nx (MAP (\i. i.inst_id) L) = EL ny (MAP (\i. i.inst_id) L)` by
      metis_tac[] >>
    `nx = ny` by metis_tac[ALL_DISTINCT_EL_IMP] >>
    metis_tac[]) >>
  simp[INJ_DEF]
QED

(* ================================================================
   DFS idle fixpoint
   ================================================================ *)

Theorem dfs_step_idle:
  !L order eda om fl s.
    s.ds_stack = [] ==>
    dfs_step L order eda om fl s = s
Proof
  rw[dfs_step_def]
QED

Theorem funpow_dfs_step_idle:
  !n L order eda om fl s.
    s.ds_stack = [] ==>
    FUNPOW (dfs_step L order eda om fl) n s = s
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  `dfs_step L order eda om fl s = s` by simp[dfs_step_idle] >>
  simp[]
QED

(* ================================================================
   from_block preserves structural properties
   ================================================================ *)

Triviality from_block_inst_outputs:
  !L i. from_block L i ==>
    ?j. MEM j L /\ ~is_pseudo j.inst_opcode /\ i.inst_outputs = j.inst_outputs
Proof
  rw[from_block_def] >> gvs[]
  >- metis_tac[]
  >> qexists_tac `j` >> simp[flip_operands_inst_outputs]
QED

Triviality from_block_inst_id:
  !L i. from_block L i ==>
    ?j. MEM j L /\ ~is_pseudo j.inst_opcode /\ i.inst_id = j.inst_id
Proof
  rw[from_block_def] >> gvs[]
  >- metis_tac[]
  >> qexists_tac `j` >> simp[flip_operands_inst_id]
QED

