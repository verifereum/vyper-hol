(*
 * DFT Schedule Fixed — proved utility lemmas.
 *
 * Note: schedule_pipeline_eq was proved FALSE.
 * The DFS tiebreaking depends on build_eda processing order,
 * so the pipeline is NOT invariant under instruction permutation.
 *
 *)

Theory dftScheduleFixed
Ancestors
  dftPipelineInvar dftStructural dftIdempotent dftDefs venomEffects
  passSharedDefs venomInst list rich_list sorting
  finite_map pred_set pair arithmetic

(* ================================================================
   Subset injectivity
   ================================================================ *)

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

