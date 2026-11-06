Theory dftGasInvSchedulerProvenance
Ancestors
  dftTopoSort dftStructural arithmetic

Theorem inv_process_emit_ids[local]:
  !entries. stack_emit_ids (MAP DfsProcess entries) = []
Proof
  Induct >> simp[stack_emit_ids_def]
QED

Theorem inv_process_positions[local]:
  !entries. stack_pos_ordered bi (MAP DfsProcess entries)
Proof
  Induct >> simp[stack_pos_ordered_def, inv_process_emit_ids]
QED

Theorem inv_process_stack_ordered[local]:
  !entries resolved.
    stack_well_ordered (MAP DfsProcess entries) resolved bi order eda
Proof
  Induct >> simp[stack_well_ordered_def, inv_process_emit_ids]
QED

Theorem inv_scheduler_initial_topo[local]:
  dfs_topo_inv bi order eda
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|>
Proof
  simp[dfs_topo_inv_def, output_producer_before_def, output_eda_before_def,
       inv_process_emit_ids, inv_process_stack_ordered,
       inv_process_positions]
QED

Theorem inv_scheduler_iterate[local]:
  !n bi order eda om do_flip state.
    dfs_topo_inv bi order eda state /\ dfs_good_state bi state /\
    eda_wf eda bi /\ eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    dfs_topo_inv bi order eda
      (FUNPOW (dfs_step bi order eda om do_flip) n state)
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[dfs_step_preserves_topo, dfs_step_preserves_good]
QED

Theorem inv_scheduler_topo[local]:
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  bi <> [] /\
  (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\ EVERY (\i. MEM i bi) entries /\
  st = FUNPOW (dfs_step bi order eda om do_flip) n
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|> ==>
  dfs_topo_inv bi order eda st
Proof
  strip_tac >> gvs[] >> irule inv_scheduler_iterate >>
  simp[inv_scheduler_initial_topo, init_dfs_state_good]
QED

Theorem inv_scheduler_eda_provenance:
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  bi <> [] /\
  (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\ EVERY (\i. MEM i bi) entries /\
  st = FUNPOW (dfs_step bi order eda om do_flip) n
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|> /\
  MEM i st.ds_output /\ MEM dep bi /\
  MEM dep (case FLOOKUP eda i.inst_id of NONE => [] | SOME ds => ds) /\
  ~is_pseudo dep.inst_opcode ==>
  MEM dep.inst_id (MAP (\j. j.inst_id) st.ds_output) /\
  MEM dep.inst_id st.ds_visited /\
  ~MEM dep.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >>
  `dfs_topo_inv bi order eda st` by (irule inv_scheduler_topo >> metis_tac[]) >>
  fs[dfs_topo_inv_def] >> metis_tac[]
QED

Theorem inv_scheduler_producer_provenance:
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  bi <> [] /\
  (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\ EVERY (\i. MEM i bi) entries /\
  st = FUNPOW (dfs_step bi order eda om do_flip) n
    <|ds_stack := MAP DfsProcess entries; ds_output := []; ds_visited := []|> /\
  MEM i st.ds_output /\ MEM dep bi /\
  MEM (Var v) i.inst_operands /\ producing_inst bi v = SOME dep /\
  ~is_pseudo dep.inst_opcode ==>
  MEM dep.inst_id (MAP (\j. j.inst_id) st.ds_output) /\
  MEM dep.inst_id st.ds_visited /\
  ~MEM dep.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >>
  `dfs_topo_inv bi order eda st` by (irule inv_scheduler_topo >> metis_tac[]) >>
  fs[dfs_topo_inv_def] >> metis_tac[]
QED
