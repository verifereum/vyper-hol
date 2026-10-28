(* Exact native DFS cases with explicit work-stack and dependency facts. *)
Theory venomDfsCases
Ancestors dftDefs list

Theorem dfs_step_empty:
  !block_insts order eda offspring_map do_flip state.
    state.ds_stack = [] ==>
    dfs_step block_insts order eda offspring_map do_flip state = state
Proof
  simp[dfs_step_def]
QED

Theorem dfs_step_emit:
  !block_insts order eda offspring_map do_flip state inst rest.
    state.ds_stack = DfsEmit inst :: rest ==>
    dfs_step block_insts order eda offspring_map do_flip state =
      state with <|ds_stack := rest; ds_output := state.ds_output ++ [inst]|>
Proof
  simp[dfs_step_def]
QED

Theorem dfs_step_visited:
  !block_insts order eda offspring_map do_flip state inst rest.
    state.ds_stack = DfsProcess inst :: rest /\
    MEM inst.inst_id state.ds_visited ==>
    dfs_step block_insts order eda offspring_map do_flip state =
      state with ds_stack := rest
Proof
  simp[dfs_step_def]
QED

Theorem dfs_step_pseudo:
  !block_insts order eda offspring_map do_flip state inst rest.
    state.ds_stack = DfsProcess inst :: rest /\
    ~MEM inst.inst_id state.ds_visited /\ is_pseudo inst.inst_opcode ==>
    dfs_step block_insts order eda offspring_map do_flip state =
      state with <|ds_stack := rest;
        ds_visited := inst.inst_id :: state.ds_visited|>
Proof
  simp[dfs_step_def]
QED

Theorem dfs_step_process:
  !block_insts order eda offspring_map do_flip state inst rest children sorted.
    state.ds_stack = DfsProcess inst :: rest /\
    ~MEM inst.inst_id state.ds_visited /\ ~is_pseudo inst.inst_opcode /\
    inst_all_deps block_insts order eda inst = children /\
    sort_children block_insts order eda offspring_map inst children = sorted ==>
    dfs_step block_insts order eda offspring_map do_flip state =
      state with <|
        ds_stack := MAP DfsProcess sorted ++
          [DfsEmit (if do_flip /\ is_flippable inst.inst_opcode /\
                        sorted <> children then flip_operands inst else inst)] ++ rest;
        ds_visited := inst.inst_id :: state.ds_visited|>
Proof
  simp[dfs_step_def]
QED
