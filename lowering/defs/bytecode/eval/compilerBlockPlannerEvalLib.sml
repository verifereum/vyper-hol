(* Certify the real recursive instruction suffixes as well as leaf plans. *)
structure compilerBlockPlannerEvalLib = struct
  open HolKernel
  val loop_head = compilerPlannerEvalLib.insts_head
  val function_head = compilerPlannerEvalLib.function_head
  val traversal_head = compilerPlannerEvalLib.traversal_head
  val successors_head = compilerPlannerEvalLib.successors_head
  val lookup_head = prim_mk_const {Thy="venomInst",Name="lookup_block"}
  val regular_head = prim_mk_const {Thy="stackPlanGen",Name="generate_regular_inst_plan"}
  val regular_queries =
    [(prim_mk_const {Thy="stackPlanGen",Name="emit_input_plan"},4),
     (prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"},3),
     (prim_mk_const {Thy="stackPlanGen",Name="generate_emit_ops"},3),
     (prim_mk_const {Thy="stackPlanOps",Name="popmany_plan"},2),
     (prim_mk_const {Thy="stackPlanGen",Name="optimistic_swap_plan"},5),
     (prim_mk_const {Thy="stackPlanOps",Name="release_dead_spills"},2)]
  fun entry_head () = prim_mk_const {Thy="stackPlanBlockCases",Name="planner_block_entry"}
  fun cleanup_head () = prim_mk_const {Thy="stackPlanBlockCases",Name="planner_block_cleanup"}
  val metadata_heads =
    [prim_mk_const {Thy="stackPlanGen",Name="non_param_insts"},
     prim_mk_const {Thy="stackPlanGen",Name="get_params"},
     prim_mk_const {Thy="cfgTransform",Name="bb_is_halting"}]

  fun configure () =
    (compilerPlannerEvalLib.configure ();
     app (fn head => evalCompilerBytecodeLib.ensure_certificate_head head 1) metadata_heads;
     app (fn (head,arity) => evalCompilerBytecodeLib.ensure_certificate_head head arity)
       ([(loop_head,11),(function_head,3),(traversal_head,7),(successors_head,9),
        (entry_head (),4),(cleanup_head (),5),(lookup_head,2),(regular_head,10)] @
       regular_queries))

  fun capture_heads head =
    if same_const head compilerPlannerEvalLib.block_head then
      [entry_head (),cleanup_head (),loop_head] @ metadata_heads
    else if List.exists (same_const head) metadata_heads then []
    else if same_const head lookup_head then []
    else if same_const head compilerPlannerEvalLib.inst_head then [regular_head]
    else if same_const head regular_head then map fst regular_queries @ [lookup_head]
    else if List.exists (fn (query,_) => same_const head query) regular_queries then []
    else if same_const head (entry_head ()) then [compilerPlannerEvalLib.params_head]
    else if same_const head (cleanup_head ()) then [compilerPlannerEvalLib.cleanup_head]
    else if same_const head loop_head then
      [compilerPlannerEvalLib.inst_head,loop_head]
    else if same_const head function_head then [traversal_head]
    else if same_const head traversal_head then
      [compilerPlannerEvalLib.block_head,traversal_head,successors_head,lookup_head]
    else if same_const head successors_head then [traversal_head,successors_head]
    else let val captures = compilerPlannerEvalLib.capture_heads head
      in if length captures = 1 andalso
          same_const (hd captures) compilerPlannerEvalLib.block_head
        then [function_head] else captures end

  fun warm_step goal = compilerPlannerEvalLib.warm_step_with capture_heads goal
end
