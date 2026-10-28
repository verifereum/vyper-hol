(* Eliminate a successor's checked branch result before its continuation. *)
Theory stackPlanTraversalCases
Ancestors stackPlanGen

val successor_step = List.nth(CONJUNCTS(SPEC_ALL generate_fn_plan_aux_def),3)
val function_empty = List.nth(CONJUNCTS(SPEC_ALL generate_fn_plan_aux_def),0)
val function_step = List.nth(CONJUNCTS(SPEC_ALL generate_fn_plan_aux_def),1)

Theorem generate_succs_plan_some:
  generate_fn_plan_aux liveness dfg cfg func [succ] visited
      (ps with <|ps_stack := saved_stack; ps_spilled := saved_spilled|>) =
    SOME (branch_ops,visited1,ps1) ==>
  generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
      (succ::rest) visited ps =
    case generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
        rest visited1
        (ps with <|ps_alloc := ps1.ps_alloc; ps_label_counter := ps1.ps_label_counter|>) of
      NONE => NONE
    | SOME (rest_ops,visited2,ps2) => SOME (branch_ops ++ rest_ops,visited2,ps2)
Proof
  strip_tac >> simp[Once successor_step,LET_THM]
QED

Theorem generate_succs_plan_none:
  generate_fn_plan_aux liveness dfg cfg func [succ] visited
      (ps with <|ps_stack := saved_stack; ps_spilled := saved_spilled|>) = NONE ==>
  generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
      (succ::rest) visited ps = NONE
Proof
  strip_tac >> simp[Once successor_step,LET_THM]
QED

Theorem generate_fn_plan_aux_singleton_visited:
  MEM label visited ==>
  generate_fn_plan_aux liveness dfg cfg func [label] visited ps =
    SOME ([],visited,ps)
Proof
  strip_tac >> simp[Once function_step,function_empty,LET_THM]
QED

Theorem generate_fn_plan_aux_singleton_missing:
  ~MEM label visited /\ lookup_block label func.fn_blocks = NONE ==>
  generate_fn_plan_aux liveness dfg cfg func [label] visited ps =
    SOME ([],label::visited,ps)
Proof
  strip_tac >> simp[Once function_step,function_empty,LET_THM]
QED

Theorem generate_fn_plan_aux_singleton_some:
  ~MEM label visited /\ lookup_block label func.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg func bb ps = SOME (block_ops,ps1) ==>
  generate_fn_plan_aux liveness dfg cfg func [label] visited ps =
    case generate_succs_plan liveness dfg cfg func ps1.ps_stack ps1.ps_spilled
        (cfg_succs_of cfg label) (label::visited) ps1 of
      NONE => NONE
    | SOME (succ_ops,visited1,ps2) => SOME (block_ops ++ succ_ops,visited1,ps2)
Proof
  strip_tac >> simp[Once function_step,function_empty,LET_THM]
QED

Theorem generate_fn_plan_aux_singleton_none:
  ~MEM label visited /\ lookup_block label func.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg func bb ps = NONE ==>
  generate_fn_plan_aux liveness dfg cfg func [label] visited ps = NONE
Proof
  strip_tac >> simp[Once function_step,function_empty,LET_THM]
QED
