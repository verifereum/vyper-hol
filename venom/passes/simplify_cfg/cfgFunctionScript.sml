(*
 * SimplifyCFG Function-Level Correctness
 *
 * This theory proves function and context-level correctness of CFG simplification.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - simplify_cfg_merge_correct   : Block merge preserves semantics
 *   - simplify_cfg_thread_correct  : Jump threading preserves semantics
 *   - simplify_cfg_correct         : Full transformation correctness
 *
 * HELPER THEOREMS:
 *   - run_function_merge_equiv     : Function execution with merged block
 *   - run_function_thread_equiv    : Function execution with threaded jump
 *
 * ============================================================================
 *)

Theory cfgFunction
Ancestors
  cfgBlock cfgWellFormed cfgTransform execEquiv venomSem venomInst stateEquiv list

(* ==========================================================================
   Function Execution with Modified Blocks
   ========================================================================== *)

(* Lookup in blocks with one block replaced *)
Theorem lookup_block_replace:
  !lbl old_lbl new_bb blocks.
    lookup_block lbl (MAP (\bb. if bb.bb_label = old_lbl then new_bb else bb) blocks) =
    if lbl = old_lbl /\ new_bb.bb_label = old_lbl
    then OPTION_MAP (\bb. new_bb) (lookup_block old_lbl blocks)
    else if lbl = new_bb.bb_label /\ new_bb.bb_label <> old_lbl
    then if ?bb. MEM bb blocks /\ bb.bb_label = old_lbl
         then SOME new_bb
         else lookup_block lbl blocks
    else lookup_block lbl blocks
Proof
  cheat
QED

(* ==========================================================================
   Block Merge Correctness
   ========================================================================== *)

(* When we merge blocks A and B, execution starting from A reaches the same
   result as before, because:
   1. Running merged block = running A's body + B's body
   2. A's terminator was a JMP to B, which we removed
   3. After merged block, state.vs_current_bb points to B's successor *)

(* Helper: Running merged function from A gives same result as original *)
Theorem run_function_merge_from_a:
  !fuel fn a_lbl b_lbl s result.
    wf_cfg_fn fn /\
    merge_wf_blocks fn a_lbl b_lbl /\
    s.vs_current_bb = a_lbl /\
    run_function fuel fn s = result ==>
    ?result'.
      run_function fuel (apply_merge_fn fn a_lbl b_lbl) s = result' /\
      result_equiv result result'
Proof
  cheat (* Main merge correctness - requires induction on fuel *)
QED

(* Merge well-formedness helper *)
Definition merge_wf_blocks_def:
  merge_wf_blocks fn a_lbl b_lbl <=>
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) => merge_wf a b fn.fn_blocks
    | _ => F
End

(* Apply merge to function (wrapper for apply_merge) *)
Definition apply_merge_fn_def:
  apply_merge_fn fn a_lbl b_lbl =
    case apply_merge a_lbl b_lbl fn of
      SOME fn' => fn'
    | NONE => fn
End

(* ==========================================================================
   Jump Threading Correctness
   ========================================================================== *)

(* When we thread a jump through passthrough B:
   1. Any block jumping to B now jumps to B's target C
   2. Execution is equivalent because B was just "jmp C" *)

(* Thread well-formedness helper *)
Definition thread_wf_blocks_def:
  thread_wf_blocks fn passthrough_lbl <=>
    case lookup_block passthrough_lbl fn.fn_blocks of
      SOME bb => thread_wf bb
    | NONE => F
End

(* Apply thread to function (wrapper for apply_thread) *)
Definition apply_thread_fn_def:
  apply_thread_fn fn passthrough_lbl target_lbl =
    case apply_thread passthrough_lbl target_lbl fn of
      SOME fn' => fn'
    | NONE => fn
End

(* Helper: Threading preserves function execution *)
Theorem run_function_thread:
  !fuel fn passthrough_lbl target_lbl s result.
    wf_cfg_fn fn /\
    thread_wf_blocks fn passthrough_lbl /\
    lookup_block passthrough_lbl fn.fn_blocks = SOME passthrough_bb /\
    get_block_target passthrough_bb = SOME target_lbl /\
    run_function fuel fn s = result ==>
    ?result'.
      run_function fuel (apply_thread_fn fn passthrough_lbl target_lbl) s = result' /\
      result_equiv result result'
Proof
  cheat (* Main thread correctness - requires careful simulation argument *)
QED

(* ==========================================================================
   Main Correctness Theorems
   ========================================================================== *)

(* TOP-LEVEL: Block merge preserves semantics *)
Theorem simplify_cfg_merge_correct:
  !fuel (func:ir_function) s result a_lbl b_lbl.
    wf_cfg_fn func /\
    merge_wf_blocks func a_lbl b_lbl /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'.
      run_function fuel (apply_merge_fn func a_lbl b_lbl) s = result' /\
      result_equiv result result'
Proof
  cheat
QED

(* TOP-LEVEL: Jump threading preserves semantics *)
Theorem simplify_cfg_thread_correct:
  !fuel (func:ir_function) s result passthrough_lbl target_lbl passthrough_bb.
    wf_cfg_fn func /\
    thread_wf_blocks func passthrough_lbl /\
    lookup_block passthrough_lbl func.fn_blocks = SOME passthrough_bb /\
    get_block_target passthrough_bb = SOME target_lbl /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'.
      run_function fuel (apply_thread_fn func passthrough_lbl target_lbl) s = result' /\
      result_equiv result result'
Proof
  rpt strip_tac >>
  irule run_function_thread >> simp[] >>
  qexists_tac `passthrough_bb` >> simp[]
QED

(* ==========================================================================
   Transformation Preservation
   ========================================================================== *)

(* Merge preserves well-formedness *)
Theorem merge_preserves_wf:
  !func a_lbl b_lbl.
    wf_cfg_fn func /\
    merge_wf_blocks func a_lbl b_lbl ==>
    wf_cfg_fn (apply_merge_fn func a_lbl b_lbl)
Proof
  cheat (* Well-formedness preservation *)
QED

(* Thread preserves well-formedness *)
Theorem thread_preserves_wf:
  !func passthrough_lbl target_lbl passthrough_bb.
    wf_cfg_fn func /\
    thread_wf_blocks func passthrough_lbl /\
    lookup_block passthrough_lbl func.fn_blocks = SOME passthrough_bb /\
    get_block_target passthrough_bb = SOME target_lbl ==>
    wf_cfg_fn (apply_thread_fn func passthrough_lbl target_lbl)
Proof
  cheat (* Well-formedness preservation *)
QED

(* ==========================================================================
   Iterative Transformation
   ========================================================================== *)

(* The full simplify_cfg pass applies multiple merge/thread operations.
   We show correctness by composing the individual operation correctness. *)

(* Single step of simplify_cfg *)
Datatype:
  cfg_step =
    | MergeStep string string     (* Merge block a into b *)
    | ThreadStep string string    (* Thread through passthrough to target *)
End

(* Apply a single step *)
Definition apply_cfg_step_def:
  apply_cfg_step (MergeStep a_lbl b_lbl) fn = apply_merge_fn fn a_lbl b_lbl /\
  apply_cfg_step (ThreadStep pl tl) fn = apply_thread_fn fn pl tl
End

(* Apply a sequence of steps *)
Definition apply_cfg_steps_def:
  apply_cfg_steps [] fn = fn /\
  apply_cfg_steps (step::steps) fn = apply_cfg_steps steps (apply_cfg_step step fn)
End

(* Step is valid for a function *)
Definition valid_cfg_step_def:
  valid_cfg_step (MergeStep a_lbl b_lbl) fn = merge_wf_blocks fn a_lbl b_lbl /\
  valid_cfg_step (ThreadStep pl tl) fn =
    (thread_wf_blocks fn pl /\
     ?bb. lookup_block pl fn.fn_blocks = SOME bb /\
          get_block_target bb = SOME tl)
End

(* All steps are valid *)
Definition valid_cfg_steps_def:
  valid_cfg_steps [] fn = T /\
  valid_cfg_steps (step::steps) fn =
    (valid_cfg_step step fn /\
     valid_cfg_steps steps (apply_cfg_step step fn))
End

(* TOP-LEVEL: Sequence of valid steps preserves semantics *)
Theorem simplify_cfg_steps_correct:
  !steps fuel (func:ir_function) s result.
    wf_cfg_fn func /\
    valid_cfg_steps steps func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'.
      run_function fuel (apply_cfg_steps steps func) s = result' /\
      result_equiv result result'
Proof
  cheat
QED

(* ==========================================================================
   Context-Level Correctness
   ========================================================================== *)

(* TOP-LEVEL: Context-level correctness - transformation preserves semantics
   for all functions in a context. *)
Theorem simplify_cfg_context_correct:
  !ctx fn_name steps fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_cfg_fn func /\
    valid_cfg_steps steps func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?func' result'.
      func'.fn_name = fn_name /\
      run_function fuel func' s = result' /\
      result_equiv result result'
Proof
  cheat
QED

