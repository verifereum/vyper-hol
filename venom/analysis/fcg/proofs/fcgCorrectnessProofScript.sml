(*
 * FCG Analysis Correctness Proofs
 *
 * Actual proofs for theorems stated in fcgAnalysisPropsScript.
 * Currently cheated; fill in as proofs are developed.
 *)

Theory fcgCorrectnessProof
Ancestors
  fcgDefs

(* ==========================================================================
   Bridge lemma
   ========================================================================== *)

Theorem fn_directly_calls_scan_proof:
  fn_directly_calls ctx fn_a fn_b <=>
  ?func. lookup_function fn_a ctx.ctx_functions = SOME func /\
         MEM fn_b (MAP FST (fcg_scan_function func))
Proof
  cheat
QED

(* ==========================================================================
   Domain invariants
   ========================================================================== *)

Theorem fcg_analyze_reachable_in_context_proof:
  !ctx fn_name.
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  MEM fn_name (ctx_fn_names ctx)
Proof
  cheat
QED

Theorem fcg_analyze_callees_in_context_proof:
  !ctx fn_name callee.
  wf_fn_names ctx /\
  wf_invoke_targets ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  MEM callee (ctx_fn_names ctx)
Proof
  cheat
QED

Theorem fcg_analyze_reachable_distinct_proof:
  !ctx.
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  cheat
QED

(* ==========================================================================
   Callees correctness
   ========================================================================== *)

Theorem fcg_analyze_callees_sound_proof:
  !ctx fn_name callee.
  wf_fn_names ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  fn_directly_calls ctx fn_name callee
Proof
  cheat
QED

Theorem fcg_analyze_callees_complete_proof:
  !ctx fn_name callee.
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name /\
  fn_directly_calls ctx fn_name callee ==>
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  cheat
QED

Theorem fcg_analyze_callees_distinct_proof:
  !ctx fn_name.
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  cheat
QED

(* ==========================================================================
   Call sites correctness
   ========================================================================== *)

Theorem fcg_analyze_call_sites_sound_proof:
  !ctx callee inst.
  wf_fn_names ctx /\
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee) ==>
  ?caller func.
    fcg_is_reachable (fcg_analyze ctx) caller /\
    lookup_function caller ctx.ctx_functions = SOME func /\
    MEM inst (fn_insts func) /\
    inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label callee :: rest
Proof
  cheat
QED

Theorem fcg_analyze_call_sites_complete_proof:
  !ctx caller callee func inst rest.
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) caller /\
  lookup_function caller ctx.ctx_functions = SOME func /\
  MEM inst (fn_insts func) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: rest ==>
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  cheat
QED

(* ==========================================================================
   Reachability correctness
   ========================================================================== *)

Theorem fcg_analyze_reachable_sound_proof:
  !ctx entry_name fn_name.
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  fcg_path ctx entry_name fn_name
Proof
  cheat
QED

Theorem fcg_analyze_reachable_complete_proof:
  !ctx entry_name fn_name.
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_path ctx entry_name fn_name /\
  MEM fn_name (ctx_fn_names ctx) ==>
  fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  cheat
QED

(* ==========================================================================
   No-entry edge cases
   ========================================================================== *)

Theorem fcg_analyze_no_entry_proof:
  !ctx fn_name.
  ctx.ctx_entry = NONE ==>
  ~fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_callees_proof:
  !ctx fn_name.
  ctx.ctx_entry = NONE ==>
  fcg_get_callees (fcg_analyze ctx) fn_name = []
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_call_sites_proof:
  !ctx fn_name.
  ctx.ctx_entry = NONE ==>
  fcg_get_call_sites (fcg_analyze ctx) fn_name = []
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_unreachable_proof:
  !ctx.
  ctx.ctx_entry = NONE ==>
  fcg_get_unreachable ctx (fcg_analyze ctx) = ctx.ctx_functions
Proof
  cheat
QED

(* ==========================================================================
   Unreachable correctness
   ========================================================================== *)

Theorem fcg_analyze_unreachable_correct_proof:
  !ctx func.
  wf_fn_names ctx ==>
  (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
   MEM func ctx.ctx_functions /\
   ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  cheat
QED
