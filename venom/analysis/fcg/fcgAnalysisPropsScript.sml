(*
 * FCG Analysis Correctness (Statements Only)
 *
 * We structure the statements in five layers:
 *
 * 1) Bridge lemma
 *    - fn_directly_calls is equivalent to fcg_scan_function membership.
 *
 * 2) Domain invariants
 *    - Reachable names and callees belong to the context's function names.
 *    - Reachable list has no duplicates.
 *
 * 3) Callees correctness
 *    - Callee lists are sound and complete w.r.t. fn_directly_calls.
 *    - Callee lists have no duplicates.
 *
 * 4) Call sites correctness
 *    - Recorded call sites are sound and complete w.r.t. actual INVOKEs.
 *
 * 5) Reachability correctness
 *    - fcg_is_reachable coincides with fcg_path (RTC of fn_directly_calls).
 *
 * 6) No-entry edge cases
 *    - When ctx_entry = NONE, nothing is reachable, no callees/sites recorded.
 *
 * 7) Unreachable correctness
 *    - fcg_get_unreachable is exactly the complement of reachable.
 *
 * Proofs live in fcgCorrectnessProofScript.sml; this file re-exports
 * via ACCEPT_TAC.
 *)

Theory fcgAnalysisProps
Ancestors
  fcgCorrectnessProof

(* ==========================================================================
   1) Bridge lemma
   ========================================================================== *)

(* The semantic direct-call relation (fn_directly_calls) is equivalent to
 * membership in the scan result: fn_a directly calls fn_b iff fn_b appears
 * as a target in fcg_scan_function applied to fn_a's function body. *)
Theorem fn_directly_calls_scan:
  fn_directly_calls ctx fn_a fn_b <=>
  ?func. lookup_function fn_a ctx.ctx_functions = SOME func /\
         MEM fn_b (MAP FST (fcg_scan_function func))
Proof
  ACCEPT_TAC fn_directly_calls_scan_proof
QED

(* ==========================================================================
   2) Domain invariants
   ========================================================================== *)

(* Any function name marked reachable by fcg_analyze belongs to the
 * context's function list. *)
Theorem fcg_analyze_reachable_in_context:
  !ctx fn_name.
    wf_fn_names ctx /\
    fcg_is_reachable (fcg_analyze ctx) fn_name ==>
    MEM fn_name (ctx_fn_names ctx)
Proof
  ACCEPT_TAC fcg_analyze_reachable_in_context_proof
QED

(* Every callee recorded by fcg_analyze names a function in the context.
 * Requires wf_invoke_targets (INVOKE operands are valid Labels). *)
Theorem fcg_analyze_callees_in_context:
  !ctx fn_name callee.
    wf_fn_names ctx /\
    wf_invoke_targets ctx /\
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
    MEM callee (ctx_fn_names ctx)
Proof
  ACCEPT_TAC fcg_analyze_callees_in_context_proof
QED

(* The reachable list produced by fcg_analyze contains no duplicates. *)
Theorem fcg_analyze_reachable_distinct:
  !ctx.
    wf_fn_names ctx ==>
    ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  ACCEPT_TAC fcg_analyze_reachable_distinct_proof
QED

(* ==========================================================================
   3) Callees correctness
   ========================================================================== *)

(* Soundness: if callee is recorded as a callee of fn_name, then
 * fn_name directly calls callee (via an INVOKE instruction). *)
Theorem fcg_analyze_callees_sound:
  !ctx fn_name callee.
    wf_fn_names ctx /\
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
    fn_directly_calls ctx fn_name callee
Proof
  ACCEPT_TAC fcg_analyze_callees_sound_proof
QED

(* Completeness: if fn_name is reachable and directly calls callee,
 * then callee appears in the recorded callee list. *)
Theorem fcg_analyze_callees_complete:
  !ctx fn_name callee.
    wf_fn_names ctx /\
    fcg_is_reachable (fcg_analyze ctx) fn_name /\
    fn_directly_calls ctx fn_name callee ==>
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  ACCEPT_TAC fcg_analyze_callees_complete_proof
QED

(* The callee list for any function has no duplicates. *)
Theorem fcg_analyze_callees_distinct:
  !ctx fn_name.
    wf_fn_names ctx ==>
    ALL_DISTINCT (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  ACCEPT_TAC fcg_analyze_callees_distinct_proof
QED

(* ==========================================================================
   4) Call sites correctness
   ========================================================================== *)

(* Soundness: every recorded call site for callee is an actual INVOKE
 * instruction in some reachable caller's function body. *)
Theorem fcg_analyze_call_sites_sound:
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
  ACCEPT_TAC fcg_analyze_call_sites_sound_proof
QED

(* Completeness: every INVOKE instruction targeting callee from a
 * reachable caller is recorded in the call sites list. *)
Theorem fcg_analyze_call_sites_complete:
  !ctx caller callee func inst rest.
    wf_fn_names ctx /\
    fcg_is_reachable (fcg_analyze ctx) caller /\
    lookup_function caller ctx.ctx_functions = SOME func /\
    MEM inst (fn_insts func) /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee :: rest ==>
    MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  ACCEPT_TAC fcg_analyze_call_sites_complete_proof
QED

(* ==========================================================================
   5) Reachability correctness
   ========================================================================== *)

(* Soundness: if the analysis marks fn_name reachable, then there is a
 * path of direct calls from the entry function to fn_name. *)
Theorem fcg_analyze_reachable_sound:
  !ctx entry_name fn_name.
    wf_fn_names ctx /\
    ctx.ctx_entry = SOME entry_name /\
    fcg_is_reachable (fcg_analyze ctx) fn_name ==>
    fcg_path ctx entry_name fn_name
Proof
  ACCEPT_TAC fcg_analyze_reachable_sound_proof
QED

(* Completeness: if there is a path of direct calls from entry to fn_name
 * and fn_name is in the context, then the analysis marks it reachable. *)
Theorem fcg_analyze_reachable_complete:
  !ctx entry_name fn_name.
    wf_fn_names ctx /\
    ctx.ctx_entry = SOME entry_name /\
    fcg_path ctx entry_name fn_name /\
    MEM fn_name (ctx_fn_names ctx) ==>
    fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  ACCEPT_TAC fcg_analyze_reachable_complete_proof
QED

(* ==========================================================================
   6) No-entry edge cases
   ========================================================================== *)

(* When no entry function exists, nothing is reachable. *)
Theorem fcg_analyze_no_entry:
  !ctx fn_name.
    ctx.ctx_entry = NONE ==>
    ~fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  ACCEPT_TAC fcg_analyze_no_entry_proof
QED

(* When no entry function exists, no callees are recorded. *)
Theorem fcg_analyze_no_entry_callees:
  !ctx fn_name.
    ctx.ctx_entry = NONE ==>
    fcg_get_callees (fcg_analyze ctx) fn_name = []
Proof
  ACCEPT_TAC fcg_analyze_no_entry_callees_proof
QED

(* When no entry function exists, no call sites are recorded. *)
Theorem fcg_analyze_no_entry_call_sites:
  !ctx fn_name.
    ctx.ctx_entry = NONE ==>
    fcg_get_call_sites (fcg_analyze ctx) fn_name = []
Proof
  ACCEPT_TAC fcg_analyze_no_entry_call_sites_proof
QED

(* When no entry function exists, every function is unreachable. *)
Theorem fcg_analyze_no_entry_unreachable:
  !ctx.
    ctx.ctx_entry = NONE ==>
    fcg_get_unreachable ctx (fcg_analyze ctx) = ctx.ctx_functions
Proof
  ACCEPT_TAC fcg_analyze_no_entry_unreachable_proof
QED

(* ==========================================================================
   7) Unreachable correctness
   ========================================================================== *)

(* A function is in the unreachable list iff it is in the context and
 * the analysis does not mark it reachable. *)
Theorem fcg_analyze_unreachable_correct:
  !ctx func.
    wf_fn_names ctx ==>
    (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
     MEM func ctx.ctx_functions /\
     ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  ACCEPT_TAC fcg_analyze_unreachable_correct_proof
QED
