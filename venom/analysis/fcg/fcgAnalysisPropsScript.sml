(*
 * FCG Analysis Correctness (Statements Only)
 *
 * Structured in five layers:
 *
 * 1) Domain invariants
 *    - Reachable names and callees belong to the context's function names.
 *    - Reachable list has no duplicates.
 *
 * 2) Callees correctness
 *    - Callee lists are sound and complete w.r.t. fn_directly_calls.
 *
 * 3) Call sites correctness
 *    - Recorded call sites are sound and complete w.r.t. actual INVOKEs.
 *    - Call site lists have no duplicates.
 *
 * 4) Reachability correctness
 *    - fcg_is_reachable coincides with fcg_path (RTC of fn_directly_calls).
 *
 * 5) Unreachable correctness
 *    - fcg_get_unreachable is exactly the complement of reachable.
 *
 * Proofs live in fcgCorrectnessProofScript.sml; this file re-exports
 * via ACCEPT_TAC.
 *)

Theory fcgAnalysisProps
Ancestors
  fcgCorrectnessProof

(* ==========================================================================
   1) Domain invariants
   ========================================================================== *)

(* Any function name marked reachable by fcg_analyze belongs to the
 * context's function list. *)
Theorem fcg_analyze_reachable_in_context:
  !ctx fn_name.
    ctx_wf ctx /\
    fcg_is_reachable (fcg_analyze ctx) fn_name ==>
    MEM fn_name (ctx_fn_names ctx)
Proof
  ACCEPT_TAC fcg_analyze_reachable_in_context_proof
QED

(* Every callee recorded by fcg_analyze names a function in the context.
 * Requires wf_invoke_targets (INVOKE operands are valid Labels). *)
Theorem fcg_analyze_callees_in_context:
  !ctx fn_name callee.
    ctx_wf ctx /\
    wf_invoke_targets ctx /\
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
    MEM callee (ctx_fn_names ctx)
Proof
  ACCEPT_TAC fcg_analyze_callees_in_context_proof
QED

(* The reachable list produced by fcg_analyze contains no duplicates. *)
Theorem fcg_analyze_reachable_distinct:
  !ctx.
    ctx_wf ctx ==>
    ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  ACCEPT_TAC fcg_analyze_reachable_distinct_proof
QED

(* ==========================================================================
   2) Callees correctness
   ========================================================================== *)

(* Soundness: if callee is recorded as a callee of fn_name, then
 * fn_name directly calls callee (via an INVOKE instruction). *)
Theorem fcg_analyze_callees_sound:
  !ctx fn_name callee.
    ctx_wf ctx /\
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
    fn_directly_calls ctx fn_name callee
Proof
  ACCEPT_TAC fcg_analyze_callees_sound_proof
QED

(* Completeness: if fn_name is reachable and directly calls callee,
 * then callee appears in the recorded callee list. *)
Theorem fcg_analyze_callees_complete:
  !ctx fn_name callee.
    ctx_wf ctx /\
    fcg_is_reachable (fcg_analyze ctx) fn_name /\
    fn_directly_calls ctx fn_name callee ==>
    MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  ACCEPT_TAC fcg_analyze_callees_complete_proof
QED

(* ==========================================================================
   3) Call sites correctness
   ========================================================================== *)

(* Soundness: every recorded call site for callee is an actual INVOKE
 * instruction in some reachable caller's function body. *)
Theorem fcg_analyze_call_sites_sound:
  !ctx callee inst.
    ctx_wf ctx /\
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
    ctx_wf ctx /\
    fcg_is_reachable (fcg_analyze ctx) caller /\
    lookup_function caller ctx.ctx_functions = SOME func /\
    MEM inst (fn_insts func) /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee :: rest ==>
    MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  ACCEPT_TAC fcg_analyze_call_sites_complete_proof
QED

(* The call site list for any callee has no duplicates. *)
Theorem fcg_analyze_call_sites_distinct:
  !ctx callee.
    ctx_wf ctx ==>
    ALL_DISTINCT (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  ACCEPT_TAC fcg_analyze_call_sites_distinct_proof
QED

(* ==========================================================================
   4) Reachability correctness
   ========================================================================== *)

(* Soundness: if the analysis marks fn_name reachable, then there is a
 * path of direct calls from the entry function to fn_name. *)
Theorem fcg_analyze_reachable_sound:
  !ctx fn_name.
    ctx_wf ctx /\
    fcg_is_reachable (fcg_analyze ctx) fn_name ==>
    ?entry_name. ctx.ctx_entry = SOME entry_name /\
                 fcg_path ctx entry_name fn_name
Proof
  ACCEPT_TAC fcg_analyze_reachable_sound_proof
QED

(* Completeness: if there is a path of direct calls from entry to fn_name
 * and fn_name is in the context, then the analysis marks it reachable. *)
Theorem fcg_analyze_reachable_complete:
  !ctx entry_name fn_name.
    ctx_wf ctx /\
    ctx.ctx_entry = SOME entry_name /\
    fcg_path ctx entry_name fn_name /\
    MEM fn_name (ctx_fn_names ctx) ==>
    fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  ACCEPT_TAC fcg_analyze_reachable_complete_proof
QED

(* ==========================================================================
   5) Unreachable correctness
   ========================================================================== *)

(* A function is in the unreachable list iff it is in the context and
 * the analysis does not mark it reachable. *)
Theorem fcg_analyze_unreachable_correct:
  !ctx func.
    ctx_wf ctx ==>
    (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
     MEM func ctx.ctx_functions /\
     ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  ACCEPT_TAC fcg_analyze_unreachable_correct_proof
QED
