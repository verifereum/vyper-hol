(*
 * FCG Analysis Correctness
 *
 * Top-level soundness and completeness of the FCG analysis.
 * Uses DFS invariants from fcgAnalysisDfs to prove properties
 * of fcg_analyze.
 *
 * TOP-LEVEL theorems:
 *   fcg_analyze_reachable_in_context     - reachable => in context
 *   fcg_analyze_callees_in_context       - callees => in context
 *   fcg_analyze_reachable_distinct       - reachable list is distinct
 *   fcg_analyze_callees_sound            - callees => fn_directly_calls
 *   fcg_analyze_callees_complete         - fn_directly_calls => callees
 *   fcg_analyze_callees_distinct         - callee lists are distinct
 *   fcg_analyze_call_sites_sound         - recorded => real INVOKE
 *   fcg_analyze_call_sites_complete      - real INVOKE => recorded
 *   fcg_analyze_reachable_sound          - reachable => fcg_path
 *   fcg_analyze_reachable_complete       - fcg_path => reachable
 *   fcg_analyze_no_entry                 - NONE entry => nothing reachable
 *   fcg_analyze_no_entry_callees         - NONE entry => callees empty
 *   fcg_analyze_no_entry_call_sites      - NONE entry => call sites empty
 *   fcg_analyze_no_entry_unreachable     - NONE entry => all unreachable
 *   fcg_analyze_unreachable_correct      - unreachable = complement
 *)

Theory fcgAnalysisCorrectness
Ancestors
  fcgAnalysisDfs fcgAnalysisDefs fcgAnalysis venomInst relation

(* ===== Domain Invariants ===== *)

Theorem fcg_analyze_reachable_in_context:
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  MEM fn_name (ctx_fn_names ctx)
Proof
  simp[fcg_is_reachable_def, fcg_analyze_def, ctx_fn_names_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >>
  drule (SIMP_RULE (srw_ss()) [fcg_empty_def]
    (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
       fcg_dfs_reachable_in_context)) >>
  simp[]
QED

Theorem fcg_analyze_reachable_distinct:
  ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  simp[fcg_analyze_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  irule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_reachable_distinct
    |> SIMP_RULE (srw_ss()) [fcg_empty_def])
QED

(* ===== Callees Correctness ===== *)

(* Soundness: recorded callee => semantic direct call *)
Theorem fcg_analyze_callees_sound:
  wf_fn_names ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  fn_directly_calls ctx fn_name callee
Proof
  simp[fcg_analyze_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def, fcg_get_callees_def] >>
  strip_tac >>
  drule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_callees_sound
    |> SIMP_RULE (srw_ss()) [fcg_empty_def, fcg_get_callees_def]) >>
  disch_then irule
QED

(* Domain: callees are in context (needs wf_invoke_targets) *)
Theorem fcg_analyze_callees_in_context:
  wf_fn_names ctx /\
  wf_invoke_targets ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  MEM callee (ctx_fn_names ctx)
Proof
  strip_tac >>
  drule_all fcg_analyze_callees_sound >> strip_tac >>
  gvs[fn_directly_calls_def, wf_invoke_targets_def,
      ctx_fn_names_def] >>
  imp_res_tac lookup_function_MEM >>
  res_tac >> gvs[]
QED

(* Completeness: reachable + direct call => recorded callee *)
Theorem fcg_analyze_callees_complete:
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name /\
  fn_directly_calls ctx fn_name callee ==>
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >>
  drule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_callees_complete
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_callees_def]
    |> REWRITE_RULE [GSYM fcg_get_callees_def]) >>
  simp[fcg_empty_def]
QED

(* Distinctness: callee lists have no duplicates *)
Theorem fcg_analyze_callees_distinct:
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  simp[fcg_analyze_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def, fcg_get_callees_def] >>
  strip_tac >>
  irule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_callees_distinct
    |> SIMP_RULE (srw_ss()) [fcg_empty_def, fcg_get_callees_def])
QED

(* ===== Call Sites Correctness ===== *)

(* Soundness: recorded call site is a real INVOKE from a reachable caller *)
Theorem fcg_analyze_call_sites_sound:
  wf_fn_names ctx /\
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee) ==>
  ?caller func.
    fcg_is_reachable (fcg_analyze ctx) caller /\
    lookup_function caller ctx.ctx_functions = SOME func /\
    MEM inst (fn_insts func) /\
    inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label callee :: rest
Proof
  strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  Cases_on `ctx.ctx_entry`
  >- simp[fcg_empty_def, fcg_get_call_sites_def]
  >> simp[] >> strip_tac >>
  drule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_call_sites_sound
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_call_sites_def]
    |> REWRITE_RULE
         [GSYM fcg_get_call_sites_def, GSYM fcg_empty_def]) >>
  strip_tac >>
  imp_res_tac mem_scan_function_pair >>
  MAP_EVERY qexists_tac [`caller`, `func`] >> simp[]
QED

(* Completeness: every INVOKE targeting callee from a reachable caller
   is recorded *)
Theorem fcg_analyze_call_sites_complete:
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) caller /\
  lookup_function caller ctx.ctx_functions = SOME func /\
  MEM inst (fn_insts func) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: rest ==>
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >>
  `MEM (callee, inst) (fcg_scan_function func)` by
    (simp[fcg_scan_function_def] >>
     irule get_invoke_targets_intro >> simp[] >>
     metis_tac[]) >>
  drule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_call_sites_complete
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_call_sites_def]
    |> REWRITE_RULE [GSYM fcg_get_call_sites_def]) >>
  simp[fcg_empty_def]
QED

(* ===== Reachability Correctness ===== *)

(* Soundness: analysis says reachable => semantic path from entry *)
Theorem fcg_analyze_reachable_sound:
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  fcg_path ctx entry_name fn_name
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >> gvs[] >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_reachable_sound
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_path_def, relationTheory.RTC_REFL]
    |> Q.SPEC `entry_name`
    |> REWRITE_RULE [GSYM fcg_path_def, relationTheory.RTC_REFL]) >>
  simp[]
QED

(* Completeness: semantic path + in context => analysis says reachable *)
Theorem fcg_analyze_reachable_complete:
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_path ctx entry_name fn_name /\
  MEM fn_name (ctx_fn_names ctx) ==>
  fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def, fcg_path_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >> gvs[] >>
  qabbrev_tac `result = fcg_dfs ctx [entry_name] []
    <|fcg_callees := FEMPTY; fcg_call_sites := FEMPTY;
      fcg_reachable := []|>` >>
  `!fn_n. (fn_directly_calls ctx)^* entry_name fn_n ==>
     MEM fn_n (ctx_fn_names ctx) ==>
     MEM fn_n result.fcg_reachable`
    suffices_by (strip_tac >> res_tac) >>
  ho_match_mp_tac (GEN_ALL relationTheory.RTC_ALT_RIGHT_INDUCT) >>
  conj_tac
  (* Base: entry_name itself *)
  >- (strip_tac >> simp[Abbr`result`] >>
      irule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,
        `<|fcg_callees := FEMPTY; fcg_call_sites := FEMPTY;
          fcg_reachable := []|>`]
        fcg_dfs_stack_reachable |> SIMP_RULE (srw_ss()) []) >> simp[])
  (* Step: fn_n -> fn_name via fn_directly_calls *)
  >> rpt strip_tac
  >> `MEM fn_n (ctx_fn_names ctx)` by
       (gvs[fn_directly_calls_def, ctx_fn_names_def] >>
        imp_res_tac lookup_function_mem >> simp[listTheory.MEM_MAP] >>
        qexists_tac `func` >> simp[])
  >> `MEM fn_n result.fcg_reachable` by res_tac
  >> simp[Abbr`result`]
  >> drule_all (Q.SPECL [`ctx`,`[entry_name]`,`[]`,
       `<|fcg_callees := FEMPTY; fcg_call_sites := FEMPTY;
         fcg_reachable := []|>`]
       fcg_dfs_reachable_closed |> SIMP_RULE (srw_ss()) [])
  >> simp[]
QED

(* ===== No-Entry Edge Cases ===== *)

Theorem fcg_analyze_no_entry:
  ctx.ctx_entry = NONE ==>
  ~fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def, fcg_empty_def]
QED

Theorem fcg_analyze_no_entry_callees:
  ctx.ctx_entry = NONE ==>
  fcg_get_callees (fcg_analyze ctx) fn_name = []
Proof
  simp[fcg_analyze_def, fcg_get_callees_def, fcg_empty_def]
QED

Theorem fcg_analyze_no_entry_call_sites:
  ctx.ctx_entry = NONE ==>
  fcg_get_call_sites (fcg_analyze ctx) fn_name = []
Proof
  simp[fcg_analyze_def, fcg_get_call_sites_def, fcg_empty_def]
QED

Theorem fcg_analyze_no_entry_unreachable:
  ctx.ctx_entry = NONE ==>
  fcg_get_unreachable ctx (fcg_analyze ctx) = ctx.ctx_functions
Proof
  simp[fcg_analyze_def, fcg_get_unreachable_def, fcg_empty_def]
QED

(* ===== Unreachable Correctness ===== *)

(* Unreachable = complement of reachable within context functions *)
Theorem fcg_analyze_unreachable_correct:
  MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
  MEM func ctx.ctx_functions /\
  ~fcg_is_reachable (fcg_analyze ctx) func.fn_name
Proof
  simp[fcg_get_unreachable_def, fcg_is_reachable_def,
       listTheory.MEM_FILTER] >>
  metis_tac[]
QED

val _ = export_theory();
