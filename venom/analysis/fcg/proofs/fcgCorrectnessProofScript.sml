(*
 * FCG Analysis Correctness Proofs
 *
 * Top-level soundness and completeness of the FCG analysis.
 * Uses DFS invariants from fcgDfs to prove properties of fcg_analyze.
 *
 * TOP-LEVEL theorems:
 *   fcg_analyze_reachable_in_context_proof   - reachable => in context
 *   fcg_analyze_callees_in_context_proof     - callees => in context
 *   fcg_analyze_reachable_distinct_proof     - reachable list is distinct
 *   fcg_analyze_callees_sound_proof          - callees => fn_directly_calls
 *   fcg_analyze_callees_complete_proof       - fn_directly_calls => callees
 *   fcg_analyze_call_sites_sound_proof       - recorded => real INVOKE
 *   fcg_analyze_call_sites_complete_proof    - real INVOKE => recorded
 *   fcg_analyze_call_sites_distinct_proof    - call site lists are distinct
 *   fcg_analyze_reachable_sound_proof        - reachable => fcg_path
 *   fcg_analyze_reachable_complete_proof     - fcg_path => reachable
 *   fcg_analyze_unreachable_correct_proof    - unreachable = complement
 *)

Theory fcgCorrectnessProof
Ancestors
  fcgDfs fcgBridge fcgDefs venomInst

(* Helper: unfold ctx_wf to get entry_name, then expand fcg_empty
 * everywhere and simplify. After this, both assumptions and goal
 * have the expanded fcg_dfs call. *)
fun ctx_wf_tac (g as (asms, _)) =
  (gvs[ctx_wf_def, ctx_has_entry_def] >>
   RULE_ASSUM_TAC (REWRITE_RULE [fcg_empty_def]) >>
   simp[fcg_empty_def]) g;

(* ===== Domain Invariants ===== *)

Theorem fcg_analyze_reachable_in_context_proof:
  !ctx fn_name.
  ctx_wf ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  MEM fn_name (ctx_fn_names ctx)
Proof
  simp[fcg_is_reachable_def, fcg_analyze_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  drule (SIMP_RULE (srw_ss()) [fcg_empty_def]
    (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
       fcg_dfs_reachable_in_context)) >>
  simp[]
QED

Theorem fcg_analyze_reachable_distinct_proof:
  !ctx.
  ctx_wf ctx ==>
  ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  simp[fcg_analyze_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  irule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_reachable_distinct
    |> SIMP_RULE (srw_ss()) [fcg_empty_def])
QED

(* ===== Callees Correctness ===== *)

Theorem fcg_analyze_callees_sound_proof:
  !ctx fn_name callee.
  ctx_wf ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  fn_directly_calls ctx fn_name callee
Proof
  simp[fcg_analyze_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_callees_sound
    |> SIMP_RULE (srw_ss()) [fcg_empty_def, fcg_get_callees_def]
    |> REWRITE_RULE [GSYM fcg_get_callees_def]) >>
  disch_then irule
QED

Theorem fcg_analyze_callees_in_context_proof:
  !ctx fn_name callee.
  ctx_wf ctx /\
  wf_invoke_targets ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  MEM callee (ctx_fn_names ctx)
Proof
  rpt strip_tac >>
  drule_all fcg_analyze_callees_sound_proof >> strip_tac >>
  gvs[fn_directly_calls_def, wf_invoke_targets_def,
      ctx_fn_names_def] >>
  imp_res_tac lookup_function_MEM >>
  res_tac >> gvs[]
QED

Theorem fcg_analyze_callees_complete_proof:
  !ctx fn_name callee.
  ctx_wf ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name /\
  fn_directly_calls ctx fn_name callee ==>
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_callees_complete
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_callees_def]
    |> REWRITE_RULE [GSYM fcg_get_callees_def]) >>
  simp[fcg_empty_def]
QED

(* ===== Call Sites Correctness ===== *)

Theorem fcg_analyze_call_sites_sound_proof:
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
  rpt strip_tac >>
  qpat_x_assum `MEM _ _` mp_tac >>
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  gvs[ctx_wf_def, ctx_has_entry_def] >>
  simp[fcg_empty_def] >> strip_tac >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_call_sites_sound
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_call_sites_def]
    |> REWRITE_RULE [GSYM fcg_get_call_sites_def]) >>
  strip_tac >>
  imp_res_tac mem_scan_function_pair >>
  MAP_EVERY qexists_tac [`caller`, `func`] >> simp[]
QED

Theorem fcg_analyze_call_sites_complete_proof:
  !ctx caller callee func inst rest.
  ctx_wf ctx /\
  fcg_is_reachable (fcg_analyze ctx) caller /\
  lookup_function caller ctx.ctx_functions = SOME func /\
  MEM inst (fn_insts func) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: rest ==>
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  `MEM (callee, inst) (fcg_scan_function func)` by
    (simp[fcg_scan_function_def] >>
     irule get_invoke_targets_intro >> simp[] >>
     metis_tac[]) >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_call_sites_complete
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_get_call_sites_def]
    |> REWRITE_RULE [GSYM fcg_get_call_sites_def]) >>
  simp[fcg_empty_def]
QED

Theorem fcg_analyze_call_sites_distinct_proof:
  !ctx callee.
  ctx_wf ctx ==>
  ALL_DISTINCT (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  simp[fcg_analyze_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  irule (SIMP_RULE (srw_ss()) [fcg_empty_def, fcg_get_call_sites_def]
    (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
       fcg_dfs_call_sites_distinct)
    |> REWRITE_RULE [GSYM fcg_get_call_sites_def])
QED

(* ===== Reachability Correctness ===== *)

Theorem fcg_analyze_reachable_sound_proof:
  !ctx fn_name.
  ctx_wf ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  ?entry_name. ctx.ctx_entry = SOME entry_name /\
               fcg_path ctx entry_name fn_name
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def] >>
  rpt strip_tac >> ctx_wf_tac >>
  drule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
    fcg_dfs_reachable_sound
    |> SIMP_RULE (srw_ss())
         [fcg_empty_def, fcg_path_def, relationTheory.RTC_REFL]
    |> Q.SPEC `entry_name`
    |> REWRITE_RULE [GSYM fcg_path_def, relationTheory.RTC_REFL]) >>
  simp[]
QED

Theorem fcg_analyze_reachable_complete_proof:
  !ctx entry_name fn_name.
  ctx_wf ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_path ctx entry_name fn_name /\
  MEM fn_name (ctx_fn_names ctx) ==>
  fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  simp[fcg_analyze_def, fcg_is_reachable_def, fcg_path_def] >>
  rpt strip_tac >> gvs[] >>
  simp[fcg_empty_def] >>
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
      irule (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
        fcg_dfs_stack_reachable
        |> SIMP_RULE (srw_ss()) [fcg_empty_def]) >> simp[])
  (* Step: fn_n -> fn_name via fn_directly_calls *)
  >> rpt strip_tac
  >> `MEM fn_n (ctx_fn_names ctx)` by
       (gvs[fn_directly_calls_def, ctx_fn_names_def] >>
        imp_res_tac lookup_function_mem >> simp[listTheory.MEM_MAP] >>
        qexists_tac `func` >> simp[])
  >> `MEM fn_n result.fcg_reachable` by res_tac
  >> simp[Abbr`result`]
  >> drule_all (Q.SPECL [`ctx`,`[entry_name]`,`[]`,`fcg_empty`]
       fcg_dfs_reachable_closed
       |> SIMP_RULE (srw_ss()) [fcg_empty_def])
  >> simp[]
QED

(* ===== Unreachable Correctness ===== *)

Theorem fcg_analyze_unreachable_correct_proof:
  !ctx func.
  ctx_wf ctx ==>
  (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
   MEM func ctx.ctx_functions /\
   ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  simp[fcg_get_unreachable_def, fcg_is_reachable_def,
       listTheory.MEM_FILTER] >>
  metis_tac[]
QED
