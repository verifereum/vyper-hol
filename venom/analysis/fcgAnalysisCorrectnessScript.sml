(*
 * FCG Analysis Correctness Statements
 *
 * Theorem statements characterizing soundness and completeness
 * of the FCG analysis, with cheated proofs as scaffolding.
 *
 * TOP-LEVEL definitions:
 *   ctx_fn_names          - convenience: function names in context
 *   wf_fn_names           - well-formedness: distinct names, entry valid
 *   wf_invoke_targets     - well-formedness: INVOKE targets are valid
 *   fn_directly_calls     - semantic direct-call relation
 *   fcg_path              - reachability via RTC of direct calls
 *
 * TOP-LEVEL theorems (all cheated):
 *   fn_directly_calls_scan               - bridge to get_invoke_targets
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
  fcgAnalysis relation
Libs
  venomInstTheory

(* ==========================================================================
   Section 0: Convenience Helper
   ========================================================================== *)

Definition ctx_fn_names_def:
  ctx_fn_names ctx = MAP (\f. f.fn_name) ctx.ctx_functions
End

(* ==========================================================================
   Section 1: Well-Formedness Predicates

   Most theorems assume only wf_fn_names (distinct names, valid entry).
   wf_invoke_targets is stronger and only needed by
   fcg_analyze_callees_in_context, which must know that INVOKE targets
   name real functions in the context. Each theorem uses the minimal
   precondition it actually requires.
   ========================================================================== *)

Definition wf_fn_names_def:
  wf_fn_names ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\
    (!entry_name. ctx.ctx_entry = SOME entry_name ==>
       MEM entry_name (ctx_fn_names ctx))
End

Definition wf_invoke_targets_def:
  wf_invoke_targets ctx <=>
    (!func inst.
       MEM func ctx.ctx_functions /\
       MEM inst (fn_insts func) /\
       inst.inst_opcode = INVOKE ==>
       ?lbl rest. inst.inst_operands = Label lbl :: rest /\
                  MEM lbl (ctx_fn_names ctx))
End

(* ==========================================================================
   Section 2: Semantic Relation via RTC
   ========================================================================== *)

(* Direct call edge: fn_a has an INVOKE instruction targeting fn_b.
   Defined purely from instruction structure — no analysis functions. *)
Definition fn_directly_calls_def:
  fn_directly_calls ctx fn_a fn_b <=>
    ?func inst rest.
      lookup_function fn_a ctx.ctx_functions = SOME func /\
      MEM inst (fn_insts func) /\
      inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label fn_b :: rest
End

(* Reachability = reflexive-transitive closure of direct calls *)
Definition fcg_path_def:
  fcg_path ctx = RTC (fn_directly_calls ctx)
End

(* Helper: lookup_function success implies the function is in the list *)
Theorem lookup_function_mem_func:
  lookup_function name fns = SOME func ==> MEM func fns
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >> Cases_on `h.fn_name = name` >> gvs[]
QED

(* Helper: if name is in the function name list, lookup succeeds *)
Theorem lookup_function_mem_name:
  MEM name (MAP (\f. f.fn_name) fns) ==>
  ?func. lookup_function name fns = SOME func
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.fn_name = name` >> gvs[]
QED

(* ==========================================================================
   Section 3: Bridge Lemma — connects semantic spec to analysis impl
   ========================================================================== *)

(* Helper: MEM pair in get_invoke_targets => instruction properties *)
Theorem mem_get_invoke_targets_pair:
  !insts callee inst.
    MEM (callee, inst) (get_invoke_targets insts) ==>
    MEM inst insts /\ inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label callee :: rest
Proof
  Induct >> simp[get_invoke_targets_def]
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum `MEM _ _` mp_tac
  >> simp[Once get_invoke_targets_def]
  >> Cases_on `h.inst_opcode` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> Cases_on `h.inst_operands` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> rename1 `op :: ops`
  >> Cases_on `op` >> simp[]
  >> TRY (strip_tac >> res_tac >> simp[] >> NO_TAC)
  >> strip_tac >> gvs[]
  >> TRY (res_tac >> simp[])
  >> metis_tac[]
QED

(* Corollary: MEM pair in fcg_scan_function => instruction properties *)
Theorem mem_scan_function_pair:
  MEM (callee, inst) (fcg_scan_function func) ==>
  MEM inst (fn_insts func) /\ inst.inst_opcode = INVOKE /\
  ?rest. inst.inst_operands = Label callee :: rest
Proof
  simp[fcg_scan_function_def] >>
  metis_tac[mem_get_invoke_targets_pair]
QED

(* Helper: non-INVOKE instructions are skipped *)
Theorem get_invoke_targets_skip:
  h.inst_opcode <> INVOKE ==>
  get_invoke_targets (h::rest) = get_invoke_targets rest
Proof
  strip_tac >> simp[Once get_invoke_targets_def] >>
  Cases_on `h.inst_opcode` >> gvs[]
QED

(* Helper: characterizes MEM in MAP FST of get_invoke_targets *)
Theorem mem_get_invoke_targets:
  MEM name (MAP FST (get_invoke_targets insts)) <=>
  ?inst rest. MEM inst insts /\
              inst.inst_opcode = INVOKE /\
              inst.inst_operands = Label name :: rest
Proof
  Induct_on `insts`
  >- simp[get_invoke_targets_def]
  >> rpt gen_tac
  >> reverse (Cases_on `h.inst_opcode = INVOKE`)
  >- (simp[get_invoke_targets_skip] >> metis_tac[])
  >> simp[Once get_invoke_targets_def]
  >> Cases_on `h.inst_operands`
  >- (simp[] >> eq_tac >> strip_tac >> gvs[] >> metis_tac[])
  >> rename1 `op :: ops`
  >> Cases_on `op` >> simp[]
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Key equivalence: the raw-instruction definition of fn_directly_calls
   is equivalent to the analysis's fcg_scan_function / get_invoke_targets.
   This is the only place that bridges semantics to implementation. *)
Theorem fn_directly_calls_scan:
  fn_directly_calls ctx fn_a fn_b <=>
  ?func. lookup_function fn_a ctx.ctx_functions = SOME func /\
         MEM fn_b (MAP FST (fcg_scan_function func))
Proof
  simp[fn_directly_calls_def, fcg_scan_function_def,
       mem_get_invoke_targets] >>
  metis_tac[]
QED

(* ==========================================================================
   Section 3.5: Structural helpers for fcg_record_edges / fcg_visit / fcg_dfs
   ========================================================================== *)

(* fcg_record_edges does not change fcg_reachable *)
Theorem fcg_record_edges_reachable:
  !fn_name targets fcg.
    (fcg_record_edges fn_name targets fcg).fcg_reachable =
    fcg.fcg_reachable
Proof
  Induct_on `targets`
  >- simp[fcg_record_edges_def]
  >> Cases >> simp[fcg_record_edges_def]
QED

(* fcg_visit: reachable grows by at most fn_name (when in context) *)
Theorem fcg_visit_reachable:
  !x. MEM x (SND (fcg_visit ctx fn_name fcg)).fcg_reachable ==>
      MEM x fcg.fcg_reachable \/
      (x = fn_name /\
       MEM fn_name (MAP (\f. f.fn_name) ctx.ctx_functions))
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >> simp[] >>
  strip_tac >> imp_res_tac lookup_function_mem >>
  gvs[rich_listTheory.SNOC_APPEND, fcg_record_edges_reachable] >>
  metis_tac[]
QED

(* fcg_visit: reachable list after visit *)
Theorem fcg_visit_reachable_eq:
  (SND (fcg_visit ctx fn_name fcg)).fcg_reachable =
  (case lookup_function fn_name ctx.ctx_functions of
     NONE => fcg.fcg_reachable
   | SOME _ => SNOC fn_name fcg.fcg_reachable)
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[fcg_record_edges_reachable]
QED

(* fcg_dfs: all reachable names were either already reachable or are
   in ctx_fn_names *)
Theorem fcg_dfs_reachable_in_context:
  !ctx stack visited fcg.
    (!x. MEM x fcg.fcg_reachable ==>
         MEM x (MAP (\f. f.fn_name) ctx.ctx_functions)) ==>
    (!x. MEM x (fcg_dfs ctx stack visited fcg).fcg_reachable ==>
         MEM x (MAP (\f. f.fn_name) ctx.ctx_functions))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  (* Base: empty stack *)
  >> simp[fcg_dfs_def]
  (* Step: fn_name::stack *)
  >> rpt strip_tac >> pop_assum mp_tac
  >> simp[Once fcg_dfs_def]
  >> Cases_on `MEM fn_name visited` >> simp[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> simp[]
  >> strip_tac
  >> first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[]
  >> disch_then irule >> simp[]
  >> rpt strip_tac
  >> `MEM x' (SND (fcg_visit ctx fn_name fcg)).fcg_reachable`
       by gvs[]
  >> drule fcg_visit_reachable >> strip_tac >> gvs[]
QED

(* fcg_record_edges: callees for fn_name = old callees + MAP FST targets *)
Theorem fcg_record_edges_callees_same:
  !fn_name targets fcg callee.
    MEM callee (fcg_get_callees
      (fcg_record_edges fn_name targets fcg) fn_name) <=>
    MEM callee (fcg_get_callees fcg fn_name) \/
    MEM callee (MAP FST targets)
Proof
  Induct_on `targets`
  >- simp[fcg_record_edges_def]
  >> Cases >> rpt gen_tac
  >> rename1 `(callee_name, inst)`
  >> once_rewrite_tac[fcg_record_edges_def] >> simp[]
  >> pop_assum (fn ih =>
       simp[fcg_get_callees_def,
            finite_mapTheory.FLOOKUP_UPDATE,
            listTheory.MEM_SNOC] >>
       simp[GSYM fcg_get_callees_def, ih])
  >> Cases_on `MEM callee_name (fcg_get_callees fcg fn_name)`
  >> gvs[]
  >> eq_tac >> rw[] >> gvs[]
QED

(* fcg_record_edges: callees for other functions are unchanged *)
Theorem fcg_record_edges_callees_other:
  !fn_name targets fcg other.
    other <> fn_name ==>
    fcg_get_callees (fcg_record_edges fn_name targets fcg) other =
    fcg_get_callees fcg other
Proof
  Induct_on `targets` >> simp[fcg_record_edges_def] >>
  Cases >> rpt gen_tac >>
  simp[fcg_record_edges_def] >> strip_tac >>
  simp[fcg_get_callees_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* fcg_visit: callees after visit for fn_name *)
(* Updating fcg_reachable does not affect fcg_get_callees *)
Theorem fcg_get_callees_reachable_update:
  !fcg r fn_n.
    fcg_get_callees (fcg with fcg_reachable := r) fn_n =
    fcg_get_callees fcg fn_n
Proof
  simp[fcg_get_callees_def]
QED

Theorem fcg_visit_callees:
  !callee.
    MEM callee (fcg_get_callees
      (SND (fcg_visit ctx fn_name fcg)) fn_name) <=>
    MEM callee (fcg_get_callees fcg fn_name) \/
    (?func. lookup_function fn_name ctx.ctx_functions = SOME func /\
            MEM callee (MAP FST (fcg_scan_function func)))
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[fcg_record_edges_callees_same,
       fcg_get_callees_reachable_update]
QED

(* fcg_visit: callees for other functions are unchanged *)
Theorem fcg_visit_callees_other:
  other <> fn_name ==>
  fcg_get_callees (SND (fcg_visit ctx fn_name fcg)) other =
  fcg_get_callees fcg other
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[fcg_record_edges_callees_other,
       fcg_get_callees_reachable_update]
QED

(* fcg_visit: elements of FST are callees of fn_name *)
Theorem fcg_visit_fst_calls:
  MEM x (FST (fcg_visit ctx fn_name fcg)) ==>
  fn_directly_calls ctx fn_name x
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[listTheory.MEM_REVERSE, listTheory.MEM_MAP] >>
  strip_tac >> Cases_on `y` >> gvs[] >>
  simp[fn_directly_calls_scan, listTheory.MEM_MAP] >>
  qexists_tac `(q, r)` >> simp[]
QED

(* Updating fcg_reachable does not affect fcg_get_call_sites *)
Theorem fcg_get_call_sites_reachable_update:
  !fcg r fn_n.
    fcg_get_call_sites (fcg with fcg_reachable := r) fn_n =
    fcg_get_call_sites fcg fn_n
Proof
  simp[fcg_get_call_sites_def]
QED

(* fcg_record_edges: call_sites membership for a specific callee *)
Theorem fcg_record_edges_call_sites_mem:
  !fn_name targets fcg callee inst.
    MEM inst (fcg_get_call_sites
      (fcg_record_edges fn_name targets fcg) callee) <=>
    MEM inst (fcg_get_call_sites fcg callee) \/
    MEM (callee, inst) targets
Proof
  Induct_on `targets`
  >- simp[fcg_record_edges_def]
  >> Cases >> rpt gen_tac
  >> rename1 `(target_name, target_inst)`
  >> once_rewrite_tac[fcg_record_edges_def] >> simp[]
  >> pop_assum (fn ih =>
       simp[fcg_get_call_sites_def,
            finite_mapTheory.FLOOKUP_UPDATE,
            listTheory.MEM_SNOC] >>
       simp[GSYM fcg_get_call_sites_def, ih])
  >> Cases_on `callee = target_name` >> gvs[]
  >> eq_tac >> rw[] >> gvs[fcg_get_call_sites_def]
QED

(* fcg_record_edges: call_sites for non-target callees unchanged *)
Theorem fcg_record_edges_call_sites_other:
  !fn_name targets fcg callee.
    ~MEM callee (MAP FST targets) ==>
    fcg_get_call_sites (fcg_record_edges fn_name targets fcg) callee =
    fcg_get_call_sites fcg callee
Proof
  Induct_on `targets` >> simp[fcg_record_edges_def] >>
  Cases >> rpt gen_tac >> rename1 `(target_name, inst)` >>
  simp[fcg_record_edges_def] >> strip_tac >>
  simp[fcg_get_call_sites_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* fcg_visit: call_sites after visit *)
Theorem fcg_visit_call_sites:
  !callee inst.
    MEM inst (fcg_get_call_sites
      (SND (fcg_visit ctx fn_name fcg)) callee) <=>
    MEM inst (fcg_get_call_sites fcg callee) \/
    (?func. lookup_function fn_name ctx.ctx_functions = SOME func /\
            MEM (callee, inst) (fcg_scan_function func))
Proof
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[fcg_record_edges_call_sites_mem,
       fcg_get_call_sites_reachable_update]
QED

(* fcg_dfs: visited functions in context end up in output reachable *)
Theorem fcg_dfs_visited_reachable:
  !ctx stack visited fcg.
    (!x. MEM x visited /\
         MEM x (MAP (\f. f.fn_name) ctx.ctx_functions) ==>
         MEM x fcg.fcg_reachable) ==>
    (!x. MEM x visited /\
         MEM x (MAP (\f. f.fn_name) ctx.ctx_functions) ==>
         MEM x (fcg_dfs ctx stack visited fcg).fcg_reachable)
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> first_x_assum irule >> simp[]
  >> rpt strip_tac
  >> `r = SND (fcg_visit ctx fn_name fcg)` by simp[]
  >> pop_assum SUBST_ALL_TAC
  >> simp[fcg_visit_reachable_eq]
  >> Cases_on `lookup_function fn_name ctx.ctx_functions`
  >> simp[listTheory.MEM_SNOC]
  >> gvs[]
  >> imp_res_tac lookup_function_not_mem >> gvs[]
QED

(* fcg_dfs: callees soundness invariant *)
Theorem fcg_dfs_callees_sound:
  !ctx stack visited fcg.
    (!fn_n c. MEM c (fcg_get_callees fcg fn_n) ==>
              fn_directly_calls ctx fn_n c) ==>
    (!fn_n c. MEM c (fcg_get_callees
                (fcg_dfs ctx stack visited fcg) fn_n) ==>
              fn_directly_calls ctx fn_n c)
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> `!fn_n' c'. MEM c' (fcg_get_callees r fn_n') ==>
        fn_directly_calls ctx fn_n' c'`
       by (rpt strip_tac
           >> `r = SND (fcg_visit ctx fn_name fcg)` by simp[]
           >> pop_assum SUBST_ALL_TAC
           >> reverse (Cases_on `fn_n' = fn_name`)
           >- gvs[fcg_visit_callees_other]
           >> gvs[fcg_visit_callees]
           >> simp[fn_directly_calls_scan])
  >> gvs[]
QED

(* fcg_dfs: reachable stays ALL_DISTINCT *)
Theorem fcg_dfs_reachable_distinct:
  !ctx stack visited fcg.
    ALL_DISTINCT fcg.fcg_reachable /\
    (!x. MEM x fcg.fcg_reachable ==> MEM x visited) ==>
    ALL_DISTINCT (fcg_dfs ctx stack visited fcg).fcg_reachable
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `fcg_visit ctx fn_name fcg` >> simp[]
  >> Cases_on `MEM fn_name visited` >> simp[]
  >> first_x_assum (qspecl_then [`q`,`r`] mp_tac) >> simp[]
  >> disch_then irule
  >> `r.fcg_reachable =
      (SND (fcg_visit ctx fn_name fcg)).fcg_reachable` by simp[]
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> simp[fcg_visit_reachable_eq]
  >> Cases_on `lookup_function fn_name ctx.ctx_functions`
  >> simp[listTheory.ALL_DISTINCT_SNOC]
  >> metis_tac[]
QED

(* fcg_record_edges: preserves ALL_DISTINCT of callees for fn_name *)
Theorem fcg_record_edges_callees_distinct:
  !fn_name targets fcg.
    ALL_DISTINCT (fcg_get_callees fcg fn_name) ==>
    ALL_DISTINCT (fcg_get_callees
      (fcg_record_edges fn_name targets fcg) fn_name)
Proof
  Induct_on `targets`
  >- simp[fcg_record_edges_def]
  >> Cases >> rpt gen_tac >> rename1 `(callee, inst)`
  >> once_rewrite_tac[fcg_record_edges_def] >> simp[]
  >> strip_tac
  >> first_x_assum irule
  >> simp[fcg_get_callees_def, finite_mapTheory.FLOOKUP_UPDATE]
  >> Cases_on `MEM callee (fcg_get_callees fcg fn_name)`
  >> simp[GSYM fcg_get_callees_def]
  >> simp[listTheory.ALL_DISTINCT_SNOC]
QED

(* fcg_visit: preserves ALL_DISTINCT of callees *)
Theorem fcg_visit_callees_distinct:
  !fn_n. ALL_DISTINCT (fcg_get_callees fcg fn_n) ==>
         ALL_DISTINCT (fcg_get_callees
           (SND (fcg_visit ctx fn_name fcg)) fn_n)
Proof
  rpt strip_tac >>
  simp[fcg_visit_def] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >>
  simp[fcg_get_callees_reachable_update] >>
  Cases_on `fn_n = fn_name`
  >- gvs[fcg_record_edges_callees_distinct]
  >> simp[fcg_record_edges_callees_other]
QED

(* fcg_dfs: callees distinctness invariant *)
Theorem fcg_dfs_callees_distinct:
  !ctx stack visited fcg.
    (!fn_n. ALL_DISTINCT (fcg_get_callees fcg fn_n)) ==>
    (!fn_n. ALL_DISTINCT (fcg_get_callees
              (fcg_dfs ctx stack visited fcg) fn_n))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> first_x_assum irule >> simp[]
  >> rpt strip_tac
  >> `r = SND (fcg_visit ctx fn_name fcg)` by simp[]
  >> pop_assum SUBST1_TAC
  >> simp[fcg_visit_callees_distinct]
QED

(* fcg_dfs: callees completeness - visited functions have all callees *)
Theorem fcg_dfs_callees_complete:
  !ctx stack visited fcg.
    (!fn_n callee. MEM fn_n visited /\
       fn_directly_calls ctx fn_n callee ==>
       MEM callee (fcg_get_callees fcg fn_n)) /\
    (!x. MEM x fcg.fcg_reachable ==> MEM x visited) ==>
    (!fn_n callee.
       MEM fn_n (fcg_dfs ctx stack visited fcg).fcg_reachable /\
       fn_directly_calls ctx fn_n callee ==>
       MEM callee (fcg_get_callees
         (fcg_dfs ctx stack visited fcg) fn_n))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> first_x_assum irule >> simp[]
  >> conj_tac
  (* callees for fn_name :: visited *)
  >- (rpt strip_tac
      >> reverse (Cases_on `fn_n' = fn_name`) >> gvs[]
      (* fn_name case: rewrite r -> SND(fcg_visit ...) *)
      >- (qpat_x_assum `fcg_visit _ _ _ = _`
            (fn th => REWRITE_TAC [GSYM (CONV_RULE
               (RAND_CONV (REWR_CONV pairTheory.SND))
               (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis``
                        th))])
          >> simp[fcg_visit_callees, fn_directly_calls_scan]
          >> disj2_tac >> gvs[fn_directly_calls_scan])
      (* visited case *)
      >> qpat_x_assum `fcg_visit _ _ _ = _`
           (fn th => REWRITE_TAC [GSYM (CONV_RULE
              (RAND_CONV (REWR_CONV pairTheory.SND))
              (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis``
                       th))])
      >> simp[fcg_visit_callees_other]
      >> res_tac)
  (* r.fcg_reachable ⊆ fn_name :: visited *)
  >> rpt strip_tac
  >> qpat_x_assum `fcg_visit _ _ _ = _`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE
          [GSYM (CONV_RULE
             (RAND_CONV (REWR_CONV pairTheory.SND))
             (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis``
                      th))]))
  >> pop_assum mp_tac
  >> simp[fcg_visit_reachable_eq]
  >> Cases_on `lookup_function fn_name ctx.ctx_functions`
  >> simp[listTheory.MEM_SNOC]
  >> strip_tac >> gvs[]
QED

(* fcg_dfs: call_sites completeness - all INVOKEs from visited are recorded *)
Theorem fcg_dfs_call_sites_complete:
  !ctx stack visited fcg.
    (!caller func callee inst.
       MEM caller visited /\
       lookup_function caller ctx.ctx_functions = SOME func /\
       MEM (callee, inst) (fcg_scan_function func) ==>
       MEM inst (fcg_get_call_sites fcg callee)) /\
    (!x. MEM x fcg.fcg_reachable ==> MEM x visited) ==>
    (!caller func callee inst.
       MEM caller (fcg_dfs ctx stack visited fcg).fcg_reachable /\
       lookup_function caller ctx.ctx_functions = SOME func /\
       MEM (callee, inst) (fcg_scan_function func) ==>
       MEM inst (fcg_get_call_sites
         (fcg_dfs ctx stack visited fcg) callee))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> TRY (res_tac >> NO_TAC)
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> qpat_x_assum `(_ /\ _) ==> _` mp_tac >> impl_tac
  >- (conj_tac
      (* call sites for fn_name :: visited are in r *)
      >- (rpt strip_tac
          >> qpat_x_assum `fcg_visit _ _ _ = _`
               (fn th => REWRITE_TAC [GSYM (CONV_RULE
                  (RAND_CONV (REWR_CONV pairTheory.SND))
                  (AP_TERM ``SND : string list # fcg_analysis
                                  -> fcg_analysis`` th))])
          >> simp[fcg_visit_call_sites]
          >> TRY (metis_tac[])
          >> disj1_tac >> res_tac)
      (* r.fcg_reachable ⊆ fn_name :: visited *)
      >> rpt strip_tac
      >> qpat_x_assum `fcg_visit _ _ _ = _`
           (fn th => RULE_ASSUM_TAC (REWRITE_RULE
              [GSYM (CONV_RULE
                 (RAND_CONV (REWR_CONV pairTheory.SND))
                 (AP_TERM ``SND : string list # fcg_analysis
                                 -> fcg_analysis`` th))]))
      >> pop_assum mp_tac >> simp[fcg_visit_reachable_eq]
      >> Cases_on `lookup_function fn_name ctx.ctx_functions`
      >> simp[listTheory.MEM_SNOC] >> strip_tac >> gvs[])
  >> strip_tac >> res_tac
QED

(* fcg_dfs: reachable sound - reachable entries have RTC path *)
Theorem fcg_dfs_reachable_sound:
  !ctx stack visited fcg entry_name.
    (!x. MEM x fcg.fcg_reachable ==>
         fcg_path ctx entry_name x) /\
    (!x. MEM x stack ==>
         fcg_path ctx entry_name x) /\
    (!x. MEM x visited ==>
         fcg_path ctx entry_name x) ==>
    (!x. MEM x (fcg_dfs ctx stack visited fcg).fcg_reachable ==>
         fcg_path ctx entry_name x)
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  (* Establish the three IH preconditions *)
  >> `!x'. MEM x' r.fcg_reachable ==> fcg_path ctx entry_name x'`
       by (rpt strip_tac
           >> qpat_x_assum `fcg_visit _ _ _ = _`
                (fn th => RULE_ASSUM_TAC (REWRITE_RULE
                   [GSYM (CONV_RULE (RAND_CONV (REWR_CONV pairTheory.SND))
                          (AP_TERM ``SND : string list # fcg_analysis
                                        -> fcg_analysis`` th))]))
           >> pop_assum mp_tac >> simp[fcg_visit_reachable_eq]
           >> Cases_on `lookup_function fn_name ctx.ctx_functions`
           >> simp[listTheory.MEM_SNOC] >> strip_tac >> gvs[])
  >> `!x'. MEM x' q ==> fcg_path ctx entry_name x'`
       by (rpt strip_tac
           >> qpat_x_assum `fcg_visit _ _ _ = _`
                (fn th => RULE_ASSUM_TAC (REWRITE_RULE
                   [GSYM (CONV_RULE (RAND_CONV (REWR_CONV pairTheory.FST))
                          (AP_TERM ``FST : string list # fcg_analysis
                                        -> string list`` th))]))
           >> drule fcg_visit_fst_calls >> strip_tac
           >> simp[fcg_path_def]
           >> irule relationTheory.RTC_TRANS
           >> qexists_tac `fn_name`
           >> conj_tac >- gvs[fcg_path_def]
           >> simp[Once relationTheory.RTC_CASES1]
           >> metis_tac[relationTheory.RTC_REFL])
  (* Apply IH *)
  >> qpat_x_assum `!e. (_ /\ _ /\ _) ==> _`
       (qspec_then `entry_name` mp_tac)
  >> impl_tac
  >- (rpt conj_tac >> rpt strip_tac >> gvs[]
      >> res_tac)
  >> disch_then drule >> simp[]
QED

(* fcg_dfs: stack elements in context end up reachable *)
Theorem fcg_dfs_stack_reachable:
  !ctx stack visited fcg.
    (!x. MEM x visited /\
         MEM x (ctx_fn_names ctx) ==>
         MEM x fcg.fcg_reachable) /\
    (!x. MEM x fcg.fcg_reachable ==> MEM x visited) ==>
    (!fn_n. MEM fn_n stack /\
       MEM fn_n (ctx_fn_names ctx) ==>
       MEM fn_n (fcg_dfs ctx stack visited fcg).fcg_reachable)
Proof
  cheat
QED

(* fcg_dfs: call_sites soundness - recorded sites come from reachable callers *)
Theorem fcg_dfs_call_sites_sound:
  !ctx stack visited fcg.
    (!callee inst. MEM inst (fcg_get_call_sites fcg callee) ==>
      ?caller func. MEM caller fcg.fcg_reachable /\
        lookup_function caller ctx.ctx_functions = SOME func /\
        MEM (callee, inst) (fcg_scan_function func)) /\
    (!x. MEM x visited /\
         MEM x (MAP (\f. f.fn_name) ctx.ctx_functions) ==>
         MEM x fcg.fcg_reachable) ==>
    (!callee inst. MEM inst (fcg_get_call_sites
                    (fcg_dfs ctx stack visited fcg) callee) ==>
      ?caller func.
        MEM caller (fcg_dfs ctx stack visited fcg).fcg_reachable /\
        lookup_function caller ctx.ctx_functions = SOME func /\
        MEM (callee, inst) (fcg_scan_function func))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> gvs[]
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> first_x_assum irule >> simp[]
  >> conj_tac
  (* Subgoal 1: call_sites in r come from reachable callers *)
  >- (rpt strip_tac
      >> qpat_x_assum `MEM _ (fcg_get_call_sites r _)` mp_tac
      >> qpat_x_assum `fcg_visit _ _ _ = _`
           (fn th => REWRITE_TAC [GSYM (CONV_RULE
              (RAND_CONV (REWR_CONV pairTheory.SND))
              (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis``
                       th))])
      >> simp[fcg_visit_call_sites] >> strip_tac
      >> TRY (MAP_EVERY qexists_tac [`fn_name`, `func`]
              >> simp[fcg_visit_reachable_eq, listTheory.MEM_SNOC]
              >> NO_TAC)
      >> qpat_x_assum `!c i. MEM i (fcg_get_call_sites fcg c) ==> _`
           drule >> strip_tac
      >> MAP_EVERY qexists_tac [`caller`, `func`]
      >> simp[fcg_visit_reachable_eq]
      >> Cases_on `lookup_function fn_name ctx.ctx_functions`
      >> simp[listTheory.MEM_SNOC])
  (* Subgoal 2: visited ⊆ r.fcg_reachable *)
  >> rpt strip_tac >> gvs[]
  >> `r.fcg_reachable = (SND (fcg_visit ctx fn_name fcg)).fcg_reachable`
       by simp[]
  >> pop_assum (fn eq => REWRITE_TAC [eq])
  >> simp[fcg_visit_reachable_eq]
  >> Cases_on `lookup_function fn_name ctx.ctx_functions`
  >> simp[listTheory.MEM_SNOC]
  >> gvs[]
  >> imp_res_tac lookup_function_not_mem >> gvs[]
QED

(* ==========================================================================
   Section 4: Domain Invariants
   ========================================================================== *)

Theorem fcg_analyze_reachable_in_context:
  wf_fn_names ctx /\
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
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  simp[fcg_analyze_def] >>
  Cases_on `ctx.ctx_entry` >> simp[fcg_empty_def] >>
  strip_tac >>
  irule (Q.SPECL [`ctx`,`[x]`,`[]`,`fcg_empty`]
    fcg_dfs_reachable_distinct
    |> SIMP_RULE (srw_ss()) [fcg_empty_def])
QED

(* ==========================================================================
   Section 5: Callees Correctness
   ========================================================================== *)

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
  imp_res_tac lookup_function_mem_func >>
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

(* ==========================================================================
   Section 6: Call Sites Correctness
   ========================================================================== *)

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

(* Completeness: every INVOKE targeting callee from a reachable caller is recorded *)
Theorem fcg_analyze_call_sites_complete:
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
   Section 7: Reachability Correctness
   ========================================================================== *)

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
  cheat
QED

(* ==========================================================================
   Section 8: No-Entry Edge Cases
   ========================================================================== *)

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

(* ==========================================================================
   Section 9: Unreachable Correctness
   ========================================================================== *)

(* Unreachable = complement of reachable within context functions *)
Theorem fcg_analyze_unreachable_correct:
  wf_fn_names ctx ==>
  (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
   MEM func ctx.ctx_functions /\
   ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  strip_tac >>
  simp[fcg_get_unreachable_def, fcg_is_reachable_def,
       listTheory.MEM_FILTER] >>
  metis_tac[]
QED

val _ = export_theory();
