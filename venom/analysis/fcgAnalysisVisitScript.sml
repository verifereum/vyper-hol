(*
 * FCG Analysis Visit
 *
 * Properties of fcg_record_edges and fcg_visit.
 *
 * TOP-LEVEL theorems:
 *   fcg_record_edges_reachable          - record_edges preserves reachable
 *   fcg_record_edges_callees_same       - callees for same fn_name
 *   fcg_record_edges_callees_other      - callees for other fn unchanged
 *   fcg_record_edges_callees_distinct   - preserves ALL_DISTINCT callees
 *   fcg_record_edges_call_sites_mem     - call_sites membership
 *   fcg_record_edges_call_sites_other   - call_sites for non-targets unchanged
 *   fcg_visit_reachable                 - visit grows reachable by at most fn_name
 *   fcg_visit_reachable_eq              - exact reachable after visit
 *   fcg_visit_callees                   - callees after visit for fn_name
 *   fcg_visit_callees_other             - callees for other fn unchanged
 *   fcg_visit_callees_distinct          - preserves ALL_DISTINCT callees
 *   fcg_visit_fst_calls                 - FST elements are callees
 *   fcg_visit_call_sites                - call_sites after visit
 *   fcg_get_callees_reachable_update    - reachable update doesn't affect callees
 *   fcg_get_call_sites_reachable_update - reachable update doesn't affect call_sites
 *)

Theory fcgAnalysisVisit
Ancestors
  fcgAnalysisDefs fcgAnalysis venomInst

(* ===== fcg_record_edges helpers ===== *)

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

(* ===== fcg_visit helpers ===== *)

(* Updating fcg_reachable does not affect fcg_get_callees *)
Theorem fcg_get_callees_reachable_update:
  !fcg r fn_n.
    fcg_get_callees (fcg with fcg_reachable := r) fn_n =
    fcg_get_callees fcg fn_n
Proof
  simp[fcg_get_callees_def]
QED

(* Updating fcg_reachable does not affect fcg_get_call_sites *)
Theorem fcg_get_call_sites_reachable_update:
  !fcg r fn_n.
    fcg_get_call_sites (fcg with fcg_reachable := r) fn_n =
    fcg_get_call_sites fcg fn_n
Proof
  simp[fcg_get_call_sites_def]
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

(* fcg_visit: callees after visit for fn_name *)
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

val _ = export_theory();
