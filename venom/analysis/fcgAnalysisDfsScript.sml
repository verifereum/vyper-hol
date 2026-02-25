(*
 * FCG Analysis DFS Invariants
 *
 * Inductive invariants for fcg_dfs, all proved by ho_match_mp_tac fcg_dfs_ind.
 *
 * TOP-LEVEL theorems:
 *   fcg_dfs_reachable_in_context   - reachable names are in context
 *   fcg_dfs_visited_reachable      - visited context-names end up reachable
 *   fcg_dfs_callees_sound          - recorded callees => fn_directly_calls
 *   fcg_dfs_callees_complete       - visited + fn_directly_calls => recorded
 *   fcg_dfs_callees_distinct       - callee lists stay ALL_DISTINCT
 *   fcg_dfs_reachable_distinct     - reachable list stays ALL_DISTINCT
 *   fcg_dfs_call_sites_sound       - recorded sites from reachable callers
 *   fcg_dfs_call_sites_complete    - all INVOKEs from visited are recorded
 *   fcg_dfs_reachable_sound        - reachable => RTC path from entry
 *   fcg_dfs_stack_reachable        - stack elements end up reachable
 *   fcg_dfs_reachable_closed       - reachable closed under direct calls
 *)

Theory fcgAnalysisDfs
Ancestors
  fcgAnalysisVisit fcgAnalysisDefs fcgAnalysis venomInst relation

(* Local tactics: rewrite r/q back to SND/FST (fcg_visit ...) via pair eq.
 * visit_{snd,fst}_tac rewrite the goal;
 * asm_visit_{snd,fst}_tac rewrite assumptions.
 * Usage: qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac *)
fun visit_snd_tac th = REWRITE_TAC [GSYM (CONV_RULE
  (RAND_CONV (REWR_CONV pairTheory.SND))
  (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis`` th))];
fun visit_fst_tac th = REWRITE_TAC [GSYM (CONV_RULE
  (RAND_CONV (REWR_CONV pairTheory.FST))
  (AP_TERM ``FST : string list # fcg_analysis -> string list`` th))];
fun asm_visit_snd_tac th = RULE_ASSUM_TAC (REWRITE_RULE
  [GSYM (CONV_RULE (RAND_CONV (REWR_CONV pairTheory.SND))
    (AP_TERM ``SND : string list # fcg_analysis -> fcg_analysis`` th))]);
fun asm_visit_fst_tac th = RULE_ASSUM_TAC (REWRITE_RULE
  [GSYM (CONV_RULE (RAND_CONV (REWR_CONV pairTheory.FST))
    (AP_TERM ``FST : string list # fcg_analysis -> string list`` th))]);

(* ===== Reachable domain ===== *)

(* fcg_dfs: all reachable names were either already reachable or are
   in ctx_fn_names *)
Theorem fcg_dfs_reachable_in_context:
  !ctx stack visited fcg.
    (!x. MEM x fcg.fcg_reachable ==>
         MEM x (ctx_fn_names ctx)) ==>
    (!x. MEM x (fcg_dfs ctx stack visited fcg).fcg_reachable ==>
         MEM x (ctx_fn_names ctx))
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def]
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
  >> drule fcg_visit_reachable >> strip_tac >> gvs[ctx_fn_names_def]
QED

(* ===== Visited reachable ===== *)

(* fcg_dfs: visited functions in context end up in output reachable *)
Theorem fcg_dfs_visited_reachable:
  !ctx stack visited fcg.
    (!x. MEM x visited /\
         MEM x (ctx_fn_names ctx) ==>
         MEM x fcg.fcg_reachable) ==>
    (!x. MEM x visited /\
         MEM x (ctx_fn_names ctx) ==>
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
  >> imp_res_tac lookup_function_not_mem >> gvs[ctx_fn_names_def]
QED

(* ===== Callees invariants ===== *)

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
      >- (qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac
          >> simp[fcg_visit_callees, fn_directly_calls_scan]
          >> disj2_tac >> gvs[fn_directly_calls_scan])
      (* visited case *)
      >> qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac
      >> simp[fcg_visit_callees_other]
      >> res_tac)
  (* r.fcg_reachable <= fn_name :: visited *)
  >> rpt strip_tac
  >> qpat_x_assum `fcg_visit _ _ _ = _` asm_visit_snd_tac
  >> pop_assum mp_tac
  >> simp[fcg_visit_reachable_eq]
  >> Cases_on `lookup_function fn_name ctx.ctx_functions`
  >> simp[listTheory.MEM_SNOC]
  >> strip_tac >> gvs[]
QED

(* ===== Reachable distinctness ===== *)

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

(* ===== Call sites invariants ===== *)

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
          >> qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac
          >> simp[fcg_visit_call_sites]
          >> TRY (metis_tac[])
          >> disj1_tac >> res_tac)
      (* r.fcg_reachable <= fn_name :: visited *)
      >> rpt strip_tac
      >> qpat_x_assum `fcg_visit _ _ _ = _` asm_visit_snd_tac
      >> pop_assum mp_tac >> simp[fcg_visit_reachable_eq]
      >> Cases_on `lookup_function fn_name ctx.ctx_functions`
      >> simp[listTheory.MEM_SNOC] >> strip_tac >> gvs[])
  >> strip_tac >> res_tac
QED

(* fcg_dfs: call_sites soundness - recorded sites come from reachable callers *)
Theorem fcg_dfs_call_sites_sound:
  !ctx stack visited fcg.
    (!callee inst. MEM inst (fcg_get_call_sites fcg callee) ==>
      ?caller func. MEM caller fcg.fcg_reachable /\
        lookup_function caller ctx.ctx_functions = SOME func /\
        MEM (callee, inst) (fcg_scan_function func)) /\
    (!x. MEM x visited /\
         MEM x (ctx_fn_names ctx) ==>
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
      >> qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac
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
  (* Subgoal 2: visited <= r.fcg_reachable *)
  >> qpat_x_assum `fcg_visit _ _ _ = _` visit_snd_tac
  >> MATCH_MP_TAC fcg_visit_visited_in_reachable >> simp[]
QED

(* ===== Reachable soundness ===== *)

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
           >> qpat_x_assum `fcg_visit _ _ _ = _` asm_visit_snd_tac
           >> pop_assum mp_tac >> simp[fcg_visit_reachable_eq]
           >> Cases_on `lookup_function fn_name ctx.ctx_functions`
           >> simp[listTheory.MEM_SNOC] >> strip_tac >> gvs[])
  >> `!x'. MEM x' q ==> fcg_path ctx entry_name x'`
       by (rpt strip_tac
           >> qpat_x_assum `fcg_visit _ _ _ = _` asm_visit_fst_tac
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

(* ===== Stack reachable ===== *)

(* Local tactics: rewrite r -> SND(fcg_visit ...) then apply Visit helpers.
 * visit_extends_reachable_tac: closes "visited ∪ {fn_name} ⊆ r.fcg_reachable"
 * visit_contracts_visited_tac: closes "r.fcg_reachable ⊆ fn_name :: visited"
 * Both take a `fcg_visit ctx fn_name fcg = (q,r)` equation as thm. *)
fun visit_extends_reachable_tac th =
  visit_snd_tac th
  >> MATCH_MP_TAC fcg_visit_visited_in_reachable
  >> simp[];
fun visit_contracts_visited_tac th =
  visit_snd_tac th
  >> MATCH_MP_TAC fcg_visit_reachable_in_visited
  >> simp[];

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
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  >> Cases_on `MEM fn_name visited` >> fs[]
  (* visited: use fcg_dfs_visited_reachable *)
  >- (gvs[]
      >> irule (Q.SPECL [`ctx`,`stack`,`visited`,`fcg`]
           fcg_dfs_visited_reachable |> SIMP_RULE (srw_ss()) [])
      >> simp[])
  (* not visited: use IH *)
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  (* Goal 1: fn_n = fn_name, just visited *)
  >- (irule (Q.SPECL [`ctx`,`q ++ stack`,`fn_n :: visited`,`r`]
         fcg_dfs_visited_reachable |> SIMP_RULE (srw_ss()) [])
      >> simp[]
      >> qpat_x_assum `fcg_visit _ _ _ = _` visit_extends_reachable_tac)
  (* Goal 2: fn_n on stack -- use IH *)
  >> first_x_assum irule >> simp[]
  >> qpat_x_assum `fcg_visit _ _ _ = _`
       (fn th => conj_tac
          >- visit_extends_reachable_tac th
          >> visit_contracts_visited_tac th)
QED

(* ===== Reachable closed ===== *)

(* fcg_dfs: output reachable is closed under fn_directly_calls
   for in-context callees *)
Theorem fcg_dfs_reachable_closed:
  !ctx stack visited fcg.
    (!x. MEM x visited /\
         MEM x (ctx_fn_names ctx) ==>
         MEM x fcg.fcg_reachable) /\
    (!x. MEM x fcg.fcg_reachable ==> MEM x visited) /\
    (!fn_n callee. MEM fn_n visited /\
       fn_directly_calls ctx fn_n callee /\
       MEM callee (ctx_fn_names ctx) ==>
       MEM callee visited \/ MEM callee stack) ==>
    (!fn_n callee.
       MEM fn_n (fcg_dfs ctx stack visited fcg).fcg_reachable /\
       fn_directly_calls ctx fn_n callee /\
       MEM callee (ctx_fn_names ctx) ==>
       MEM callee (fcg_dfs ctx stack visited fcg).fcg_reachable)
Proof
  ho_match_mp_tac fcg_dfs_ind >> rpt gen_tac >> strip_tac
  >> simp[fcg_dfs_def] >> rpt strip_tac
  (* Base case: empty stack *)
  >- (res_tac >> res_tac)
  >> Cases_on `MEM fn_name visited` >> gvs[]
  (* visited case: fn_name already visited, IH applies directly *)
  >- (first_x_assum irule >> simp[]
      >> conj_tac
      >- (rpt strip_tac >> res_tac >> gvs[])
      >> qexists_tac `fn_n` >> simp[])
  (* not visited: split on fcg_visit *)
  >> Cases_on `fcg_visit ctx fn_name fcg` >> gvs[]
  >> qpat_x_assum `(_ /\ _ /\ _) ==> _` mp_tac >> impl_tac
  >- (qpat_x_assum `fcg_visit _ _ _ = _`
       (fn th => rpt conj_tac
          >- visit_extends_reachable_tac th
          >- visit_contracts_visited_tac th
          (* callees of fn_name :: visited are visited or on q ++ stack *)
          >> visit_fst_tac th
          >> rpt strip_tac >> fs[]
          >- (disj2_tac
              >> simp[fcg_visit_def, fn_directly_calls_scan]
              >> gvs[fn_directly_calls_scan]
              >> Cases_on `lookup_function fn_name ctx.ctx_functions`
              >> gvs[listTheory.MEM_REVERSE, listTheory.MEM_MAP]
              >> metis_tac[])
          >> res_tac >> gvs[]))
  >> strip_tac >> res_tac
QED
