(*
 * Expression simulation: compile_subscript_map_case, a case of exprSimPlaces on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimSubscriptMap
Ancestors
  exprSimMapDefs exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimDefs gasContext gasSummary gasSummaryCompose gasExemptCert vyperState
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* Counted source sequencing keeps the observation stream available to both
   operands; in particular the index is forced only after the base succeeds. *)
Theorem eval_subscript_bind:
  eval_expr cx (Subscript ann obj idx) =
    bind (eval_expr cx obj) (\tv.
      bind (bind (eval_expr cx idx) (read_result cx)) (\v.
        select_result cx (expr_type obj) tv (ValueSubscript v)))
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_assoc]
QED

Theorem subscript_map_base_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_map_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_map_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _ ==> _` (qspec_then `gs` mp_tac) >>
  rewrite_tac[eval_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  simp[bind_def]
QED

Theorem subscript_map_index_admissible:
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es /\
  gas_marked_exec memory (ctx, func) (eval_expr cx obj)
    (es, s0) marks (INL tv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx idx) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  rewrite_tac[eval_subscript_bind] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  gvs[bind_def, expr_map_res_ok_def, expr_res_ok_def]
QED

(* A counted continuation, including its exemption origin, may follow a
   completed result-valued source prefix. *)
Theorem gas_outcome_result_prefix:
  gas_marked_exec memory (ctx, func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es, s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx, func) (k v)
    (mid with gas_obs := [], t) Q R ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists_tac `left ++ right` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`out`, `fin`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_normal >>
                    goal_assum drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err, ef) (callee, tf)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  qexistsl_tac [`mid`, `t`, `v`] >>
  simp[GSYM ignore_bind_def]
QED

Theorem gas_outcome_bind_result:
  gas_outcome memory tops (ctx, func)
    (a : evaluation_state -> eval_result evaluation_result) (es, s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!v mid t. P v (mid with gas_obs := []) t ==>
     gas_outcome memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) Q R) ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2
    (mp_tac o REWRITE_RULE [gasOutcomeTheory.gas_outcome_def]) assume_tac) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (gvs[] >> irule gas_outcome_result_prefix >>
          qexistsl_tac [`marks`, `mid`, `t`, `v`] >>
          simp[] >> first_x_assum irule >> simp[]) >>
      gvs[] >> rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >> simp[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err, ef) (callee, tf)` >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

(* A top-level mapping variable: compile_expr lowers it to a pointer
   literal holding the mapping's declared slot (env_consistent's hashmap
   clause, lookup_global_mapping_region), and the source lookup returns the
   HashMapRef at that slot. *)
Theorem compile_toplevel_map_case:
  !nocalls ctx func cenv cx ty id.
    expr_map_case nocalls ctx func cenv cx (TopLevelName ty id)
Proof
  cheat
QED

(* A mapping that is a value of a mapping (m[a] for m : HashMap[K,
   HashMap[...]]): the base's slot, the key lowered after it, and
   compile_mapping_subscript's SHA3 over the two (in a fresh 64-byte
   buffer) against hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key. *)
Theorem compile_subscript_map_map_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_map_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* With every smaller expression simulating, an expression naming a
   mapping simulates: its keys are smaller. *)
Theorem expr_map_case_below:
  !obj cenv ctx func cx.
    expr_sim_below cenv (expr_size obj) ==>
    expr_map_case T ctx func cenv cx obj
Proof
  measureInduct_on `expr_size obj` >> rpt strip_tac >>
  Cases_on `obj`
  >~ [`TopLevelName`] >- simp[compile_toplevel_map_case]
  >~ [`Subscript _ _ _`]
  >- (rename1 `Subscript ann obj0 idx` >>
      irule compile_subscript_map_map_case >> conj_tac
      >- (rpt strip_tac >>
          `expr_ok cenv idx` by
            (fs[expr_sim_below_def] >> first_x_assum irule >>
             simp[expr_size_def]) >>
          gvs[expr_ok_case]) >>
      first_x_assum irule >> simp[expr_size_def] >>
      irule expr_sim_below_mono >>
      qexists_tac `expr_size (Subscript ann obj0 idx)` >>
      simp[expr_size_def]) >>
  irule expr_map_case_other >> simp[]
QED

(* A subscript of a mapping (place_type MapPT) whose value is not a
   mapping: the base's expr_map_case gives the operand holding the
   mapping's slot, the key is lowered after it, and the slot computation
   is compile_subscript_map_map_case's.  expr_sim_inv's map table clauses
   make MapPT mean a declared mapping.  For a storage or transient leaf,
   storage_holds also asks that the leaf's slots are in range
   (slots_in_range); the proof gets that from static_/dyn_slots_in_range
   and the hashmap regions of contract_storage_well_formed, as
   toplevel_storage_slots_in_range and storage_field_slots_in_range do for
   names and struct fields. *)
Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED
