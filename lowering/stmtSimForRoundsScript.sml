(*
 * Counted For loops: the rounds of eval_for composed over the actual
 * source action.
 *
 * TOP-LEVEL:
 *   eval_for_rounds — a loop over the values from the k-th on has a
 *                     counted outcome when every round from a state of the
 *                     loop invariant has one, and the invariant after the
 *                     last value reaches the loop's exit without GAS reads
 *   eval_for_value_rounds — the same for a loop over copied values
 *)

Theory stmtSimForRounds
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath vyperInterpreter vyperState list rich_list arithmetic
Libs
  monadsyntax

Theorem eval_for_cons_round:
  !cx tyv nm body r rs.
  eval_for cx tyv nm body (r::rs) =
  bind (do v <- read_result cx r;
           push_scope_with_var nm tyv v;
           finally (try (do eval_stmts cx body; return F od)
                        handle_loop_exception) pop_scope od)
       (\b. if b then return () else eval_for cx tyv nm body rs)
Proof
  simp[Once evaluate_def, ignore_bind_def, bind_assoc]
QED

(* A copied element is already a value: its round reads nothing. *)
Theorem eval_for_cons_value_round:
  !cx tyv nm body v rs.
  eval_for cx tyv nm body (Value v::rs) =
  bind (do push_scope_with_var nm tyv v;
           finally (try (do eval_stmts cx body; return F od)
                        handle_loop_exception) pop_scope od)
       (\b. if b then return () else eval_for cx tyv nm body rs)
Proof
  rewrite_tac[eval_for_cons_round, read_result_def, bind_return] >> simp[]
QED

Theorem gas_admissible_bind_tail:
  gas_admissible (bind a next) ok es /\
  (!tail. a (es with gas_obs := xs ++ tail) =
          (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (next v) ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem gas_marked_exec_break:
  gas_marked_exec memory (ctx,func) a (es,s) marks (INL T) mid r ==>
  gas_marked_exec memory (ctx,func)
    (bind a (\b. if b then return () else next))
    (es,s) marks (INL ()) mid r
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[bind_def, return_def]
QED

Theorem gas_outcome_return_path:
  gas_marked_path memory ctx func s 0 (OK t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     Q H (INL ()) (es with gas_obs := []) t) ==>
  gas_outcome memory tops (ctx,func) cx st0 (return ()) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK t`] >>
  simp[gas_marked_exec_def, return_def]
QED

Theorem gas_outcome_false_tail:
  gas_marked_exec memory (ctx,func) a (es,s) left (INL F) mid (OK t) /\
  gas_outcome memory tops (ctx,func) cx st0 next (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0
    (bind a (\b. if b then return () else next)) (es,s) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[])
  >- (gvs[gas_summary_at_def]
      >- (qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
          qexistsl_tac [`res`, `es_end`, `OK t'`] >> simp[] >>
          irule gas_marked_exec_bind_normal >>
          qexistsl_tac [`mid`, `t`, `F`] >> simp[]) >>
      qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`, `t`, `F`] >> simp[]) >>
  qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 4 gas_exempt_cert_rules) >>
  qexistsl_tac [`mid`, `t`, `F`] >> simp[GSYM ignore_bind_def]
QED

(* The round's source left the storage domain: the whole loop is a
   bad-storage run under the round's marks. *)
val bool_round_out_of_domain_tac =
  qexists_tac `left` >> disj1_tac >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >> fs[] >>
  irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
  metis_tac[];

Theorem gas_outcome_bool_round:
  gas_outcome memory tops (ctx,func) cx st0 a (es,s)
    (\H res ee t. ?b. res = INL b /\
       (b ==> Done H ee t) /\ (~b ==> P H ee t))
    (\H res ee r. ?ex. res = INR ex /\ R H ex ee r) /\
  (!marks mid t.
     gas_marked_exec memory (ctx,func) a (es,s) marks (INL F) mid (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
        P H (mid with gas_obs := []) t) ==>
     gas_outcome memory tops (ctx,func) cx st0 next (mid with gas_obs := [],t)
       (\H res ee u. res = INL () /\ Done H ee u)
       (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)) /\
  storage_trace_frame next ==>
  gas_outcome memory tops (ctx,func) cx st0
    (bind a (\b. if b then return () else next)) (es,s)
    (\H res ee t. res = INL () /\ Done H ee t)
    (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)
Proof
  strip_tac >>
  `!b. storage_trace_frame ((\b. if b then return () else next) b)` by
    (Cases >> simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (qexists_tac `left` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> fs[])
  >- suspend "normal"
  >- suspend "exit" >>
  suspend "exempt"
QED

Resume gas_outcome_bool_round[normal]:
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- bool_round_out_of_domain_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?b. res = INL b` by metis_tac[] >> gvs[] >>
  Cases_on `b` >> gvs[]
  >- (qexists_tac `left` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL ()`, `es_end`, `OK t`] >> simp[] >>
      irule gas_marked_exec_break >> simp[]) >>
  first_x_assum (qspecl_then [`left`, `es_end`, `t`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all gas_outcome_false_tail >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >>
  simp[]
QED
Resume gas_outcome_bool_round[exit]:
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- bool_round_out_of_domain_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
  qexists_tac `left` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume gas_outcome_bool_round[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexists_tac `left` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 5 gas_exempt_cert_rules) >> simp[GSYM ignore_bind_def]
QED
Finalise gas_outcome_bool_round

(* A round is eval_for's step for one element: reading its value, the
   loop variable's scope, the body, and the break/continue handling, up
   to the boolean telling whether the loop broke.  Inv k holds at the
   loop head before the k-th round; Done holds where the loop leaves,
   after a break or after the last round.  ok is the admissibility the
   enclosing statement supplies for the remaining loop.  Exceptional
   exits keep their exception. *)
Theorem eval_for_rounds:
  !memory tops ctx func cx st0 tyv nm body vs ok Inv Done R.
    (!k es s.
       k < LENGTH vs /\
       (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es s) /\
       gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
       gas_outcome memory tops (ctx, func) cx st0
         (do v <- read_result cx (EL k vs);
             push_scope_with_var nm tyv v;
             finally
               (try (do eval_stmts cx body; return F od)
                  handle_loop_exception)
               pop_scope
          od) (es, s)
         (\H res ee t. ?broke. res = INL broke /\
            (broke ==> Done H ee t) /\ (~broke ==> Inv H (SUC k) ee t))
         (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)) /\
    (!es s.
       (?H. valid_horizon cx st0 H es.storage_trace) /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
          Inv H (LENGTH vs) es s) ==>
       ?t. gas_marked_path memory ctx func s 0 (OK t) /\
           !H. valid_horizon cx st0 H es.storage_trace ==>
             Done H (es with gas_obs := []) t) ==>
    !k es s.
      k <= LENGTH vs /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es s) /\
      gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
      gas_outcome memory tops (ctx, func) cx st0
        (eval_for cx tyv nm body (DROP k vs)) (es, s)
        (\H res ee t. res = INL () /\ Done H ee t)
        (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)
Proof
  rpt gen_tac >> strip_tac >>
  gen_tac >> measureInduct_on `LENGTH vs - k` >>
  rpt gen_tac >> strip_tac >>
  Cases_on `k = LENGTH vs`
  >- (gvs[] >> simp[Once evaluate_def] >>
      reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
          fs[gasStorageTheory.gas_bad_storage_at_def, return_def,
             vyperStorageFootprintTheory.storage_trace_domain_def]) >>
      irule gas_outcome_return_path >>
      qpat_x_assum `!es s. (?H. _) /\ _ ==> _`
        (qspecl_then [`es`, `s`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      qexists_tac `t` >> simp[]) >>
  `k < LENGTH vs` by decide_tac >>
  `DROP k vs = EL k vs :: DROP (SUC k) vs` by
    metis_tac[DROP_CONS_EL] >>
  `SUC k <= LENGTH vs /\ LENGTH vs - SUC k < LENGTH vs - k` by
    decide_tac >>
  qpat_assum `!k es s. _` drule_all >> strip_tac >>
  asm_rewrite_tac[eval_for_cons_round] >>
  irule gas_outcome_bool_round >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists_tac `\H. Inv H (SUC k)` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ es` mp_tac >>
  asm_rewrite_tac[eval_for_cons_round] >> disch_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  drule_all gas_admissible_bind_tail >> simp[] >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC k` mp_tac) >>
  simp[]
QED

(* eval_for_rounds for a loop over copied values: a round binds the k-th
   value directly. *)
Theorem eval_for_value_rounds:
  !memory tops ctx func cx st0 tyv nm body vs ok Inv Done R.
    (!k es s.
       k < LENGTH vs /\
       (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es s) /\
       gas_admissible (eval_for cx tyv nm body (MAP Value (DROP k vs))) ok es ==>
       gas_outcome memory tops (ctx, func) cx st0
         (do push_scope_with_var nm tyv (EL k vs);
             finally
               (try (do eval_stmts cx body; return F od)
                  handle_loop_exception)
               pop_scope
          od) (es, s)
         (\H res ee t. ?broke. res = INL broke /\
            (broke ==> Done H ee t) /\ (~broke ==> Inv H (SUC k) ee t))
         (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)) /\
    (!es s.
       (?H. valid_horizon cx st0 H es.storage_trace) /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
          Inv H (LENGTH vs) es s) ==>
       ?t. gas_marked_path memory ctx func s 0 (OK t) /\
           !H. valid_horizon cx st0 H es.storage_trace ==>
             Done H (es with gas_obs := []) t) ==>
    !k es s.
      k <= LENGTH vs /\
      (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es s) /\
      gas_admissible (eval_for cx tyv nm body (MAP Value (DROP k vs))) ok es ==>
      gas_outcome memory tops (ctx, func) cx st0
        (eval_for cx tyv nm body (MAP Value (DROP k vs))) (es, s)
        (\H res ee t. res = INL () /\ Done H ee t)
        (\H res ee r. ?ex. res = INR ex /\ R H ex ee r)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`memory`, `tops`, `ctx`, `func`, `cx`, `st0`, `tyv`, `nm`, `body'`,
    `MAP Value vs`, `ok`, `Inv`, `Done`, `R`] mp_tac eval_for_rounds >>
  simp[GSYM MAP_DROP, EL_MAP, read_result_def, bind_return]
QED
