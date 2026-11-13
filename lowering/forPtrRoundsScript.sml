(* Ghost-parametric composition of counted For rounds. The invariant is
   quantified over the current ghost rather than freezing it at loop entry. *)
Theory forPtrRounds
Ancestors gasSummaryComposePtrAll gasSummaryComposePtr fragGasPathPtr stmtSimForRounds gasOutcome
  gasSummary gasExemptCert gasSummaryCompose gasContext vyperInterpreter
  vyperState list rich_list arithmetic
Libs monadsyntax

Theorem gas_marked_exec_ptr_break:
  gas_marked_exec_ptr D (ctx,fn) PG a (es,s,G0,tn0) marks (INL T) mid G tn r ==>
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind a (\b. if b then return () else tail))
    (es,s,G0,tn0) marks (INL ()) mid G tn r
Proof
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[bind_def, return_def]
QED

Theorem gas_outcome_ptr_return_path:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_path_ptr (D H) 0 ctx fn PG G0 tn0 s 0 G tn (OK t) /\
    Q H (INL ()) (es with gas_obs := []) G tn t) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 (return ()) (es,s,G0,tn0) Q ExitPost
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL ()`, `es`, `G`, `tn`, `OK t`] >>
  simp[gas_marked_exec_ptr_def, return_def]
QED

Theorem gas_outcome_ptr_false_tail:
  gas_marked_exec F (ctx,fn) a (es,s) left (INL F) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_path_ptr (D H) 0 ctx fn PG G0 tn0 s (LENGTH left) G1 tn1 (OK t)) /\
  storage_trace_frame tail /\
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 tail (mid with gas_obs := [],t,G1,tn1) Q ExitPost ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0
    (bind a (\b. if b then return () else tail)) (es,s,G0,tn0) Q ExitPost
Proof
  strip_tac >>
  mp_tac (Q.INST [`v` |-> `F`, `source` |-> `a`, `R` |-> `ExitPost`,
    `func` |-> `fn`, `s0` |-> `s`,
    `next` |-> `\b. if b then return () else tail`]
    (INST_TYPE [alpha |-> ``:bool``, beta |-> ``:unit``] gas_outcome_ptr_bind_normal)) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
      irule (cj 4 gas_exempt_cert_rules) >>
      goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]) >>
  simp[]
QED

Theorem gas_outcome_ptr_bool_round:
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 a (es,s,G0,tn0)
    (\H res ee G tn t. ?b. res = INL b /\
      (b ==> Done H ee G tn t) /\ (~b ==> ContinuePost H ee G tn t))
    (\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r) /\
  (!marks mid G tn t.
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_marked_exec_ptr (D H) (ctx,fn) PG a (es,s,G0,tn0) marks
        (INL F) mid G tn (OK t) /\ ContinuePost H (mid with gas_obs := []) G tn t) ==>
    gas_outcome_ptr D tops (ctx,fn) PG cx st0 tail (mid with gas_obs := [],t,G,tn)
      (\H res ee G tn u. res = INL () /\ Done H ee G tn u)
      (\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r)) /\
  storage_trace_frame tail ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0
    (bind a (\b. if b then return () else tail)) (es,s,G0,tn0)
    (\H res ee G tn t. res = INL () /\ Done H ee G tn t)
    (\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r)
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`source` |-> `a`, `func` |-> `fn`, `s0` |-> `s`,
     `next` |-> `\b. if b then return () else tail`,
     `P` |-> `\H res ee G tn t. ?b. res = INL b /\
       (b ==> Done H ee G tn t) /\ (~b ==> ContinuePost H ee G tn t)`,
     `E` |-> `\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r`,
     `Q` |-> `\H res ee G tn t. res = INL () /\ Done H ee G tn t`,
     `R` |-> `\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r`]
    (INST_TYPE [alpha |-> ``:bool``, beta |-> ``:unit``] gas_outcome_ptr_bind_all)) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> gvs[])
      >- simp[]
      >- (Cases >> simp[vyperStorageTraceTheory.storage_trace_frame_return])
      >- (rpt gen_tac >> strip_tac >> Cases_on `v` >> simp[]
          >- (`~t.vs_halted` by
                (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
                 metis_tac[fragGasPathTheory.gas_path_normal]) >>
              rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
              disj2_tac >> disj1_tac >>
              rewrite_tac[gas_summary_ptr_at_marked] >>
              qexistsl_tac [`INL ()`, `mid`, `G`, `tn`, `OK t`] >>
              simp[return_def] >> rpt strip_tac >>
              first_x_assum drule >> strip_tac >> gvs[] >>
              simp[gas_marked_exec_ptr_def, return_def] >>
              irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
          qpat_x_assum `!marks mid G tn t. _`
            (qspecl_then [`left`, `mid`, `G`, `tn`, `t`] mp_tac) >>
          impl_tac
          >- (conj_tac >- metis_tac[] >>
              rpt strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[gas_marked_exec_ptr_def, gas_marked_exec_def,
                  fragGasModeTheory.gas_marked_path_def]) >>
          simp[])
      >- (rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
          irule (cj 5 gas_exempt_cert_rules) >> simp[GSYM ignore_bind_def]) >>
      rpt strip_tac >> simp[ignore_bind_def, bind_assoc] >>
      irule (cj 4 gas_exempt_cert_rules) >>
      goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]) >>
  simp[]
QED

Theorem eval_for_rounds_ptr:
  !D tops ctx fn PG cx st0 tyv nm body vs ok Inv Done ExitPost.
  (!k es s G tn.
    k < LENGTH vs /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (MAP Value (DROP k vs))) ok es ==>
    gas_outcome_ptr D tops (ctx,fn) PG cx st0
      (do push_scope_with_var nm tyv (EL k vs);
          finally (try (do eval_stmts cx body; return F od)
            handle_loop_exception) pop_scope od) (es,s,G,tn)
      (\H res ee gf tf t. ?broke. res = INL broke /\
        (broke ==> Done H ee gf tf t) /\ (~broke ==> Inv H (SUC k) ee gf tf t))
      (\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r)) /\
  (!es s G tn.
    (?H. valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      Inv H (LENGTH vs) es G tn s) ==>
    ?t gf tf. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_path_ptr (D H) 0 ctx fn PG G tn s 0 gf tf (OK t) /\
      Done H (es with gas_obs := []) gf tf t) ==>
  !k es s G tn.
    k <= LENGTH vs /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H k es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (MAP Value (DROP k vs))) ok es ==>
    gas_outcome_ptr D tops (ctx,fn) PG cx st0
      (eval_for cx tyv nm body (MAP Value (DROP k vs))) (es,s,G,tn)
      (\H res ee gf tf t. res = INL () /\ Done H ee gf tf t)
      (\H res ee gt r. ?ex. res = INR ex /\ ExitPost H ex ee gt r)
Proof
  rpt gen_tac >> strip_tac >>
  gen_tac >> measureInduct_on `LENGTH vs - k` >>
  rpt gen_tac >> strip_tac >> Cases_on `k = LENGTH vs`
  >- (gvs[] >> simp[Once evaluate_def] >>
      reverse (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`)
      >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
          fs[gasStorageTheory.gas_bad_storage_at_def, return_def,
             vyperStorageFootprintTheory.storage_trace_domain_def]) >>
      irule gas_outcome_ptr_return_path >>
      qpat_x_assum `!es s G tn. _`
        (qspecl_then [`es`, `s`, `G`, `tn`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      qexistsl_tac [`gf`, `t`, `tf`] >> simp[]) >>
  `k < LENGTH vs` by decide_tac >>
  `DROP k vs = EL k vs :: DROP (SUC k) vs` by metis_tac[DROP_CONS_EL] >>
  `SUC k <= LENGTH vs /\ LENGTH vs - SUC k < LENGTH vs - k` by decide_tac >>
  qpat_assum `!k es s G tn. _` drule_all >> strip_tac >>
  asm_rewrite_tac[MAP, eval_for_cons_value_round] >>
  irule gas_outcome_ptr_bool_round >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists_tac `\H. Inv H (SUC k)` >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ es` mp_tac >>
  asm_rewrite_tac[MAP, eval_for_cons_value_round] >> disch_tac >>
  `?H0. valid_horizon cx st0 H0 mid.storage_trace` by metis_tac[] >>
  `gas_marked_exec_ptr (D H0) (ctx,fn) PG
    (do push_scope_with_var nm tyv (EL k vs);
        finally (try (do eval_stmts cx body; return F od)
          handle_loop_exception) pop_scope od)
    (es,s,G,tn) marks (INL F) mid G' tn' (OK t)` by metis_tac[] >>
  drule gas_marked_exec_ptr_exec >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  drule_all gas_admissible_bind_tail >> simp[] >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC k` mp_tac) >> simp[]
QED
