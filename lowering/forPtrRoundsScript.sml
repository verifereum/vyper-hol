(* Ghost-parametric composition of counted For rounds. The invariant is
   quantified over the current ghost rather than freezing it at loop entry. *)
Theory forPtrRounds
Ancestors gasSummaryComposePtr fragGasPathPtr stmtSimForRounds gasOutcome
  gasSummary gasExemptCert gasSummaryCompose gasContext vyperInterpreter
  vyperState list rich_list arithmetic
Libs monadsyntax

Theorem gas_marked_exec_ptr_break:
  gas_marked_exec_ptr D (ctx,fn) PG a (es,s,G0,tn0) marks (INL T) mid G tn r ==>
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind a (\b. if b then return () else next))
    (es,s,G0,tn0) marks (INL ()) mid G tn r
Proof
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[bind_def, return_def]
QED

Theorem gas_outcome_ptr_return_path:
  gas_path_ptr D 0 ctx fn PG G0 tn0 s 0 G tn (OK t) /\
  Q (INL ()) (es with gas_obs := []) G tn t ==>
  gas_outcome_ptr D tops (ctx,fn) PG (return ()) (es,s,G0,tn0) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL ()`, `es`, `G`, `tn`, `OK t`] >>
  simp[gas_marked_exec_ptr_def, return_def]
QED

Theorem gas_outcome_ptr_false_tail:
  gas_marked_exec_ptr D (ctx,fn) PG a (es,s,G0,tn0) left
    (INL F) mid G1 tn1 (OK t) /\
  gas_outcome_ptr D tops (ctx,fn) PG next (mid with gas_obs := [],t,G1,tn1) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind a (\b. if b then return () else next)) (es,s,G0,tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind_normal >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt strip_tac >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 4 gas_exempt_cert_rules) >>
  goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]
QED

Theorem gas_outcome_ptr_bool_round:
  gas_outcome_ptr D tops (ctx,fn) PG a (es,s,G0,tn0)
    (\res ee G tn t. ?b. res = INL b /\
      (b ==> Done ee G tn t) /\ (~b ==> P ee G tn t))
    (\res ee gt r. ?ex. res = INR ex /\ R ex ee gt r) /\
  (!marks mid G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG a (es,s,G0,tn0) marks
      (INL F) mid G tn (OK t) /\ P (mid with gas_obs := []) G tn t ==>
    gas_outcome_ptr D tops (ctx,fn) PG next (mid with gas_obs := [],t,G,tn)
      (\res ee G tn u. res = INL () /\ Done ee G tn u)
      (\res ee gt r. ?ex. res = INR ex /\ R ex ee gt r)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind a (\b. if b then return () else next)) (es,s,G0,tn0)
    (\res ee G tn t. res = INL () /\ Done ee G tn t)
    (\res ee gt r. ?ex. res = INR ex /\ R ex ee gt r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gas_summary_ptr_at_marked]
      >- (Cases_on `b` >> gvs[]
          >- suspend "break" >> suspend "continue") >>
      suspend "exit") >>
  suspend "exempt"
QED

Resume gas_outcome_ptr_bool_round[break]:
  qexists_tac `left` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL ()`, `es_end`, `G`, `tn`, `OK t`] >>
  simp[] >> irule gas_marked_exec_ptr_break >> simp[]
QED
Resume gas_outcome_ptr_bool_round[continue]:
  first_x_assum drule_all >> strip_tac >>
  drule_all gas_outcome_ptr_false_tail >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked]
QED
Resume gas_outcome_ptr_bool_round[exit]:
  qexists_tac `left` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED
Resume gas_outcome_ptr_bool_round[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 5 gas_exempt_cert_rules) >> simp[GSYM ignore_bind_def]
QED
Finalise gas_outcome_ptr_bool_round

Theorem eval_for_rounds_ptr:
  !D tops ctx fn PG cx tyv nm body vs ok Inv Done R.
  (!k es s G tn.
    k < LENGTH vs /\ Inv k es G tn s /\
    gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
    gas_outcome_ptr D tops (ctx,fn) PG
      (do push_scope_with_var nm tyv (EL k vs);
          finally (try (do eval_stmts cx body; return F od)
            handle_loop_exception) pop_scope od) (es,s,G,tn)
      (\res ee gf tf t. ?broke. res = INL broke /\
        (broke ==> Done ee gf tf t) /\ (~broke ==> Inv (SUC k) ee gf tf t))
      (\res ee gt r. ?ex. res = INR ex /\ R ex ee gt r)) /\
  (!es s G tn. Inv (LENGTH vs) es G tn s ==>
    ?t gf tf. gas_path_ptr D 0 ctx fn PG G tn s 0 gf tf (OK t) /\
      Done (es with gas_obs := []) gf tf t) ==>
  !k es s G tn.
    k <= LENGTH vs /\ Inv k es G tn s /\
    gas_admissible (eval_for cx tyv nm body (DROP k vs)) ok es ==>
    gas_outcome_ptr D tops (ctx,fn) PG
      (eval_for cx tyv nm body (DROP k vs)) (es,s,G,tn)
      (\res ee gf tf t. res = INL () /\ Done ee gf tf t)
      (\res ee gt r. ?ex. res = INR ex /\ R ex ee gt r)
Proof
  rpt gen_tac >> strip_tac >>
  gen_tac >> measureInduct_on `LENGTH vs - k` >>
  rpt gen_tac >> strip_tac >> Cases_on `k = LENGTH vs`
  >- (gvs[] >> simp[Once evaluate_def] >>
      irule gas_outcome_ptr_return_path >>
      first_x_assum drule >> metis_tac[]) >>
  `k < LENGTH vs` by decide_tac >>
  `DROP k vs = EL k vs :: DROP (SUC k) vs` by metis_tac[DROP_CONS_EL] >>
  `SUC k <= LENGTH vs /\ LENGTH vs - SUC k < LENGTH vs - k` by decide_tac >>
  qpat_assum `!k es s G tn. _` drule_all >> strip_tac >>
  asm_rewrite_tac[eval_for_cons_round] >>
  irule gas_outcome_ptr_bool_round >>
  qexists_tac `Inv (SUC k)` >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_admissible _ _ es` mp_tac >>
  asm_rewrite_tac[eval_for_cons_round] >> disch_tac >>
  drule gas_marked_exec_ptr_exec >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  drule_all gas_admissible_bind_tail >> simp[] >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `SUC k` mp_tac) >> simp[]
QED
