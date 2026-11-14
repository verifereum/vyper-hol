(* Conditional fold of the current, interleaved staging compiler. *)
Theory bodyIntCallNRStageTraversal
Ancestors
  bodyIntCallFamCallIntStageInterface bodyIntCallJointCallCore
  bodyIntCallFamStmtLogGas exprSimSliceCompose stmtReasonVvMemory
  exprSimWordArgs exprLowering

(* Same certificate quotation as StageInterface; no new HOL definitions. *)
val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;
val stage_inv = ``\(ds:expr list) (fs:bool list) (ts:type list)
  (pts:type list) (pfs:bool list) (pvs:value list) (pops:operand list)
  (ee:evaluation_state) (sc:compile_state) (st:venom_state).
  J ds fs ts pts pfs pvs pops ee sc st /\ ~st.vs_halted /\
  LENGTH ds = LENGTH fs /\ LENGTH ds = LENGTH ts /\
  ^completed_prefix cx start sc pts pfs pvs pops st``;
val reset = ``!(ds:expr list) (fs:bool list) (ts:type list)
  (pts:type list) (pfs:bool list) (pvs:value list) (pops:operand list)
  (ee:evaluation_state) (sc:compile_state) (st:venom_state).
  J ds fs ts pts pfs pvs pops ee sc st ==>
  J ds fs ts pts pfs pvs pops (ee with gas_obs := []) sc st``;
val head = ``!h ds f fs ty ts pts pfs pvs pops ee sc st out fin.
  ^stage_inv (h::ds) (f::fs) (ty::ts) pts pfs pvs pops ee sc st /\
  compile_stage_intcall_args compile_expr ce (h::ds) (f::fs) (ty::ts) sc = (out,fin) ==>
  ?op next rest. out = op::rest /\
    compile_stage_intcall_args compile_expr ce ds fs ts next = (rest,fin) /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (vyperState$bind (eval_expr cx h) (read_result cx)) (ee,st)
      (\res mid u. ?v. res = INL v /\
        ^stage_inv ds fs ts (pts++[ty]) (pfs++[f]) (pvs++[v]) (pops++[op]) mid next u)
      (\res mid r. expr_exit res r)``;

Theorem intcall_stage_current_fold[local]:
  ^reset /\ ^head ==>
  !ds fs ts pts pfs pvs pops ee sc st out fin.
  ^stage_inv ds fs ts pts pfs pvs pops ee sc st /\
  compile_stage_intcall_args compile_expr ce ds fs ts sc = (out,fin) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx ds) (ee,st)
    (\res mid u. ?vs. res = INL vs /\
      ^stage_inv [] [] [] (pts++ts) (pfs++fs) (pvs++vs) (pops++out) mid fin u)
    (\res mid r. expr_exit res r)
Proof
  strip_tac >> Induct_on `ds`
  >- suspend "nil" >>
  suspend "cons"
QED

Resume intcall_stage_current_fold[nil]:
  rpt gen_tac >> strip_tac >>
  gvs[compile_stage_intcall_args_def, compileEnvTheory.comp_return_def] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil, vyperStateTheory.return_def] >>
  pop_assum SUBST1_TAC >>
  irule intcall_gas_outcome_return >> simp[] >> metis_tac[]
QED

Resume intcall_stage_current_fold[cons]:
  rpt gen_tac >> disch_tac >>
  Cases_on `fs` >- gvs[] >>
  Cases_on `ts` >- gvs[] >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `!h ds f fs ty ts pts pfs pvs pops ee sc st out fin. _`
    (drule_all_then strip_assume_tac) >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "tail" >>
  Cases >> simp[] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume intcall_stage_current_fold[tail]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res mid u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  BETA_TAC >>
  irule (bodyIntCallFamStmtLogGasTheory.gas_outcome_return_map
    |> INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value list``]
    |> Q.INST [`f` |-> `CONS (v:value)`]) >>
  qpat_x_assum `!fs ts pts pfs pvs pops ee sc st out fin. _`
    (drule_at_then (Pat `compile_stage_intcall_args _ _ _ _ _ _ = _`) mp_tac) >>
  disch_then (drule_all_then assume_tac o BETA_RULE) >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- simp[exprSimDefsTheory.expr_exit_success_map] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  strip_tac >> gvs[]
QED

Finalise intcall_stage_current_fold

Theorem intcall_stage_current_traverse:
  ^reset /\ ^head /\
  ^stage_inv ds fs ts pts pfs pvs pops ee sc st /\
  compile_stage_intcall_args compile_expr ce ds fs ts sc = (out,fin) /\
  (!vs mid u.
    ^stage_inv [] [] [] (pts++ts) (pfs++fs) (pvs++vs) (pops++out) mid fin u ==>
    Q (INL vs) mid u) /\
  (!ex mid r. exit_result r /\ expr_exit (INR ex) r ==> R (INR ex) mid r) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx ds) (ee,st) Q R
Proof
  strip_tac >>
  drule_all intcall_stage_current_fold >> strip_tac >>
  irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
  conj_tac
  >- (Cases >> simp[] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!ex mid r. _` irule >> simp[] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `y` >> Cases_on `r` >>
      simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >>
      rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >>
      simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!vs mid u. _` irule >> simp[]
QED
