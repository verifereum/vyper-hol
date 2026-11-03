(* Native return reflection at a historically justified open-call boundary. *)
Theory dftOpenReturnHistory
Ancestors
  dftOpenHistory dftOpenAdequacy dftOpenMachine venomExecSemantics arithmetic list

Theorem dft_history_first_hit_interval:
  i <= j /\ E (FUNPOW N j c) /\
  (!t. i <= t /\ t < j ==> ~E (FUNPOW N t c)) ==>
  dft_first_hit N E (FUNPOW N i c) (j-i) (FUNPOW N j c)
Proof
  strip_tac >> simp[dft_first_hit_def] >>
  conj_tac
  >- (`j - i + i = j` by decide_tac >> metis_tac[FUNPOW_ADD]) >>
  rpt strip_tac >>
  `i <= j' + i /\ j' + i < j` by decide_tac >> metis_tac[FUNPOW_ADD]
QED

Theorem dft_history_run_return:
  dft_sparse_oracle a xs /\ i <= j /\ n0 <= n /\
  FUNPOW (dft_open_next a ctx) i initial =
    DftOpen (DftEnter callee budget start) stack n0 /\
  FUNPOW (dft_open_next a ctx) j initial =
    DftOpen (DftDone (IntRet ret cs)) stack n /\
  (!t. i <= t /\ t < j ==> ~dft_open_stack_exit stack
    (FUNPOW (dft_open_next a ctx) t initial)) ==>
  run_blocks budget ctx callee (dft_open_materialize xs n0 start) =
    IntRet ret (dft_open_materialize xs n cs)
Proof
  strip_tac >>
  `dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit stack)
    (FUNPOW (dft_open_next a ctx) i initial) (j-i)
    (FUNPOW (dft_open_next a ctx) j initial)` by
    (irule dft_history_first_hit_interval >> simp[dft_open_stack_exit_def]) >>
  `0 < j-i` by (Cases_on `i=j` >- gvs[] >> decide_tac) >>
  `dft_open_run_segment a xs ctx callee budget start stack n0
    (IntRet ret (dft_open_materialize xs n cs))` by
    (simp[dft_open_run_segment_def] >>
     qexistsl_tac [`IntRet ret cs`, `n`, `j-i`, `DftOpen (DftDone (IntRet ret cs)) stack n`] >>
     simp[dft_open_materialize_result_def, dft_open_result_eq_def,
          dft_open_classified_exit_def] >> gvs[]) >>
  drule_all dft_open_run_segment_reflect >>
  Cases_on `run_blocks budget ctx callee (dft_open_materialize xs n0 start)` >>
  simp[dft_open_result_eq_def]
QED

Theorem dft_history_invoke_materialize:
  dft_history_push ctx c (DftCaller fn budget bb inst caller) rest callee start n0 /\
  run_blocks budget ctx callee (dft_open_materialize xs n0 start) =
    IntRet ret (dft_open_materialize xs n cs) /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  step_inst budget ctx inst (dft_open_materialize xs n0 caller) =
    OK (dft_open_materialize xs n after)
Proof
  simp[dft_history_push_def] >> rpt strip_tac >> gvs[] >>
  `eval_operands ops (dft_open_materialize xs n0 caller) = SOME args` by
    simp[dft_open_materialize_def] >>
  simp[Once step_inst_def, dft_open_setup_materialize, dft_open_return_materialize]
QED

Theorem dft_history_live_return:
  dft_sparse_oracle a xs /\
  FUNPOW (dft_open_next a ctx) j (DftOpen initial [] nstart) =
    DftOpen (DftDone (IntRet ret cs)) (DftCaller fn budget bb inst caller::rest) n /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  ?p n0. p < j /\ n0 <= n /\
    FUNPOW (dft_open_next a ctx) p (DftOpen initial [] nstart) =
      DftOpen (DftAt fn budget bb caller) rest n0 /\
    get_instruction bb caller.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
    step_inst budget ctx inst (dft_open_materialize xs n0 caller) =
      OK (dft_open_materialize xs n after)
Proof
  strip_tac >> drule dft_history_top_origin >> strip_tac >>
  qexistsl_tac [`p`, `n0`] >> simp[] >>
  `dft_history_push ctx (DftOpen (DftAt fn budget bb caller) rest n0)
     (DftCaller fn budget bb inst caller) rest callee cs' n0` by
    (simp[dft_history_push_def] >> metis_tac[]) >>
  `run_blocks budget ctx callee (dft_open_materialize xs n0 cs') =
     IntRet ret (dft_open_materialize xs n cs)` by
    (irule dft_history_run_return >> simp[] >>
     goal_assum (drule_at (Pat `FUNPOW _ _ _ = DftOpen (DftEnter _ _ _) _ _`)) >>
     goal_assum (drule_at (Pat `FUNPOW _ _ _ = DftOpen (DftDone _) _ _`)) >>
     simp[] >> decide_tac) >>
  drule_all dft_history_invoke_materialize >> simp[]
QED
