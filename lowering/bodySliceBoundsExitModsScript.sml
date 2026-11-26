(* Out-of-range ordinary Slice exits in the scalar bounds prefix. *)
Theory bodySliceBoundsExitMods
Ancestors
  bodyFullBuiltinBytestringAbort bodyPtrBytestringBuiltinsBounds
  gasOutcomeFullPostMods exprSimDefs fragExec vyperState venomState

Theorem slice_bounds_exit_mods:
  compile_assert_slice_bounds start cnt limit sa = ((),sc) /\
  fn_has_code sa sc func /\
  eval_operand start s = SOME (n2w i) /\
  eval_operand cnt s = SOME (n2w k) /\
  eval_operand limit s = SOME (n2w cap) /\
  (!op. MEM op [start;cnt;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)) /\
  i < dimword (:256) /\ k < dimword (:256) /\ cap < dimword (:256) /\
  ~(i+k <= cap) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. source (es with gas_obs := tail) =
    (INR (Error (RuntimeError "evaluate_slice range")) : eval_result + exception,
     es with gas_obs := tail)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  `!op z. MEM op [start;cnt;limit] /\ op = Var z ==> not_fresh_at sa z` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then strip_assume_tac slice_bounds_reserved_natural_runtime >>
  `cap < i+k` by decide_tac >>
  `run_inst_seq (emitted_insts sa sc) s =
     Abort Revert_abort (revert_state (set_returndata [] p))` by simp[] >>
  drule_all bytestring_slice_bounds_full_abort >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`, `es`, `INR (Error (RuntimeError "evaluate_slice range"))`,
    `tn'`, `revert_state (set_returndata [] p) with vs_inst_idx := s.vs_inst_idx+5`] >>
  simp[exit_result_def, expr_exit_def, halt_exit_def]
QED
