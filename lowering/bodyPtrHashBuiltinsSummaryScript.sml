(* Zero-mark suffix packaging for deterministic gas-independent actions. *)
Theory bodyPtrHashBuiltinsSummary
Ancestors fragGasPathPtr gasOutcome gasSummary vyperState list

Theorem hash_zero_mark_summary:
  (!tail. source (es with gas_obs := tail) = (res,ef with gas_obs := tail)) /\
  ef.gas_obs = [] /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
  Q res ef G' tn' t ==>
  gas_summary_ptr_at D (ctx,fn) PG [] source (es,s,G,tn) Q R
Proof
  strip_tac >>
  `ef with gas_obs := [] = ef` by
    simp[evaluation_state_component_equality] >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`res`, `ef`, `G'`, `tn'`, `OK t`] >>
  simp[gas_explicit_def]
QED
