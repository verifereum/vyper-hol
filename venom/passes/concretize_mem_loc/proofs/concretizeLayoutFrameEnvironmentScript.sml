Theory concretizeLayoutFrameEnvironment
Ancestors frameRelocationEnvironment concretizeLayoutReaderContext
  venomExecSemantics venomState list

(* These supplements ignore parameters, return tokens and allocation metadata.
   In particular paired internal calls need not pass equal arguments. *)
Theorem relocation_environment_setup_callee:
  relocation_env s t /\ relocation_reader_context s t /\
  setup_callee fn args s = SOME sc /\ ~NULL gn.fn_blocks ==>
  ?tc. setup_callee gn args' t = SOME tc /\
       relocation_env sc tc /\ relocation_reader_context sc tc
Proof
  simp[setup_callee_def] >> rpt strip_tac >>
  gvs[relocation_env_def, relocation_reader_context_def]
QED

Theorem relocation_environment_merge_callee_state:
  relocation_env s t /\ relocation_reader_context s t /\
  sc.vs_gas_readings = tc.vs_gas_readings ==>
  relocation_env (merge_callee_state s sc) (merge_callee_state t tc) /\
  relocation_reader_context (merge_callee_state s sc) (merge_callee_state t tc)
Proof
  simp[merge_callee_state_def, relocation_env_def,
       relocation_reader_context_def]
QED

Theorem relocation_environment_adopt_return_fmp:
  relocation_env s t /\ relocation_reader_context s t ==>
  relocation_env (adopt_return_fmp ir s) (adopt_return_fmp jr t) /\
  relocation_reader_context (adopt_return_fmp ir s) (adopt_return_fmp jr t)
Proof
  Cases_on `ir.iret_adopt_fmp` >> Cases_on `jr.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, relocation_env_def, relocation_reader_context_def]
QED

Theorem relocation_environment_fold_outputs[local]:
  !xs ys s t.
  relocation_env s t /\ relocation_reader_context s t ==>
  relocation_env
    (FOLDL (\s (v,x). update_var v x s) s xs)
    (FOLDL (\t (w,y). update_var w y t) t ys) /\
  relocation_reader_context
    (FOLDL (\s (v,x). update_var v x s) s xs)
    (FOLDL (\t (w,y). update_var w y t) t ys)
Proof
  Induct
  >- (Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
      fs[] >> strip_tac >> first_x_assum irule >>
      gvs[relocation_env_def, relocation_reader_context_def, update_var_def]) >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> disch_tac >>
  first_x_assum irule >>
  gvs[relocation_env_def, relocation_reader_context_def, update_var_def]
QED

Theorem relocation_environment_bind_outputs:
  relocation_env s t /\ relocation_reader_context s t /\
  bind_outputs outs vals s = SOME post /\
  LENGTH outs' = LENGTH vals' ==>
  ?post'. bind_outputs outs' vals' t = SOME post' /\
    relocation_env post post' /\ relocation_reader_context post post'
Proof
  simp[bind_outputs_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  irule relocation_environment_fold_outputs >> simp[]
QED

Theorem relocation_environment_return_plumbing:
  relocation_env s t /\ relocation_reader_context s t /\
  sc.vs_gas_readings = tc.vs_gas_readings /\
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state s sc)) =
    SOME post /\ LENGTH outs' = LENGTH vals' ==>
  ?post'.
    bind_outputs outs' vals' (adopt_return_fmp jr (merge_callee_state t tc)) =
      SOME post' /\
    relocation_env post post' /\ relocation_reader_context post post'
Proof
  rpt strip_tac >>
  drule_all relocation_environment_merge_callee_state >> strip_tac >>
  drule_all relocation_environment_adopt_return_fmp >>
  disch_then (qspecl_then [`jr`, `ir`] strip_assume_tac) >>
  drule_all relocation_environment_bind_outputs >> simp[]
QED
