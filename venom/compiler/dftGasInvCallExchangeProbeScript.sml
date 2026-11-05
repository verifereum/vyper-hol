Theory dftGasInvCallExchangeProbe
Ancestors
  dftGasOracleDefs dftRunRel venomExecSemantics venomInst venomState

Definition inv_call_probe_ctx_def:
  inv_call_probe_ctx = mk_venom_context
    [mk_raw_function "callee"
      [<| bb_label := "entry"; bb_instructions :=
          [mk_inst 10 RET [Lit 42w; Lit 0w] []] |>]] (SOME "callee")
End

Definition inv_call_probe_inst_def:
  inv_call_probe_inst = mk_inst 0 INVOKE [Label "callee"] ["r"]
End

Definition inv_call_probe_pure_def:
  inv_call_probe_pure = mk_inst 1 ADD [Lit 2w; Lit 3w] ["v"]
End

Theorem inv_call_probe_pair:
  dft_gas_swap_pair inv_call_probe_inst inv_call_probe_pure /\
  inst_wf inv_call_probe_inst /\ inst_wf inv_call_probe_pure
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem inv_call_probe_steps:
  ev_step (\event. 7w) [] 0 1 inv_call_probe_ctx inv_call_probe_inst
    (init_venom_state "caller") =
      OK (update_var "r" 42w (init_venom_state "caller")) /\
  ev_step (\event. 7w) [] 0 1 inv_call_probe_ctx inv_call_probe_pure
    (update_var "r" 42w (init_venom_state "caller") with vs_inst_idx := 1) =
      OK (update_var "v" 5w
        (update_var "r" 42w (init_venom_state "caller") with vs_inst_idx := 1)) /\
  ev_step (\event. 7w) [] 0 1 inv_call_probe_ctx inv_call_probe_pure
    (init_venom_state "caller") =
      OK (update_var "v" 5w (init_venom_state "caller")) /\
  ev_step (\event. 7w) [] 0 1 inv_call_probe_ctx inv_call_probe_inst
    (update_var "v" 5w (init_venom_state "caller") with vs_inst_idx := 1) =
      OK (update_var "r" 42w
        (update_var "v" 5w (init_venom_state "caller") with vs_inst_idx := 1))
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem inv_call_probe_normalized_result:
  (update_var "v" 5w
    (update_var "r" 42w (init_venom_state "caller") with vs_inst_idx := 1)
      with vs_inst_idx := 2) =
  (update_var "r" 42w
    (update_var "v" 5w (init_venom_state "caller") with vs_inst_idx := 1)
      with vs_inst_idx := 2)
Proof
  EVAL_TAC >> simp[wordsTheory.word_add_n2w, finite_mapTheory.FUPDATE_COMMUTES]
QED
