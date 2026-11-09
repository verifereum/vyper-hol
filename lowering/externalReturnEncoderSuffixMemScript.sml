(* Conditional composition: the same safe encoder endpoint feeds RETURN. *)
Theory externalReturnEncoderSuffixMem
Ancestors
  abiEncoderWindowRunMem abiEncoderWindowContract terminalReturnMem
  memContinuationExit compileEnv venomExecSemantics venomState valueEncoding

Theorem window_return_destination:
  abi_encoder_window_pre ctx fn st en dst src ei at av sb cap d s /\
  window_strong_result ctx fn st en out at av d s t ==>
  eval_operand dst t = SOME (n2w d)
Proof
  strip_tac >>
  drule window_strong_result_labels >> strip_tac >>
  drule window_strong_result_public >> strip_tac >>
  qpat_x_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `dst` >>
  fs[abi_encoder_window_pre_def, abi_encoder_window_result_def,
     eval_operand_def] >> metis_tac[]
QED

Theorem abi_encoder_return_safe_exit:
  abi_encoder_admissible ei /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx fn st en dst src ei at av sb cap d s /\
  emit_inst RETURN [dst;out] [] en = (x,fin) /\
  fn_has_code en fin fn ==>
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
           mem_safe_run fuel ctx fn s
Proof
  strip_tac >>
  drule_all compile_abi_encode_to_buf_window_strong_mem >> strip_tac >>
  `abi_encoder_window_result ctx fn st en out at av d s t` by
    metis_tac[window_strong_result_public] >>
  `eval_operand dst t = SOME (n2w d)` by
    metis_tac[window_return_destination] >>
  `d + LENGTH (enc at av) <= t.vs_alloca_next` by
    (drule window_strong_result_growth >> strip_tac >>
     irule window_alloca_growth_frontier >> qexists_tac `s` >>
     fs[abi_encoder_window_pre_def]) >>
  `?fuel r. run_from fuel ctx fn t = r /\ exit_result r /\
            mem_safe_run fuel ctx fn t` by
    (irule emit_return_safe_exit >>
     fs[abi_encoder_window_result_def] >> metis_tac[]) >>
  metis_tac[mem_cont_sim_safe_exit]
QED
