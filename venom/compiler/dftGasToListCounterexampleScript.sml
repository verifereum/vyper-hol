Theory dftGasToListCounterexample
Ancestors
  dftGasOracleDefs contextRawReachable contextCodegenRel venomExecSemantics
  venomInst venomState finite_map pred_set list words

Definition dup_gas_def:
  dup_gas n = mk_inst n GAS [] ["x"]
End
Definition dup_stop_def:
  dup_stop = mk_inst 2 STOP [] []
End
Definition dup_block_def:
  dup_block n = <|bb_label := "b"; bb_instructions := [dup_gas n; dup_stop]|>
End
Definition dup_fn_def:
  dup_fn = mk_raw_function "f" [dup_block 0; dup_block 1]
End
Definition dup_ctx_def:
  dup_ctx = <|ctx_functions := [dup_fn]; ctx_entry := SOME "f";
              ctx_global_reserved := []|>
End
Definition dup_state_def:
  dup_state = init_venom_state "b"
End
Definition dup_orc_def:
  dup_orc (e:gas_event) = if e = ([],1,1) then 1w else 0w
End
Definition dup_after_def:
  dup_after w = (update_var "x" w dup_state) with vs_inst_idx := 1
End

Theorem dup_eval:
  lookup_function "f" dup_ctx.ctx_functions = SOME dup_fn /\
  fn_entry_label dup_fn = SOME "b" /\
  enters_block dup_fn dup_state dup_state /\
  active_inst dup_fn (dup_gas 0) dup_state /\
  active_inst dup_fn (dup_gas 1) dup_state /\
  active_inst dup_fn dup_stop (dup_after 0w) /\
  active_inst dup_fn dup_stop (dup_after 1w) /\
  ev_step dup_orc [] 1 0 dup_ctx (dup_gas 0) dup_state = OK (update_var "x" 0w dup_state) /\
  ev_step dup_orc [] 1 0 dup_ctx (dup_gas 1) dup_state = OK (update_var "x" 1w dup_state)
Proof
  simp[dup_ctx_def, dup_fn_def, dup_block_def, dup_gas_def, dup_stop_def,
       dup_after_def, mk_raw_function_def, mk_inst_def, enters_block_def,
       active_inst_def, lookup_function_def, fn_entry_label_def, lookup_block_def,
       eval_phis_def, phi_prefix_length_def, dup_state_def, init_venom_state_def,
       update_var_def] >> EVAL_TAC >>
  simp[SF DNF_ss, eval_phis_def, phi_prefix_length_def]
QED

Theorem dup_finite:
  FINITE {e | dup_orc e <> 0w}
Proof
  ` {e | dup_orc e <> 0w} = {([],1,1)}` by
    (simp[EXTENSION, dup_orc_def] >> gen_tac >>
     Cases_on `x = ([],1,1)` >> simp[]) >> simp[]
QED

Theorem dup_oracle_entry:
  ev_reachable dup_orc dup_state dup_ctx [] 1 dup_fn (dup_gas 0) dup_state /\
  ev_reachable dup_orc dup_state dup_ctx [] 1 dup_fn (dup_gas 1) dup_state
Proof
  `dup_ctx.ctx_entry = SOME "f"` by EVAL_TAC >>
  `dup_state with <|vs_prev_bb := NONE; vs_current_bb := "b"; vs_inst_idx := 0|> = dup_state`
    by EVAL_TAC >>
  conj_tac >> irule ev_reachable_entry >> simp[dup_eval] >>
  metis_tac[dup_eval]
QED

Theorem dup_oracle_after:
  ev_reachable dup_orc dup_state dup_ctx [] 1 dup_fn dup_stop (dup_after 0w) /\
  ev_reachable dup_orc dup_state dup_ctx [] 1 dup_fn dup_stop (dup_after 1w)
Proof
  `dup_state.vs_inst_idx = 0` by EVAL_TAC >>
  `~is_terminator (dup_gas 0).inst_opcode /\ ~is_terminator (dup_gas 1).inst_opcode`
    by EVAL_TAC >>
  `SUC dup_state.vs_inst_idx = 1` by simp[] >>
  metis_tac[ev_reachable_next, dup_oracle_entry, dup_eval, dup_after_def]
QED

Definition dup_head_def:
  dup_head (W:256 word list) = if W = [] then 0w else HD W
End
Definition dup_list_after_def:
  dup_list_after W = dup_after (dup_head W) with
    vs_gas_readings := (if W = [] then [] else TL W)
End

Theorem dup_raw_invariant:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==>
    !W. vs0 = (dup_state with vs_gas_readings := W) /\ ctx = dup_ctx ==>
      fn = dup_fn /\
      ((s = (dup_state with vs_gas_readings := W) /\
        (inst = dup_gas 0 \/ inst = dup_gas 1)) \/
       (s = dup_list_after W /\ inst = dup_stop))
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> gvs[] >>
      `dup_ctx.ctx_entry = SOME "f"` by EVAL_TAC >>
      gvs[dup_eval] >>
      gvs[enters_block_def, lookup_block_def, dup_fn_def, mk_raw_function_def,
          dup_block_def, listTheory.FIND_def, listTheory.INDEX_FIND_def, dup_gas_def, mk_inst_def,
          eval_phis_def, phi_prefix_length_def] >>
      gvs[active_inst_def, dup_fn_def, mk_raw_function_def, dup_block_def,
          dup_state_def, init_venom_state_def, dup_gas_def, mk_inst_def,
          SF DNF_ss])
  >- (rpt gen_tac >> strip_tac >> qx_gen_tac `readings` >> strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[dup_stop_def, dup_gas_def, mk_inst_def, is_terminator_def] >>
      gvs[Once run_defs, step_inst_base_def, exec_gas_def] >>
      Cases_on `readings` >>
      gvs[dup_list_after_def, dup_head_def, dup_after_def, update_var_def,
          dup_state_def, init_venom_state_def, active_inst_def, dup_fn_def,
          mk_raw_function_def, dup_block_def, dup_gas_def, dup_stop_def, mk_inst_def,
          SF DNF_ss])
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      gvs[dup_stop_def, dup_gas_def, mk_inst_def, is_terminator_def] >>
      gvs[Once run_defs, step_inst_base_def])
  >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[dup_stop_def, dup_gas_def, mk_inst_def]
QED

Theorem dup_raw_value:
  !W w ws. raw_reachable (dup_state with vs_gas_readings := W) dup_ctx
    dup_fn dup_stop (dup_after w with vs_gas_readings := ws) ==>
  w = dup_head W
Proof
  map_every qx_gen_tac [`readings`, `w`, `ws`] >> strip_tac >>
  drule dup_raw_invariant >> disch_then (qspec_then `readings` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[dup_stop_def, dup_gas_def, mk_inst_def] >>
  ` (dup_after w with vs_gas_readings := ws).vs_vars =
    (dup_list_after readings).vs_vars` by metis_tac[] >>
  gvs[dup_after_def, dup_list_after_def, update_var_def, dup_state_def,
      init_venom_state_def, finite_mapTheory.FUPDATE_EQ] >>
  `FLOOKUP (FEMPTY |+ ("x",w)) "x" =
   FLOOKUP (FEMPTY |+ ("x",dup_head readings)) "x"` by metis_tac[] >>
  pop_assum mp_tac >> simp[NoAsms, FLOOKUP_UPDATE]
QED

Theorem dup_no_list:
  ~(?W. !p d fn inst t.
    ev_reachable dup_orc dup_state dup_ctx p d fn inst t ==>
    ?ws. raw_reachable (dup_state with vs_gas_readings := W) dup_ctx
      fn inst (t with vs_gas_readings := ws))
Proof
  disch_then (qx_choose_then `readings` assume_tac) >>
  `(?ws. raw_reachable (dup_state with vs_gas_readings := readings) dup_ctx
       dup_fn dup_stop (dup_after 0w with vs_gas_readings := ws)) /\
   (?ws. raw_reachable (dup_state with vs_gas_readings := readings) dup_ctx
       dup_fn dup_stop (dup_after 1w with vs_gas_readings := ws))`
    by metis_tac[dup_oracle_after] >>
  `0w <> (1w:256 word)` by simp[] >> metis_tac[dup_raw_value]
QED

(* The frozen theorem's conclusion is false for this finite-support oracle. *)
Theorem gas_oracle_to_list_counterexample:
  FINITE {e | dup_orc e <> 0w} /\
  ~(?W. (!fuel. gas_res_rel
      (run_context fuel dup_ctx (dup_state with vs_gas_readings := W))
      (ev_context dup_orc fuel dup_ctx dup_state)) /\
    (!p d fn inst t. ev_reachable dup_orc dup_state dup_ctx p d fn inst t ==>
       ?ws. raw_reachable (dup_state with vs_gas_readings := W) dup_ctx fn inst
         (t with vs_gas_readings := ws)))
Proof
  metis_tac[dup_finite, dup_no_list]
QED
