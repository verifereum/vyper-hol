(* Bounded native probe, not a multi-fuel or raw-adequacy theorem. *)
Theory dftReservationNativeProbe
Ancestors
  dftOpenReservation venomExecSemantics venomInst venomState contextRawReachable unitMemInv

Definition reservation_probe_gas_def:
  reservation_probe_gas = mk_inst 0 GAS [] ["g"]
End
Definition reservation_probe_call_def:
  reservation_probe_call = mk_inst 1 INVOKE [Label "callee"] []
End
Definition reservation_probe_callee_def:
  reservation_probe_callee = mk_raw_function "callee"
    [<|bb_label := "ce"; bb_instructions :=
        [mk_inst 2 GAS [] ["cg"];
         mk_inst 3 MSTORE [Lit 0w; Var "cg"] [];
         mk_inst 4 JMP [Label "exit"] []]|>;
     <|bb_label := "exit"; bb_instructions := [mk_inst 5 RET [Lit 0w] []]|>]
End
Definition reservation_probe_caller_def:
  reservation_probe_caller source = mk_raw_function "main"
    [<|bb_label := "entry"; bb_instructions :=
      (if source then [reservation_probe_gas; reservation_probe_call]
       else [reservation_probe_call; reservation_probe_gas]) ++
      [mk_inst 6 RET [Var "g"; Lit 0w] []]|>]
End
Definition reservation_probe_ctx_def:
  reservation_probe_ctx source = mk_venom_context
    [reservation_probe_caller source; reservation_probe_callee] (SOME "main")
End
Definition reservation_probe_state_def:
  reservation_probe_state source = init_venom_state "entry" with
    vs_gas_readings := if source then [29w;11w] else [11w;29w]
End

Theorem reservation_probe_oracle:
  (!j. dft_reserve_oracle 1 (\n. if n=0 then 11w else if n=1 then 29w else 0w) j =
    if j=0 then 29w else if j=1 then 11w else 0w)
Proof
  simp[dft_reserve_oracle_def, dft_reserve_index_def] >>
  gen_tac >> Cases_on `j` >> simp[] >> Cases_on `n` >> simp[]
QED

Theorem reservation_probe_small_fuel:
  run_blocks 2 (reservation_probe_ctx T) (reservation_probe_caller T)
    (reservation_probe_state T) = Error "out of fuel" /\
  run_blocks 2 (reservation_probe_ctx F) (reservation_probe_caller F)
    (reservation_probe_state F) = Error "out of fuel"
Proof
  EVAL_TAC
QED

Theorem reservation_probe_large_fuel:
  ?s. run_blocks 3 (reservation_probe_ctx T) (reservation_probe_caller T)
       (reservation_probe_state T) =
       IntRet <|iret_values := [29w]; iret_adopt_fmp := NONE|> s /\
      run_blocks 3 (reservation_probe_ctx F) (reservation_probe_caller F)
       (reservation_probe_state F) =
       IntRet <|iret_values := [29w]; iret_adopt_fmp := NONE|> s /\
      s.vs_gas_readings = []
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition reservation_probe_callstate_def:
  reservation_probe_callstate source =
    if source then update_var "g" 29w (reservation_probe_state source) with
      <|vs_inst_idx := 1; vs_gas_readings := [11w]|>
    else reservation_probe_state source
End
Definition reservation_probe_cs_def:
  reservation_probe_cs source =
    THE (setup_callee reservation_probe_callee [] (reservation_probe_callstate source))
End
Definition reservation_probe_memstate_def:
  reservation_probe_memstate source =
    update_var "cg" 11w (reservation_probe_cs source) with
      <|vs_inst_idx := 1; vs_gas_readings := DROP 1 (reservation_probe_cs source).vs_gas_readings|>
End

Theorem reservation_probe_call_reachable:
  !source. raw_reachable (reservation_probe_state source) (reservation_probe_ctx source)
    (reservation_probe_caller source) reservation_probe_call (reservation_probe_callstate source)
Proof
  reverse Cases
  >- (simp[reservation_probe_callstate_def] >>
      irule (cj 1 raw_reachable_rules) >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]) >>
  `raw_reachable (reservation_probe_state T) (reservation_probe_ctx T)
    (reservation_probe_caller T) reservation_probe_gas (reservation_probe_state T)`
    by (irule (cj 1 raw_reachable_rules) >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]) >>
  `raw_reachable (reservation_probe_state T) (reservation_probe_ctx T)
    (reservation_probe_caller T) reservation_probe_call
    ((update_var "g" 29w (reservation_probe_state T) with vs_gas_readings := [11w])
      with vs_inst_idx := SUC (reservation_probe_state T).vs_inst_idx)`
    suffices_by (EVAL_TAC >> simp[]) >>
  irule (cj 2 raw_reachable_rules) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexistsl_tac [`0`, `reservation_probe_gas`] >>
  simp[] >> EVAL_TAC >> simp[]
QED

Theorem reservation_probe_memory_reachable:
  !source. raw_reachable (reservation_probe_state source) (reservation_probe_ctx source)
    reservation_probe_callee (mk_inst 3 MSTORE [Lit 0w; Var "cg"] [])
    (reservation_probe_memstate source)
Proof
  gen_tac >>
  `raw_reachable (reservation_probe_state source) (reservation_probe_ctx source)
     reservation_probe_callee (mk_inst 2 GAS [] ["cg"]) (reservation_probe_cs source)`
    by (irule (cj 4 raw_reachable_rules) >>
        conj_tac >- (simp[contextCodegenRelTheory.active_inst_def] >>
          qexists_tac `HD reservation_probe_callee.fn_blocks` >>
          Cases_on `source` >> EVAL_TAC >> simp[]) >>
        qexistsl_tac [`[]`, `reservation_probe_caller source`, `reservation_probe_cs source`,
          `reservation_probe_call`, `"callee"`, `[]`, `reservation_probe_callstate source`] >>
        simp[reservation_probe_call_reachable] >>
        Cases_on `source` >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]) >>
  `raw_reachable (reservation_probe_state source) (reservation_probe_ctx source)
    reservation_probe_callee (mk_inst 3 MSTORE [Lit 0w; Var "cg"] [])
    ((update_var "cg" 11w (reservation_probe_cs source) with
      vs_gas_readings := DROP 1 (reservation_probe_cs source).vs_gas_readings)
     with vs_inst_idx := SUC (reservation_probe_cs source).vs_inst_idx)`
    suffices_by (Cases_on `source` >> EVAL_TAC >> simp[]) >>
  irule (cj 2 raw_reachable_rules) >>
  conj_tac >- (simp[contextCodegenRelTheory.active_inst_def] >>
    qexists_tac `HD reservation_probe_callee.fn_blocks` >>
    Cases_on `source` >> EVAL_TAC >> simp[]) >>
  qexistsl_tac [`0`, `mk_inst 2 GAS [] ["cg"]`] >> simp[] >>
  conj_tac >- (Cases_on `source` >> EVAL_TAC >> simp[]) >>
  conj_tac >- (Cases_on `source` >> EVAL_TAC >> simp[]) >>
  simp[contextCodegenRelTheory.active_inst_def] >>
  qexists_tac `HD reservation_probe_callee.fn_blocks` >>
  Cases_on `source` >> EVAL_TAC >> simp[]
QED

Theorem reservation_probe_memory_observation:
  inst_mem_ranges (mk_inst 3 MSTORE [Lit 0w; Var "cg"] []) (reservation_probe_memstate T) =
  inst_mem_ranges (mk_inst 3 MSTORE [Lit 0w; Var "cg"] []) (reservation_probe_memstate F) /\
  (reservation_probe_memstate T).vs_initial_fmp =
  (reservation_probe_memstate F).vs_initial_fmp
Proof
  EVAL_TAC >> simp[]
QED
