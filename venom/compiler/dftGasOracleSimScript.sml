(*
 * DFT simulates in the oracle semantics (dftGasOracleDefs) at the same
 * oracle and fuel: DFT keeps each block, its instruction ids and the fuel
 * it runs at, so a GAS read in either context reads the same word.
 *
 * TOP-LEVEL:
 *   dft_ev_context_sim - a terminating oracle run of C is one of C'
 *)
Theory dftGasOracleSim
Ancestors
  dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs o1PassContract
  unitShapeDefs venomExecSemantics dftGasSimFuel passSimulationDefs venomInst list rich_list

(* The hypotheses are dft_ctx_sim_gas's (dftContractGas).  o1_ctx_shape C
   gives inst_shape_ok for every instruction (no DJMP or OFFSET). *)
Theorem dft_ev_context_sim:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  terminates (ev_context orc fuel C s) ==>
  dft_res_rel (ev_context orc fuel C s) (ev_context orc fuel C' s)
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `!f. (dft_fn f).fn_name = f.fn_name` by
    (gen_tac >> simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  qpat_x_assum `terminates _` mp_tac >> simp[ev_context_def] >>
  Cases_on `C.ctx_entry` >> simp[terminates_def] >>
  rename1 `lookup_function nm C.ctx_functions` >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  simp[terminates_def, lookup_function_map] >>
  rename1 `lookup_function nm C.ctx_functions = SOME fn` >>
  strip_tac >> drule lookup_function_MEM >> strip_tac >>
  irule ev_function_frame_sim >>
  gvs[o1_run_state_ok_def, terminates_def] >>
  qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[MEM_EL]
QED

Theorem dft_ev_context_revert_empty:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  ev_context orc fuel C s = Abort Revert_abort a /\ a.vs_returndata = [] ==>
  ?b. ev_context orc fuel C' s = Abort Revert_abort b /\ b.vs_returndata = []
Proof
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    (qpat_assum `LIST_REL (\fn fn'. fn' = dft_fn fn) _ _` mp_tac >>
     pure_rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
     simp[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
  `!f. (dft_fn f).fn_name = f.fn_name` by
    (gen_tac >> simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  qpat_x_assum `ev_context _ _ _ _ = _` mp_tac >> simp[ev_context_def] >>
  Cases_on `C.ctx_entry` >> simp[] >>
  rename1 `lookup_function nm C.ctx_functions` >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  simp[lookup_function_map] >>
  rename1 `lookup_function nm C.ctx_functions = SOME fn` >>
  strip_tac >> drule lookup_function_MEM >> strip_tac >>
  `dft_fn_rel fn (dft_fn fn)` by
    (qpat_x_assum `LIST_REL dft_fn_rel _ _` mp_tac >>
     simp[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[MEM_EL]) >>
  `terminates (ev_function orc fuel C fn (s with vs_prev_bb := NONE))` by
    simp[terminates_def] >>
  `ctx_labels_bound C (s with vs_prev_bb := NONE).vs_labels /\
   ~(s with vs_prev_bb := NONE).vs_call_ctx.cc_static` by
    gvs[o1_run_state_ok_def] >>
  drule_at (Pat `terminates _`) ev_function_frame_sim_revert_empty >>
  disch_then (qspec_then `dft_fn fn` mp_tac) >>
  simp[] >> metis_tac[]
QED
