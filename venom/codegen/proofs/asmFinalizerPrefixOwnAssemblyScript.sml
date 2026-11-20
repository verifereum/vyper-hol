Theory asmFinalizerPrefixOwnAssembly
Ancestors
  asmFinalizerPrefixFrame asmFinalizerPrefixStatic asmFinalizerPrefixOwn
  codegenEntryRel codegenSymRel asmDataEnv asmSymBridge asmSymSem arithmetic
  asmRelocDataEnv asmSymOwnStep asmSymModeOwn asmSymForwardOwn asmSpliceOwn
  fnPlanPlaceRevertPostamble asmSem

val transport_own = ``\p q.
  ?K. 0 < K /\ !env own s n a.
    s.as_pc = 0 /\ sym_steps_own p env own n (sym_init s) = SymOK a ==>
    (?m b. sym_steps_own q env own m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
       a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
     ?m b. sym_steps_own q env own m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp op /\
       (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
       MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
       FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)``;

Theorem asm_sym_rel_own_gas_readings[local]:
  asm_sym_rel_own lo p env own cs ss ==>
  ss.sym_base.as_gas_readings = cs.as_gas_readings
Proof
  simp[asm_sym_rel_own_def] >> rpt strip_tac >> gvs[]
QED

Theorem focus_finalizer_prefix_bridge_own_conditional:
  !fin rpolicy prog prog' vs0 es0 result final.
    ^transport_own prog prog' /\
    asm_static_wf prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0) es0 /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?max_cost. !n ast.
      asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
        prog n (entry_asm_state vs0 es0) = AsmOK ast /\
      (?ss. sym_steps_own prog (asm_data_env prog' vs0.vs_code) vs0.vs_code n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
      n <= max_cost /\
      (ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" ==>
        ast.as_gas_readings <> [])
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  drule_all finalizer_prefix_static >>
  disch_then (qspec_then `vs0.vs_data_section` strip_assume_tac) >>
  drule_all finalizer_frame_prefix_ready >>
  disch_then (qx_choose_then `B` assume_tac) >>
  qabbrev_tac `own = vs0.vs_code` >>
  qabbrev_tac `env = asm_data_env prog' own` >>
  qabbrev_tac `lo = lo_reloc prog prog'` >>
  qabbrev_tac `s = entry_asm_state vs0 es0` >>
  `s.as_pc = 0 /\ s.as_code = own` by simp[Abbr `s`, Abbr `own`, entry_asm_state_def] >>
  `code_labels_agree prog lo` by simp[Abbr `lo`, lo_reloc_code_labels_agree] >>
  `asm_sym_rel_own lo prog env own s (sym_init s)` by
    (irule asm_sym_rel_own_init >> simp[Abbr `lo`, Abbr `env`] >>
     metis_tac[lo_reloc_data_env]) >>
  `asm_sym_rel_own (SND (compute_label_offsets prog')) prog' env own s (sym_init s)` by
    (irule asm_sym_rel_own_init >>
     simp[Abbr `env`, asm_data_env_lo_ok_canonical, asm_data_env_ok_asm_data_env]) >>
  `code_labels_agree prog' (SND (compute_label_offsets prog'))` by
    MATCH_ACCEPT_TAC code_labels_agree_refl >>
  `!n ss. sym_steps_own prog' env own n (sym_init s) = SymOK ss ==>
     n <= B /\ (ss.sym_base.as_pc < LENGTH prog' /\
       EL ss.sym_base.as_pc prog' = AsmOp "GAS" ==> ss.sym_base.as_gas_readings <> [])` by
    (rpt gen_tac >> strip_tac >>
     drule_all (SIMP_RULE bool_ss [sym_steps_mode_def] (Q.INST
       [`allow_own` |-> `T`, `p` |-> `prog'`] asm_sym_steps_mode_sim)) >>
     strip_tac >>
     qpat_assum `!n b. asm_steps _ _ prog' _ _ = _ ==> _` drule >> strip_tac >>
     qpat_assum `asm_sym_rel_own _ prog' env own cs' ss`
       (fn th => mp_tac (MATCH_MP asm_sym_rel_own_pc th) >>
                 mp_tac (MATCH_MP asm_sym_rel_own_gas_readings th)) >> simp[]) >>
  rename1 `0 < k` >> qexists_tac `k * (B + 1)` >> rpt gen_tac >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `T`, `p` |-> `prog`] asm_sym_steps_mode_sim)) >> strip_tac >>
  `cs' = ast` by metis_tac[asm_result_11] >> pop_assum SUBST_ALL_TAC >>
  qpat_assum `asm_sym_rel_own lo prog env own ast ss`
    (fn th => assume_tac (MATCH_MP asm_sym_rel_own_pc th) >>
              assume_tac (MATCH_MP asm_sym_rel_own_gas_readings th)) >>
  qpat_assum `!env own s n a. _` (qspecl_then [`env`,`own`,`s`,`n`,`ss`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> conj_tac
  >- (qpat_assum `!n ss. _ ==> n <= B /\ _` drule >> strip_tac >>
      irule LESS_EQ_TRANS >> qexists_tac `k * (m + 1)` >> simp[]) >>
  strip_tac >> qpat_x_assum `!op. _ ==> ?m b. _` (qspec_then `"GAS"` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`m_gas`,`b_gas`] strip_assume_tac) >>
  qpat_x_assum `sym_steps_own prog' _ _ m _ = _` kall_tac >>
  qpat_assum `!n ss. _ ==> n <= B /\ _` drule >> strip_tac >>
  `b_gas.sym_base.as_gas_readings = ss.sym_base.as_gas_readings` by
    fs[asm_state_component_equality] >> metis_tac[]
QED

Theorem focus_finalizer_prefix_bridge_own:
  !fin rpolicy prog prog' vs0 es0 result final.
    asm_static_wf prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0) es0 /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?max_cost. !n ast.
      asm_steps (lo_reloc prog prog') (build_offset_to_pc prog)
        prog n (entry_asm_state vs0 es0) = AsmOK ast /\
      (?ss. sym_steps_own prog (asm_data_env prog' vs0.vs_code) vs0.vs_code n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
      n <= max_cost /\
      (ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" ==>
        ast.as_gas_readings <> [])
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac (BETA_RULE accepted_finalizers_prefix_transport_own) >>
  drule_all_then ACCEPT_TAC (BETA_RULE focus_finalizer_prefix_bridge_own_conditional)
QED
