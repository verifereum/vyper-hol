Theory asmFinalizerPrefixAssembly
Ancestors
  asmFinalizerPrefixFrame asmFinalizerPrefixStatic codegenAsmStaticWf
  codegenEntryRel codegenSymRel asmDataEnv asmSymBridge asmSymSem arithmetic

val transport = ``\p q.
  ?K. 0 < K /\
    !env s n a.
      s.as_pc = 0 /\
      sym_steps p env n (sym_init s) = SymOK a ==>
      (?m b. sym_steps q env m (sym_init s) = SymOK b /\
             n <= K * (m + 1)) /\
      (a.sym_base.as_pc < LENGTH p /\
       EL a.sym_base.as_pc p = AsmOp "GAS" ==>
       ?m b. sym_steps q env m (sym_init s) = SymOK b /\
             b.sym_base.as_pc < LENGTH q /\
             EL b.sym_base.as_pc q = AsmOp "GAS" /\
             b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

Theorem focus_finalizer_prefix_bridge_conditional:
!fin rpolicy unit cpl prog prog' vs0 es0 result final.
    ^transport prog prog' /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    generate_context_plan unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    codegen_ready unit.cu_context /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?max_cost. !n ast.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n (entry_asm_state vs0 es0) = AsmOK ast /\
      (?ss. sym_steps prog (asm_data_env prog vs0.vs_code) n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
      n <= max_cost /\
      (ast.as_pc < LENGTH prog /\ EL ast.as_pc prog = AsmOp "GAS" ==>
        ast.as_gas_readings <> [])
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `asm_static_wf prog` by metis_tac[codegen_asm_static_wf] >>
  drule_all finalizer_prefix_static >>
  disch_then (qspec_then `vs0.vs_data_section` strip_assume_tac) >>
  drule_all finalizer_frame_prefix_ready >>
  disch_then (qx_choose_then `B` assume_tac) >>
  rename1 `0 < k` >>
  `asm_sym_rel prog (asm_data_env prog vs0.vs_code)
      (entry_asm_state vs0 es0) (sym_init (entry_asm_state vs0 es0))` by
    (irule asm_sym_rel_init >>
     simp[NoAsms, entry_asm_state_def, asm_data_env_ok_asm_data_env]) >>
  `sym_init (entry_asm_state vs0 es0 with
      as_code := assemble prog' ++ vs0.vs_data_section) =
    sym_init (entry_asm_state vs0 es0)` by
    simp[sym_init_def] >>
  `asm_sym_rel prog' (asm_data_env prog vs0.vs_code)
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section)
      (sym_init (entry_asm_state vs0 es0))` by
    (qpat_x_assum `sym_init (_ with as_code := _) = _`
       (fn th => rewrite_tac[GSYM th]) >>
     irule asm_sym_rel_init >>
     simp[entry_asm_state_def, asm_data_env_ok_asm_data_env]) >>
  qexists_tac `k * (B + 1)` >> rpt gen_tac >> strip_tac >>
  drule_all asm_sym_steps_lockstep >> strip_tac >> gvs[] >>
  `(entry_asm_state vs0 es0).as_pc = 0` by simp[entry_asm_state_def] >>
  qpat_x_assum `!env s n a. _` drule_all >> strip_tac >>
  conj_tac
  >- (drule_all asm_sym_steps_lockstep >> strip_tac >>
      qpat_x_assum `!n b. asm_steps _ _ prog' _ _ = _ ==> _` drule >>
      strip_tac >> irule LESS_EQ_TRANS >>
      qexists_tac `k * (m + 1)` >> simp[]) >>
  strip_tac >>
  `ss.sym_base.as_pc = ast.as_pc` by metis_tac[asm_sym_rel_pc] >>
  gvs[] >>
  qpat_x_assum `sym_steps prog' _ m _ = SymOK b` kall_tac >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qpat_x_assum `!n b. asm_steps _ _ prog' _ _ = _ ==> _` drule >>
  strip_tac >>
  gvs[asm_sym_rel_def]
QED
