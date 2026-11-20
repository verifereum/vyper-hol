(* GAS readiness is obtained before any source or joint successor is taken. *)
Theory gasFocusGasPreEdge
Ancestors
  fnFrameSymbolicPrefix fnFramePrefix fnFramePrefixEntry
  asmFinalizerPrefix blockSimHelpers codegenSymRel asmSplice
  asmSem venomInst asmSpliceOwn fnPlanPlaceRevertPostamble

Theorem focus_normal_frame_gas_available:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_ready unit.cu_context /\ focus_s7_symbolic_context unit prog /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final
  ==> ?max_cost. !n ast ss stk PG G tn fn inst s oms om hs h.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
      rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
    active_inst fn inst s /\ inst.inst_opcode = GAS
    ==> s.vs_gas_readings <> [] /\
      ?k ast1 ss1.
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog k ast = AsmOK ast1 /\
        sym_steps prog (asm_data_env prog vs0.vs_code) k ss = SymOK ss1 /\
        normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
          rpolicy unit cpl prog vs0 es0
          (JointConfig stk PG G tn fn inst s oms om hs h) ast1 ss1 /\
        ast1.as_pc < LENGTH prog /\ EL ast1.as_pc prog = AsmOp "GAS" /\
        ast1.as_gas_readings = s.vs_gas_readings /\ n + k <= max_cost
Proof
  strip_tac >>
  `label_flow_ok unit.cu_context /\ sym_unit_static_ok unit` by
    fs[focus_s7_symbolic_context_def] >>
  drule_all focus_finalizer_prefix_bridge >> strip_tac >>
  qexists `max_cost` >> rpt gen_tac >> strip_tac >>
  `?k ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog k ast = AsmOK ast1 /\
    sym_steps prog (asm_data_env prog vs0.vs_code) k ss = SymOK ss1 /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
      rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast1 ss1 /\
    ?ra rest mem0. active_frame_plan rpolicy unit cpl prog fn s ast1 ra rest mem0`
    by suspend "normalize" >>
  drule_all active_frame_gas_ready >> strip_tac >>
  `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n + k) (entry_asm_state vs0 es0) = AsmOK ast1` by
    (irule asm_steps_compose_ok >> goal_assum (drule_at Any) >> simp[]) >>
  `sym_steps prog (asm_data_env prog vs0.vs_code) (n + k)
     (sym_init (entry_asm_state vs0 es0)) = SymOK ss1` by
    (irule sym_steps_compose >> goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum (qspecl_then [`n + k`, `ast1`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`k`, `ast1`, `ss1`] >> gvs[]
QED

Resume focus_normal_frame_gas_available[normalize]:
  qhdtm_assum `normal_frame_symbolic_plan`
    (strip_assume_tac o REWRITE_RULE [normal_frame_symbolic_plan_def])
  >- (qexistsl [`0`, `ast`, `ss`] >>
      simp[asmSemTheory.asm_steps_def, asmSpliceTheory.sym_steps_def] >>
      fs[active_frame_symbolic_plan_def, active_frame_plan_def] >> metis_tac[]) >>
  `entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0` by
    fs[entry_frame_symbolic_plan_def] >>
  `s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    fs[entry_frame_plan_def] >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
       decide_tac >>
     drule_all entry_frame_active_param >> simp[is_param_opcode_def]) >>
  drule_all entry_frame_symbolic_plan_ready >> strip_tac >>
  qexistsl [`n'`, `ast1`, `ss1`] >> simp[] >> conj_tac
  >- (simp[normal_frame_symbolic_plan_def] >>
      qexistsl [`saved`, `ra`, `rest`, `mem0`, `sentry`, `ret`, `srest`, `labs0`] >>
      gvs[]) >>
  fs[active_frame_symbolic_plan_def, active_frame_plan_def] >> metis_tac[]
QED

Finalise focus_normal_frame_gas_available

Theorem focus_normal_frame_gas_available_reloc:
  code_labels_agree prog asm_lo /\
  focus_s7_symbolic_context_own allow_own unit prog /\
  (!j a. asm_steps asm_lo (build_offset_to_pc prog)
     prog j (entry_asm_state vs0 es0) = AsmOK a /\
     (?sr. sym_steps_mode allow_own prog env own j
       (sym_init (entry_asm_state vs0 es0)) = SymOK sr) ==>
     j <= max_cost /\
     (a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "GAS" ==>
      a.as_gas_readings <> [])) /\
  asm_steps asm_lo (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es0) = AsmOK ast /\
  sym_steps_mode allow_own prog env own n
    (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
  normal_frame_symbolic_plan_own allow_own asm_lo env own rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
  active_inst fn inst s /\ inst.inst_opcode = GAS ==>
  s.vs_gas_readings <> [] /\
  ?k ast1 ss1.
    asm_steps asm_lo (build_offset_to_pc prog) prog k ast = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own k ss = SymOK ss1 /\
    normal_frame_symbolic_plan_own allow_own asm_lo env own rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast1 ss1 /\
    ast1.as_pc < LENGTH prog /\ EL ast1.as_pc prog = AsmOp "GAS" /\
    ast1.as_gas_readings = s.vs_gas_readings /\ n + k <= max_cost
Proof
  strip_tac >>
  `?k ast1 ss1.
    asm_steps asm_lo (build_offset_to_pc prog) prog k ast = AsmOK ast1 /\
    sym_steps_mode allow_own prog env own k ss = SymOK ss1 /\
    normal_frame_symbolic_plan_own allow_own asm_lo env own rpolicy unit cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast1 ss1 /\
    ?ra rest mem0. active_frame_plan_reloc asm_lo rpolicy unit cpl prog fn s ast1 ra rest mem0`
    by suspend "normalize" >>
  drule_all active_frame_gas_ready_reloc >> strip_tac >>
  `asm_steps asm_lo (build_offset_to_pc prog)
     prog (n + k) (entry_asm_state vs0 es0) = AsmOK ast1` by
    (irule asm_steps_compose_ok >> goal_assum (drule_at Any) >> simp[]) >>
  `sym_steps_mode allow_own prog env own (n + k)
     (sym_init (entry_asm_state vs0 es0)) = SymOK ss1` by
    (irule sym_steps_mode_compose >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `!j a. _ ==> j <= max_cost /\ _`
    (qspecl_then [`n+k`,`ast1`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                qexists_tac `ss1` >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`k`,`ast1`,`ss1`] >> simp[] >> decide_tac
QED

Resume focus_normal_frame_gas_available_reloc[normalize]:
  qhdtm_assum `normal_frame_symbolic_plan_own`
    (strip_assume_tac o REWRITE_RULE [normal_frame_symbolic_plan_own_def])
  >- (qexistsl_tac [`0`,`ast`,`ss`] >>
      Cases_on `allow_own` >>
      simp[asmSemTheory.asm_steps_def, sym_steps_mode_def,
           asmSpliceTheory.sym_steps_def, sym_steps_own_def] >>
      fs[active_frame_symbolic_plan_own_def, active_frame_plan_reloc_def] >>
      metis_tac[]) >>
  `entry_frame_plan_reloc asm_lo rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0` by
    fs[entry_frame_symbolic_plan_own_def] >>
  `s.vs_inst_idx <= LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    fs[entry_frame_plan_reloc_def] >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
       decide_tac >>
     drule_all entry_frame_active_param_reloc >> simp[is_param_opcode_def]) >>
  drule_all entry_frame_symbolic_plan_ready_own >> strip_tac >>
  qexistsl_tac [`n'`,`ast1`,`ss1`] >> simp[] >> conj_tac
  >- (simp[normal_frame_symbolic_plan_own_def] >>
      qexistsl_tac [`saved`,`ra`,`rest`,`mem0`,`sentry`,`ret`,`srest`,`labs0`] >>
      gvs[]) >>
  fs[active_frame_symbolic_plan_own_def, active_frame_plan_reloc_def] >>
  metis_tac[]
QED

Finalise focus_normal_frame_gas_available_reloc
