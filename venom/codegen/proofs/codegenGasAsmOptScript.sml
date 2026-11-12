(*
 * S7g for the final assembly optimizer: codegen_gas_surplus,
 * codegen_no_returndatacopy and codegen_gas_sufficient with prog' =
 * asm_opt_finalizer's output in place of prog, under
 * codegen_correct_asm_opt's hypotheses.  The unoptimized program's bounded
 * run (codegen_entry_asm_bounded_run) carries over to prog' at c times the
 * steps (asm_refines_run_bounded, from the optimizer's step-bounded
 * refinement), and the program-generic frame lemmas of asmFrameSurplus
 * turn that into the bounds on the optimized frame.
 *
 * TOP-LEVEL:
 *   codegen_gas_surplus_asm_opt - S7g's surplus bound for the optimized code
 *   codegen_no_returndatacopy_asm_opt - no RETURNDATACOPY in the optimized
 *     frame when prog has none
 *   codegen_gas_sufficient_asm_opt - S7g for the optimized code
 *)

Theory codegenGasAsmOpt
Ancestors
  codegenAsmOpt codegenEntryBounded asmFrameSurplus asmSymWithin asmOptNoRdc
  asmOptFinalizerCorrect finalizerContract asmDataEnv contextCodegenRel
  venomRunBounded codegenAsmStaticWf codegenLabelDisciplined codegenEntryRel
  codegenCorrectness asmFrameRel asmRunBounded asmSymSem passSimulationDefs
  vfmDecreasesGas frameGas frameStep

(* The optimized program's run from the entry assembly state is bounded,
   uniformly in the entry state. *)
Theorem codegen_opt_run_bounded[local]:
  !rpolicy unit cplan prog prog' fuel M.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit
    ==>
    ?N H. !Inv vs as.
      codegen_context_obligations Inv unit.cu_context cplan /\
      codegen_reachability_package Inv unit.cu_context vs /\
      label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
      sym_unit_static_ok unit /\
      vs.vs_code = assemble prog ++ vs.vs_data_section /\
      as.as_code = vs.vs_code /\
      codegen_asm_entry_rel cplan prog vs as /\
      venom_run_bounded fuel M unit.cu_context vs
      ==>
      asm_frame_prog_ok prog' /\
      asm_run_bounded (SND (compute_label_offsets prog'))
        (build_offset_to_pc prog') prog' H N
        (as with as_code := assemble prog' ++ vs.vs_data_section)
Proof
  rpt gen_tac >> strip_tac >>
  `asm_refines prog prog'` by
    metis_tac[asm_opt_finalizer_meets_contract, finalizer_correct_def] >>
  (* without asm_static_wf prog the hypotheses contradict each other *)
  reverse (Cases_on `asm_static_wf prog`)
  >- (qexistsl_tac [`0`, `0`] >> rpt strip_tac >>
      `codegen_ready unit.cu_context` by
        fs[codegen_context_obligations_def] >>
      metis_tac[codegen_asm_static_wf]) >>
  drule_all asm_refines_run_bounded >>
  disch_then (qx_choose_then `c` assume_tac) >>
  qspecl_then [`rpolicy`, `unit`, `cplan`, `prog`, `fuel`, `M`] mp_tac
    codegen_entry_asm_bounded_run >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`N`, `H`] assume_tac) >>
  qexistsl_tac [`c * N`, `H`] >> rpt gen_tac >> strip_tac >>
  `asm_static_wf prog'` by
    (qpat_x_assum `asm_refines _ _` mp_tac >> simp[asm_refines_def]) >>
  conj_tac >- metis_tac[asm_static_wf_frame_prog_ok] >>
  qabbrev_tac `x = vs.vs_data_section` >>
  `as.as_pc = 0` by fs[codegen_asm_entry_rel_def] >>
  (* the unoptimized run is bounded and uses its labels as labels *)
  `(?v. run_context fuel unit.cu_context vs = Halt v) \/
   (?a v. run_context fuel unit.cu_context vs = Abort a v)` by
    (qspecl_then [`fuel`, `rpolicy`, `unit`, `cplan`, `prog`, `Inv`, `vs`,
                  `as`] mp_tac codegen_entry_asm_sim_state >>
     impl_tac >- simp[] >> strip_tac >>
     fs[venom_run_bounded_def, terminates_def] >>
     Cases_on `run_context fuel unit.cu_context vs` >>
     fs[run_context_never_ok]) >>
  `label_disciplined (asm_data_env prog (assemble prog ++ x)) prog as` by
    (qspecl_then [`fuel`, `rpolicy`, `unit`, `cplan`, `prog`, `Inv`, `vs`,
                  `as`, `asm_data_env prog (assemble prog ++ x)`] mp_tac
       codegen_label_disciplined >>
     (impl_tac >- (rpt conj_tac >> fs[] >>
                   metis_tac[asm_data_env_header_fdom,
                             asm_data_env_ok_asm_data_env])) >>
     simp[]) >>
  `asm_run_bounded (SND (compute_label_offsets prog))
     (build_offset_to_pc prog) prog H N as` by
    (qpat_x_assum `!Inv vs as. _` irule >> simp[] >> metis_tac[]) >>
  (* so is the optimized one, c times as long *)
  qpat_x_assum `!H k s x. _` (qspecl_then [`H`, `N`, `as`, `x`] mp_tac) >>
  simp[]
QED

(* TOP-LEVEL: codegen_gas_surplus for the optimized program. *)
Theorem codegen_gas_surplus_asm_opt:
  !rpolicy unit cplan prog prog' fuel M D.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit
    ==>
    ?g. !g' Inv vs es s op r s'.
      g <= g' /\ wf_state (add_frame_gas g' es) /\
      g' <= frame_gas_left (add_frame_gas g' es) /\
      codegen_context_obligations Inv unit.cu_context cplan /\
      codegen_reachability_package Inv unit.cu_context vs /\
      label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
      sym_unit_static_ok unit /\
      vs.vs_code = assemble prog ++ vs.vs_data_section /\
      codegen_asm_entry_rel cplan prog vs
        (entry_asm_state vs (add_frame_gas g' es)) /\
      asm_frame_rel prog' vs.vs_data_section (add_frame_gas g' es)
        (entry_asm_state vs (add_frame_gas g' es) with
           as_code := assemble prog' ++ vs.vs_data_section)
        (add_frame_gas g' es) /\
      venom_run_bounded fuel M unit.cu_context vs /\
      frame_inst_at (add_frame_gas g' es) s op /\
      (!t. frame_inst_at (add_frame_gas g' es) t ReturnDataCopy ==>
           ~RTC (\a b. LENGTH a.contexts >= LENGTH s.contexts /\
                       step a = (INL (), b)) t s) /\
      step_inst op s = (r, s') /\ LENGTH s'.contexts = LENGTH s.contexts
      ==>
      r <> INR (SOME OutOfGas) /\ D <= frame_gas_left s'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_opt_run_bounded >>
  disch_then (qspecl_then [`fuel`, `M`] (qx_choosel_then [`N`, `H`] assume_tac)) >>
  qspecl_then [`H`, `N`, `D`] (qx_choose_then `g` assume_tac)
    asm_frame_gas_surplus >>
  qexists_tac `g` >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `s0 = entry_asm_state vs (add_frame_gas g' es)` >>
  `s0.as_code = vs.vs_code` by simp[Abbr`s0`, entry_asm_state_def] >>
  `asm_frame_prog_ok prog' /\
   asm_run_bounded (SND (compute_label_offsets prog'))
     (build_offset_to_pc prog') prog' H N
     (s0 with as_code := assemble prog' ++ vs.vs_data_section)` by
    (qpat_x_assum `!Inv vs as. codegen_context_obligations _ _ _ /\ _ ==> _`
       (qspecl_then [`Inv`, `vs`, `s0`] mp_tac) >>
     impl_tac >- simp[] >> simp[]) >>
  qpat_x_assum `!prog data es0 a e s op r s'. asm_frame_prog_ok _ /\ _ ==> _`
    (qspecl_then [`prog'`, `vs.vs_data_section`, `add_frame_gas g' es`,
                  `s0 with as_code := assemble prog' ++ vs.vs_data_section`,
                  `add_frame_gas g' es`, `s`, `op`, `r`, `s'`] mp_tac) >>
  impl_tac >- simp[] >> simp[]
QED

(* TOP-LEVEL: codegen_no_returndatacopy for the optimized program. *)
Theorem codegen_no_returndatacopy_asm_opt:
  !rpolicy unit cplan prog prog' fuel M Inv vs es t.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cplan /\
    codegen_reachability_package Inv unit.cu_context vs /\
    label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
    sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cplan prog vs (entry_asm_state vs es) /\
    asm_frame_rel prog' vs.vs_data_section es
      (entry_asm_state vs es with
         as_code := assemble prog' ++ vs.vs_data_section) es /\
    venom_run_bounded fuel M unit.cu_context vs /\
    ~MEM (AsmOp "RETURNDATACOPY") prog
    ==>
    ~frame_inst_at es t ReturnDataCopy
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_opt_run_bounded >>
  disch_then (qspecl_then [`fuel`, `M`] (qx_choosel_then [`N`, `H`] assume_tac)) >>
  `(entry_asm_state vs es).as_code = vs.vs_code` by
    simp[entry_asm_state_def] >>
  qpat_x_assum `!Inv vs as. _`
    (qspecl_then [`Inv`, `vs`, `entry_asm_state vs es`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`N`, `prog'`, `vs.vs_data_section`, `es`,
               `entry_asm_state vs es with
                  as_code := assemble prog' ++ vs.vs_data_section`,
               `es`, `H`, `t`] mp_tac asm_frame_no_returndatacopy >>
  impl_tac >- (simp[] >> metis_tac[asm_opt_finalizer_no_returndatacopy]) >>
  simp[]
QED

(* TOP-LEVEL: codegen_gas_sufficient for the optimized program (S7g-opt):
   codegen_gas_surplus_asm_opt with D = 0. *)
Theorem codegen_gas_sufficient_asm_opt:
  !rpolicy unit cplan prog prog' fuel M.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    unit_shape_ok unit
    ==>
    ?g. !g' Inv vs es.
      g <= g' /\ wf_state es /\
      codegen_context_obligations Inv unit.cu_context cplan /\
      codegen_reachability_package Inv unit.cu_context vs /\
      label_flow_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
      sym_unit_static_ok unit /\
      vs.vs_code = assemble prog ++ vs.vs_data_section /\
      codegen_asm_entry_rel cplan prog vs
        (entry_asm_state vs (add_frame_gas g' es)) /\
      asm_frame_rel prog' vs.vs_data_section (add_frame_gas g' es)
        (entry_asm_state vs (add_frame_gas g' es) with
           as_code := assemble prog' ++ vs.vs_data_section)
        (add_frame_gas g' es) /\
      venom_run_bounded fuel M unit.cu_context vs /\
      mem_inv (\ctx fn inst s. inst_create_size_ok inst s) unit.cu_context vs
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule_all codegen_gas_surplus_asm_opt >>
  disch_then (qspecl_then [`fuel`, `M`, `0`] strip_assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  Cases_on `run_call (add_frame_gas g' es)` >- fs[run_call_eq_tr] >>
  rename1 `run_call _ = SOME res` >> PairCases_on `res` >>
  qexistsl_tac [`res0`, `res1`] >> simp[] >>
  rpt strip_tac >> gvs[frame_inst_raises_def] >>
  CCONTR_TAC >>
  `wf_state (add_frame_gas g' es) /\
   g' <= frame_gas_left (add_frame_gas g' es)` by
    metis_tac[add_frame_gas_wf_state, wf_state_frame_gas_left] >>
  `LENGTH s.contexts = LENGTH (add_frame_gas g' es).contexts` by
    fs[frame_inst_at_def] >>
  first_x_assum (qspecl_then [`g'`, `Inv`, `vs`, `es`, `s`, `op`, `s'`]
                   mp_tac) >>
  metis_tac[]
QED
