(*
 * S7 for the final assembly optimizer: the EVM frame that runs the
 * optimized bytecode ends as the Venom run does, or starves.
 *
 * The chain: the Venom run is simulated by the unoptimized assembly run
 * from the entry assembly state (codegen_entry_asm_sim_state);
 * that run is label-disciplined (codegen_label_disciplined), so it is a
 * symbolic run (asm_sym_forward); the optimizer refines it
 * (asm_opt_finalizer_meets_contract); the optimized symbolic run is a
 * concrete one (asm_sym_backward); and the frame runs the optimized
 * assembly (asm_frame_run).
 *
 * TOP-LEVEL:
 *   codegen_correct_asm_opt - codegen_correct for the optimized assembly
 *)

Theory codegenAsmOpt
Ancestors
  codegenCorrectness codegenAsmRunCall codegenLabelDisciplined
  asmOptFinalizerCorrect finalizerContract asmSymBridge asmDataEnv
  asmFrameRun asmFrameRel codegenEntrySim codegenEntryRel codegenAsmProgOk
  asmToBytecodeProps asmToBytecodeProofs codegenAsmStaticWf asmSymSem
  asmOptimizer asmWf asmSem venomExecSemantics vfmDecreasesGas symbolResolve
  contextCodegenRel codegenRel

(* ===== Static facts ===== *)

Theorem asm_static_wf_frame_prog_ok:
  asm_static_wf p ==> asm_frame_prog_ok p
Proof
  rw[asm_static_wf_def, asm_frame_prog_ok_def] >> CCONTR_TAC >> gvs[] >>
  `j < LENGTH p` by decide_tac >>
  qpat_x_assum `!i. i < LENGTH p /\ is_data_inst _ ==> _`
    (qspec_then `j` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `EL k p = AsmDataHeader l` >>
  qpat_x_assum `asm_data_at_end p` mp_tac >>
  simp[asm_data_at_end_def] >>
  qexists_tac `k` >> fs[] >> qexists_tac `i` >> fs[]
QED

Theorem clo_FDOM_header[local]:
  !prog off0 (labels0:string|->num).
    l IN FDOM labels0 \/ MEM (AsmDataHeader l) prog ==>
    l IN FDOM (SND (FOLDL (\(pc:num,labels:string|->num) inst.
                     (pc + asm_inst_size inst,
                      case inst of
                        AsmLabel lbl => labels |+ (lbl, pc)
                      | AsmDataHeader lbl' => labels |+ (lbl', pc)
                      | _ => labels))
              (off0, labels0) prog))
Proof
  Induct >- simp[] >> strip_tac >> Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> gvs[]
QED

Theorem asm_data_env_header_fdom:
  MEM (AsmDataHeader l) p ==> l IN FDOM (asm_data_env p code)
Proof
  strip_tac >>
  simp[asm_data_env_def, finite_mapTheory.FDOM_DRESTRICT] >>
  simp[compute_label_offsets_def, clo_step_eq] >>
  irule clo_FDOM_header >> simp[]
QED

(* ===== Terminal observations ===== *)

Theorem sym_obs_sym_init_fields[local]:
  sym_obs (sym_init a) = sym_obs (sym_init b) ==>
  a.as_accounts = b.as_accounts /\ a.as_transient = b.as_transient /\
  a.as_returndata = b.as_returndata /\ a.as_logs = b.as_logs /\
  a.as_requests = b.as_requests /\
  a.as_pending_deletions = b.as_pending_deletions
Proof
  strip_tac >> fs[sym_obs_def, sym_init_def, asm_state_component_equality]
QED

(* ===== The optimized run ===== *)

(* A terminal unoptimized run from s is matched by an optimized run from
   s with the optimized code. *)
Theorem asm_opt_transfer[local]:
  asm_refines prog prog' /\
  label_disciplined (asm_data_env prog (assemble prog ++ x)) prog s /\
  s.as_pc = 0 /\ s.as_code = assemble prog ++ x /\
  sym_terminal (asm_result_sym
    (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n s))
  ==>
  ?n'. sym_result_rel
         (asm_result_sym
            (asm_steps (SND (compute_label_offsets prog))
               (build_offset_to_pc prog) prog n s))
         (asm_result_sym
            (asm_steps (SND (compute_label_offsets prog'))
               (build_offset_to_pc prog') prog' n'
               (s with as_code := assemble prog' ++ x)))
Proof
  strip_tac >>
  qabbrev_tac `env = asm_data_env prog (assemble prog ++ x)` >>
  `asm_data_env_ok prog env s.as_code` by
    simp[Abbr`env`, asm_data_env_ok_asm_data_env] >>
  drule_all asm_sym_forward >> strip_tac >>
  `asm_static_wf prog` by fs[label_disciplined_def] >>
  `asm_static_wf prog' /\
   FILTER is_data_inst prog' = FILTER is_data_inst prog /\
   !env s fuel.
     sym_terminal (sym_run prog env fuel (sym_init s)) ==>
     ?fuel'. sym_result_rel (sym_run prog env fuel (sym_init s))
                            (sym_run prog' env fuel' (sym_init s))` by
    (qpat_x_assum `asm_refines _ _` mp_tac >> simp[asm_refines_def]) >>
  `sym_terminal (sym_run prog env fuel (sym_init s))` by
    metis_tac[sym_result_rel_terminal] >>
  `?fuel'. sym_result_rel (sym_run prog env fuel (sym_init s))
                          (sym_run prog' env fuel' (sym_init s))` by
    metis_tac[] >>
  `sym_init (s with as_code := assemble prog' ++ x) = sym_init s` by
    simp[sym_init_def] >>
  `env = asm_data_env prog' (assemble prog' ++ x)` by
    (simp[Abbr`env`] >> irule asm_data_env_agree >> simp[]) >>
  `asm_data_env_ok prog' env (assemble prog' ++ x)` by
    metis_tac[asm_data_env_ok_asm_data_env] >>
  `sym_terminal (sym_run prog' env fuel' (sym_init s))` by
    metis_tac[sym_result_rel_terminal] >>
  qspecl_then [`prog'`, `env`, `s with as_code := assemble prog' ++ x`,
               `fuel'`] mp_tac
    (Q.GENL [`p`, `env`, `s`, `fuel`] asm_sym_backward) >>
  impl_tac
  >- (qpat_x_assum `Abbrev _` kall_tac >> qpat_x_assum `env = _` kall_tac >>
      fs[]) >>
  strip_tac >>
  qexists_tac `n'` >> metis_tac[sym_result_rel_trans]
QED

(* TOP-LEVEL: codegen_correct for the optimized assembly prog'. The Venom
   state vs holds the unoptimized layout (vs_code and vs_labels for prog)
   and the entry assembly state relates to it; the EVM frame es runs the
   optimized code, and relates to the same entry state with that code. *)
Theorem codegen_correct_asm_opt:
  !fuel rpolicy unit cplan prog prog' Inv vs es.
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
         as_code := assemble prog' ++ vs.vs_data_section) es
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/
             venom_frame_rel es r es' (run_context fuel unit.cu_context vs))
Proof
  rpt strip_tac >>
  drule_all codegen_entry_asm_sim_state >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `asm_refines prog prog'` by
    metis_tac[asm_opt_finalizer_meets_contract, finalizer_correct_def] >>
  qabbrev_tac `x = vs.vs_data_section` >>
  qabbrev_tac `s = entry_asm_state vs es` >>
  qabbrev_tac `s' = s with as_code := assemble prog' ++ x` >>
  `s.as_pc = 0 /\ s.as_code = assemble prog ++ x` by
    simp[Abbr`s`, entry_asm_state_def] >>
  (* label discipline of the unoptimized run, once the Venom run ends *)
  `(?v. run_context fuel unit.cu_context vs = Halt v) \/
   (?a v. run_context fuel unit.cu_context vs = Abort a v) ==>
   label_disciplined (asm_data_env prog (assemble prog ++ x)) prog s` by
    (strip_tac >>
     qspecl_then [`fuel`, `rpolicy`, `unit`, `cplan`, `prog`, `Inv`, `vs`, `s`,
                  `asm_data_env prog (assemble prog ++ x)`] mp_tac
       codegen_label_disciplined >>
     (impl_tac >- (rpt conj_tac >> fs[] >>
                   metis_tac[asm_data_env_header_fdom,
                             asm_data_env_ok_asm_data_env])) >>
     simp[]) >>
  `asm_static_wf prog'` by
    (qpat_x_assum `asm_refines _ _` mp_tac >>
     simp[asm_refines_def] >> strip_tac >>
     `asm_static_wf prog` by
       metis_tac[codegen_context_obligations_def, codegen_asm_static_wf] >>
     fs[]) >>
  `asm_frame_prog_ok prog'` by metis_tac[asm_static_wf_frame_prog_ok] >>
  `asm_frame_rel prog' x es s' es` by simp[Abbr`s'`, Abbr`s`, Abbr`x`] >>
  Cases_on `run_call es` >- fs[run_call_eq_tr] >>
  rename1 `run_call es = SOME res` >> PairCases_on `res` >>
  qexistsl_tac [`res0`, `res1`] >> simp[] >>
  Cases_on `frame_resource_starved es res0 res1` >> simp[] >>
  qspecl_then [`n'`, `prog'`, `x`, `es`, `s'`, `es`, `res0`, `res1`]
    (assume_tac o Q.GEN `n'`) asm_frame_run >>
  `!n r0.
     asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog n s = r0 /\ sym_terminal (asm_result_sym r0) /\
     label_disciplined (asm_data_env prog (assemble prog ++ x)) prog s ==>
     ?n'. sym_result_rel (asm_result_sym r0)
            (asm_result_sym
               (asm_steps (SND (compute_label_offsets prog'))
                  (build_offset_to_pc prog') prog' n' s'))` by
    (rpt strip_tac >> gvs[Abbr`s'`] >> irule asm_opt_transfer >> simp[]) >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  gvs[venom_frame_rel_def, run_context_never_ok]
  >- ((* Halt *)
      rename1 `asm_steps _ _ prog n s = AsmHalt a1` >>
      qpat_x_assum `!n. sym_terminal _ ==> _` (qspec_then `n` mp_tac) >>
      qpat_assum `asm_steps _ _ prog n s = _` (fn th => REWRITE_TAC [th]) >>
      simp[asm_result_sym_def, sym_terminal_def] >> strip_tac >>
      Cases_on `asm_steps (SND (compute_label_offsets prog'))
                  (build_offset_to_pc prog') prog' n' s'` >>
      gvs[asm_result_sym_def, sym_result_rel_def] >>
      drule sym_obs_sym_init_fields >> strip_tac >>
      first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
      gvs[venom_asm_terminal_rel_def])
  >- ((* Revert *)
      rename1 `asm_steps _ _ prog n s = AsmRevert a1` >>
      qpat_x_assum `!n. sym_terminal _ ==> _` (qspec_then `n` mp_tac) >>
      qpat_assum `asm_steps _ _ prog n s = _` (fn th => REWRITE_TAC [th]) >>
      simp[asm_result_sym_def, sym_terminal_def] >> strip_tac >>
      Cases_on `asm_steps (SND (compute_label_offsets prog'))
                  (build_offset_to_pc prog') prog' n' s'` >>
      gvs[asm_result_sym_def, sym_result_rel_def] >>
      drule sym_obs_sym_init_fields >> strip_tac >>
      first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
      gvs[venom_asm_terminal_rel_def])
  >> ((* ExHalt *)
      rename1 `asm_steps _ _ prog n s = AsmFault a1` >>
      qpat_x_assum `!n. sym_terminal _ ==> _` (qspec_then `n` mp_tac) >>
      qpat_assum `asm_steps _ _ prog n s = _` (fn th => REWRITE_TAC [th]) >>
      simp[asm_result_sym_def, sym_terminal_def] >> strip_tac >>
      Cases_on `asm_steps (SND (compute_label_offsets prog'))
                  (build_offset_to_pc prog') prog' n' s'` >>
      gvs[asm_result_sym_def, sym_result_rel_def] >>
      first_x_assum (qspec_then `n'` mp_tac) >> simp[])
QED
