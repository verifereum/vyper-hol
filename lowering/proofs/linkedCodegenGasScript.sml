(* A frame gas surplus for each accepted assembly finalizer. *)
Theory linkedCodegenGas
Ancestors
  asmOptimizer codegenGasAsmOpt codegenEntryBounded codegenAsmOpt
  codegenAsmStaticWf asmFrameSurplus asmFrameRel codegenEntryRel codegenEntrySim
  codegenLabelDisciplined fnPlanPlaceRevertPostamble
  asmSymSem asmRunBounded contextCodegenRel arithmetic

Theorem codegen_gas_surplus_finalized_own:
  !fin rpolicy unit cplan prog prog' fuel M D.
    generate_context_plan unit.cu_context = SOME cplan /\
    codegen_assembly rpolicy unit = SOME prog /\
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    unit_shape_ok unit
    ==>
    ?g. !g' Inv vs es s op r s'.
      g <= g' /\ wf_state (add_frame_gas g' es) /\
      g' <= frame_gas_left (add_frame_gas g' es) /\
      codegen_context_obligations Inv unit.cu_context cplan /\
      codegen_reachability_package Inv unit.cu_context vs /\
      label_flow_own_ok unit.cu_context /\ code_end_offset_ok Inv unit.cu_context /\
      sym_unit_static_ok unit /\
      vs.vs_code = assemble prog' ++ vs.vs_data_section /\
      codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog vs
        (entry_asm_state vs (add_frame_gas g' es)) /\
      asm_frame_rel prog' vs.vs_data_section (add_frame_gas g' es)
        (entry_asm_state vs (add_frame_gas g' es))
        (add_frame_gas g' es) /\
      venom_run_bounded fuel M unit.cu_context vs /\
      mem_inv (\ctx fn inst s. inst_create_size_ok inst s) unit.cu_context vs /\
      frame_inst_at (add_frame_gas g' es) s op /\
      (!t. frame_inst_at (add_frame_gas g' es) t ReturnDataCopy ==>
           ~RTC (\a b. LENGTH a.contexts >= LENGTH s.contexts /\
                       step a = (INL (), b)) t s) /\
      step_inst op s = (r, s') /\ LENGTH s'.contexts = LENGTH s.contexts
      ==>
      r <> INR (SOME OutOfGas) /\ D <= frame_gas_left s'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `fin = K SOME`
  >- (gvs[] >>
      qspecl_then [`rpolicy`, `unit`, `cplan`, `prog`, `fuel`, `M`] mp_tac
        codegen_entry_asm_bounded_run >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choosel_then [`N`, `H`] assume_tac) >>
      qspecl_then [`H`, `N`, `D`] (qx_choose_then `g` assume_tac)
        asm_frame_gas_surplus >>
      qexists_tac `g` >> rpt gen_tac >> strip_tac >>
      `asm_frame_prog_ok prog` by
        (irule asm_static_wf_frame_prog_ok >>
         metis_tac[codegen_context_obligations_def, codegen_asm_static_wf]) >>
      qabbrev_tac `s0 = entry_asm_state vs (add_frame_gas g' es)` >>
      `asm_run_bounded (SND (compute_label_offsets prog))
          (build_offset_to_pc prog) prog H N s0` by
        (qpat_x_assum `!Inv vs as. codegen_context_obligations _ _ _ /\ _ ==> _`
          (qspecl_then [`Inv`, `vs`, `s0`] mp_tac) >>
         `codegen_asm_entry_rel cplan prog vs s0` by
           fs[lo_reloc_refl, codegen_asm_entry_rel_reloc_def,
              GSYM codegen_asm_entry_rel_def] >>
         asm_rewrite_tac[]) >>
      qpat_x_assum `!prog data es0 a e s op r s'. asm_frame_prog_ok _ /\ _ ==> _`
        (qspecl_then [`prog`, `vs.vs_data_section`, `add_frame_gas g' es`,
                      `s0`, `add_frame_gas g' es`, `s`, `op`, `r`, `s'`] mp_tac) >>
      `g <= frame_gas_left (add_frame_gas g' es)` by
        (irule LESS_EQ_TRANS >> qexists_tac `g'` >> asm_rewrite_tac[]) >>
      asm_rewrite_tac[]) >>
  `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
  match_mp_tac (Q.SPECL [`rpolicy`, `unit`, `cplan`, `prog`, `prog'`, `fuel`, `M`, `D`]
    codegen_gas_surplus_asm_opt_own) >>
  asm_rewrite_tac[]
QED
