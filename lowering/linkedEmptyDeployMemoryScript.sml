Theory linkedEmptyDeployMemory
Ancestors linkedEmptyDeployTarget linkedUnitMemory unitMemInv lowerDloadDefs
  o1PassContract ctorDeployMemoryFrontier linkedRawUnitShape
  o1SafeUpto contextRawReachable ptrDiscipline passSimulationDefs
  compileUnit vyperCompiler venomExecSemantics venomState venomInst words finite_map list

Theorem linked_empty_deploy_raw_variant:
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,NONE,imp_ctors) /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
  vs.vs_alloca_next = imm_len_mods mods /\
  LENGTH runtime_bc + imm_len_mods mods < dimword (:256) /\ off < dimword (:256) /\
  FLOOKUP vs.vs_labels "runtime_begin" = SOME (n2w off) /\
  DROP off vs.vs_code = runtime_bc /\ code_layout_valid vs /\
  raw_variant fmp vi vs ==>
  raw_unit_memory_ok unit.cu_context vi /\
  ptr_discipline (imm_len_mods mods) unit.cu_context vi /\
  taint_within D unit.cu_context vi /\
  mem_inv dload_offset_ok unit.cu_context vi /\
  mem_inv dload_headroom_ok unit.cu_context vi /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                           s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
    unit.cu_context vi /\
  ?post. run_context 1 unit.cu_context vi = Halt post /\
    post.vs_returndata = runtime_bc ++ REPLICATE (imm_len_mods mods) 0w /\
    post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
    post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
    post.vs_requests = vs.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac lower_vyper_deploy_unit_raw_shape_mods >>
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  `code_layout_valid vi /\ vi.vs_fmp = vi.vs_initial_fmp /\
   vi.vs_alloca_next = imm_len_mods mods` by
    (qpat_assum `vi = _` SUBST1_TAC >>
     qpat_assum `code_layout_valid vs` mp_tac >>
     simp[NoAsms, code_layout_valid_def] >> strip_tac >>
     qpat_assum `vs.vs_alloca_next = imm_len_mods mods` ACCEPT_TAC) >>
  mp_tac (Q.INST [`unit` |-> `unit`, `rp` |-> `rp`,
      `vs` |-> `vi`, `off` |-> `off`]
    (SPEC_ALL linked_empty_deploy_target)) >>
  impl_tac >- (qpat_assum `vi = _` SUBST1_TAC >> simp[]) >>
  disch_then (qx_choosel_then [`vfn`, `vpost`] strip_assume_tac) >>
  mp_tac (Q.INST [`dunit` |-> `unit`, `rpolicy` |-> `rp`, `vs` |-> `vi`, `D` |-> `D`,
     `func` |-> `vfn`] (SPEC_ALL deploy_selected_memory_mods)) >>
  impl_tac >-
    (rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC,
            qpat_assum `!D fuel. ptr_safe_blocks D _ fuel _ vfn _ _ _ _`
              (qspec_then `D` ACCEPT_TAC),
            qpat_assum `vi.vs_fmp = vi.vs_initial_fmp`
              (fn th => simp[NoAsms, th])]) >>
  disch_then strip_assume_tac >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                  s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
     unit.cu_context vi` by
    (qspecl_then [`unit.cu_context`,`"__deploy"`,`vfn`,`"__deploy"`,`vi`]
       mp_tac lowered_unit_dload_in_section >>
     impl_tac >- asm_rewrite_tac[] >>
     simp[mem_inv_raw_reachable] >> strip_tac >> rpt gen_tac >> disch_tac >>
     conj_tac
     >- first_x_assum (drule_then ACCEPT_TAC) >>
     drule_then ACCEPT_TAC o1SafeUptoTheory.raw_reachable_code_data) >>
  `vi.vs_accounts = vs.vs_accounts /\ vi.vs_transient = vs.vs_transient /\
   vi.vs_logs = vs.vs_logs /\ vi.vs_pending_deletions = vs.vs_pending_deletions /\
   vi.vs_requests = vs.vs_requests` by
    (qpat_assum `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                               vs_gas_readings := vi.vs_gas_readings|>` mp_tac >>
     simp[NoAsms, venom_state_component_equality]) >>
  asm_rewrite_tac[] >> qexists_tac `vpost` >>
  asm_rewrite_tac[]
QED
