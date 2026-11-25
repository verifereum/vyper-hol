(* The linked checker and entry layout supply the shared body invariant. *)
Theory linkedCheckedContractInv
Ancestors
  linkedCheckedBodyCalls linkedEntryStructAcyclic linkedStructFields
  entryModuleLocations e2eModsDefs bodyInvSplit bodyCallSupport supportedProgram
  supportedDecls vyperReadOnlySyntax vyperTypeCallGraphSoundness
  vyperTypeContractContext vyperTypeContract vyperContext vyperInterpreter
  compileUnit compileEnv alist list pair option

Theorem linked_checked_contract_inv:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  IS_SOME (ALOOKUP mods NONE) /\
  cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot cx.layouts cx.txn.target /\
  layouts_agree_mods mods exps am tx /\
  (if cx.in_deploy then
     lower_vyper_deploy_unit_mods mods exps rp rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps rp = SOME unit) /\
  (cx.in_deploy ==>
     IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps)))))) /\
  (!src tops. ALOOKUP mods src = SOME tops ==>
     supported_module_headers tops /\
     (src = NONE ==> supported_declaration_headers tops)) /\
  (!src tops vis mut nr rr name args dflts ret ss.
     ALOOKUP mods src = SOME tops /\
     MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
     (src = NONE \/ context_function_live cx (src,name)) ==>
     supported_declaration_body tops
       (FunctionDecl vis mut nr rr name args dflts ret ss) /\
     (cx.in_deploy ==> supported_deploy_declaration tops
       (FunctionDecl vis mut nr rr name args dflts ret ss))) /\
  (vis = Deploy <=> cx.in_deploy) ==>
  contract_inv mods exps unit.cu_context
    (build_compile_env_unit mods src vis mut name args ret ss T
       with ce_target := rp.rpol_target) cx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac check_contract_linked_body_calls_resolved >>
  `contract_namespaces_ok cx.in_deploy mods` by
    (qpat_assum `check_contract cx.in_deploy _ _ _ = _`
       (ACCEPT_TAC o MATCH_MP check_contract_namespaces_ok)) >>
  `ALL_DISTINCT (MAP FST mods) /\
   ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods)` by
    fs[contract_namespaces_ok_def] >>
  `acyclic_struct_metadata (make_struct_fields_map_mods mods)` by
    (irule (INST_TYPE [alpha |-> ``:160 word``] checked_struct_metadata_acyclic_mods) >>
     qexistsl_tac [`cx.txn.target`,`art`,`cx.in_deploy`,`cx.layouts`,`mods`] >>
     simp[] >> drule_then ACCEPT_TAC make_struct_fields_map_mods_consistent) >>
  qabbrev_tac `ce = build_compile_env_unit mods src vis mut name args ret ss T
    with ce_target := rp.rpol_target` >>
  `immutable_section_layout_mods mods ce` by
    (irule unit_module_locations_immutable_layout >>
     simp[Abbr `ce`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
     qexistsl_tac [`am`,`exps`,`tx`] >> simp[]) >>
  `!main top. ALOOKUP mods NONE = SOME main /\ MEM top main ==>
     supported_declaration_body main top /\
     (cx.in_deploy ==> supported_deploy_declaration main top)` by
    (rpt gen_tac >> strip_tac >> Cases_on `top` >>
     simp[supported_declaration_body_def,supported_deploy_declaration_def] >>
     qpat_assum `!src tops vis mut nr rr name args dflts ret ss. _`
       (qspecl_then [`NONE`,`main`] mp_tac) >>
     simp[supported_declaration_body_def, supported_deploy_declaration_def] >>
     metis_tac[]) >>
  `!s tops v m nrr rr nm ar df rt code.
     ALOOKUP mods s = SOME tops /\
     MEM (FunctionDecl v m nrr rr nm ar df rt code) tops /\
     (s = NONE \/ MEM (s,nm) (linked_live_functions mods exps)) ==>
     function_mutability_ok mods v m nrr df code /\
     (nrr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
     (cx.in_deploy /\ v = Deploy ==> EVERY (supported_value_type tops o SND) ar)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all_then assume_tac checked_function_mutability >> simp[] >>
     conj_tac
     >- (Cases_on `nrr` >> simp[] >>
         drule_then assume_tac ALOOKUP_MEM >>
         `ALOOKUP (case ALOOKUP cx.layouts cx.txn.target of
             NONE => [] | SOME (_,tl) => tl)
             (NONE,"$.nonreentrant_key") = SOME global_nonreentrant_slot` by
           (irule check_contract_linked_lock_slot >>
            metis_tac[]) >>
         Cases_on `ALOOKUP cx.layouts cx.txn.target` >>
         gvs[lookup_nonreentrant_slot_def] >>
         rename1 `ALOOKUP _ _ = SOME layout` >>
         PairCases_on `layout` >> gvs[lookup_nonreentrant_slot_def]) >>
     strip_tac >>
     `s = NONE \/ context_function_live cx (s,nm)` by
       (Cases_on `s = NONE` >> fs[context_function_live_def] >>
        drule_all linked_live_functions_function_live >> simp[]) >>
     qpat_assum `!src tops vis mut nr rr name args dflts ret ss. _`
       (qspecl_then [`s`,`tops`,`v`,`m`,`nrr`,`rr`,`nm`,`ar`,
         `df`,`rt`,`code`] mp_tac) >>
     simp[supported_deploy_declaration_def]) >>
  simp[contract_inv_def, Abbr `ce`, cenv_module_pins_mods_def,
       build_compile_env_unit_def, pairTheory.ELIM_UNCURRY,
       GSYM contract_keys_def, get_tenv_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_then assume_tac ALOOKUP_MEM >>
      drule_all_then assume_tac vyperTypeContractTheory.contract_keys_module_distinct >>
      qpat_assum `!src tops. _ ==> supported_module_headers tops /\ _`
        (drule_then strip_assume_tac) >>
      simp[] >>
      fs[supported_program_def, supported_program_deploy_def, EVERY_MEM,
         supported_module_headers_def] >> metis_tac[]) >>
  conj_tac
  >- (qexistsl_tac [`rp`,`unit`] >> Cases_on `cx.in_deploy` >> fs[] >>
      qexists_tac `rbc` >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!s tops v m nrr rr nm ar df rt code.
          ALOOKUP mods s = SOME tops /\
          MEM (FunctionDecl v m nrr rr nm ar df rt code) tops /\
          (s = NONE \/ MEM (s,nm) (linked_live_functions mods exps)) ==>
          function_mutability_ok mods v m nrr df code /\
          (nrr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
          (cx.in_deploy /\ v = Deploy ==> EVERY (supported_value_type tops o SND) ar)`
        (qspecl_then [`src'`,`tops`,`vis'`,`mut'`,`nr`,`rr`,`name'`,
          `args'`,`dflts`,`ret'`,`ss'`] mp_tac) >>
      simp[]) >>
  FIRST_ASSUM ACCEPT_TAC
QED
