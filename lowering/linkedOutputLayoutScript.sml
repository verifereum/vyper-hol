(* Code and data layout at the linked unit's finalized entry. *)
Theory linkedOutputLayout
Ancestors
  e2eModsDefs e2eDefs e2eEntry e2eProducers compileUnit vyperCompiler
  deploySymSrcData runtimeSymSrcData immutableCodeLayout asmOptEncodingLayout asmOptimizer
  asmWf asmSem asmSymSem asmDataEnv asmFinalizerPrefixStatic spillWordBounds
  codegenEncodingWf codegenAsmStaticWf codegen
  fnPlanPlaceRevertPostamble
  lowerDloadDefs venomLayout symbolResolve
  vfmExecutionProp vfmState finite_map list rich_list words

Theorem opt_entry_code_layout_valid_own_mods:
  !fin mods exps rpolicy prog prog' am tx es cplan unit.
    fin IN accepted_finalizers /\
    codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
    fin rpolicy prog = SOME prog' /\
    call_state_rel_mods mods exps (assemble prog') am tx es ==>
    code_layout_valid (opt_entry_state_own prog prog' cplan es)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (FST (HD es.contexts)).msgParams.code <= 24576` by
    (`wf_state es /\ (lookup_account tx.target es.rollback.accounts).code =
         (FST (HD es.contexts)).msgParams.code` by
       fs[call_state_rel_mods_def, evm_state_ok_def] >>
     `wf_accounts es.rollback.accounts` by fs[wf_state_def, all_accounts_def] >>
     fs[wf_accounts_def, wf_account_state_def, lookup_account_def] >>
     first_x_assum (qspec_then `tx.target` mp_tac) >> simp[]) >>
  `?section. (FST (HD es.contexts)).msgParams.code = assemble prog' ++ section` by
    fs[call_state_rel_mods_def, installed_code_rel_mods_def] >>
  `LENGTH (assemble prog') < 65536` by fs[LENGTH_APPEND] >>
  drule codegen_assembly_success_shape >> strip_tac >>
  `?prefix. prog = prefix ++ [AsmDataHeader "code_end"]` by
    metis_tac[APPEND_ASSOC] >>
  `~MEM (AsmLabel "code_end") prog` by
    (drule codegen_assembly_symbols >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  `asm_encoding_wf prog /\ !lbl d. ~MEM (AsmPushOfst lbl d) prog` by
    metis_tac[codegen_assembly_asm_encoding_wf, codegen_assembly_no_push_ofst] >>
  `asm_encoding_wf prog' /\ ?head. prog' = head ++ [AsmDataHeader "code_end"]` by
    (Cases_on `fin = K SOME` >- gvs[] >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     drule_all asm_opt_finalizer_end_offset >> simp[]) >>
  `FLOOKUP (SND (compute_label_offsets prog')) "code_end" =
     SOME (LENGTH (assemble prog'))` by
    (irule immutable_code_end_length >> asm_rewrite_tac[] >>
     qexists_tac `head` >> simp[]) >>
  `FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog'))` by
    (qpat_assum `~MEM (AsmLabel "code_end") prog` (fn absent =>
       qpat_assum `FLOOKUP (SND (compute_label_offsets prog')) _ = _` (fn lookup =>
         simp_tac (srw_ss()) [lo_reloc_def, FLOOKUP_FUNION, FLOOKUP_DRESTRICT,
           absent, lookup]))) >>
  qpat_assum `FLOOKUP (lo_reloc _ _) _ = _` (fn labels =>
    qpat_assum `(FST (HD es.contexts)).msgParams.code = _` (fn layout =>
      qpat_assum `LENGTH (FST (HD es.contexts)).msgParams.code <= 24576`
        (mp_tac o REWRITE_RULE [layout, LENGTH_APPEND]) >>
      simp_tac (srw_ss()) [code_layout_valid_def, opt_entry_state_own_def,
        entry_venom_state_frame_fields, FLOOKUP_o_f, DROP_LENGTH_APPEND, dimword_def,
        dimindex_256, layout, labels])) >>
  decide_tac
QED

Theorem lower_vyper_deploy_unit_runtime_data_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME unit ==>
  unit.cu_data_segment =
    [<| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>]
Proof
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[bool_case_eq] >> strip_tac >>
  drule_then ACCEPT_TAC run_deploy_lowering_data
QED

Theorem lower_vyper_runtime_unit_data_empty_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit ==>
  unit.cu_data_segment = []
Proof
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> simp[bool_case_eq] >> strip_tac >> gvs[]
  >- (drule_then ACCEPT_TAC run_grouped_lowering_data_empty) >>
  drule_then ACCEPT_TAC run_lowering_data_empty
QED

Theorem finalized_codegen_code_end:
  fin IN accepted_finalizers /\
  codegen_assembly rpolicy unit = SOME prog /\ asm_static_wf prog /\
  fin rpolicy prog = SOME prog' ==>
  FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog')) /\
  LENGTH (assemble prog') < 65536
Proof
  strip_tac >>
  drule codegen_assembly_success_shape >> strip_tac >>
  `?prefix. prog = prefix ++ [AsmDataHeader "code_end"]` by
    metis_tac[APPEND_ASSOC] >>
  `asm_static_wf prog' /\ FILTER is_data_inst prog' = FILTER is_data_inst prog` by
    (drule_all finalizer_prefix_static >> simp[]) >>
  `?n. EVERY (\i. ~is_data_inst i) (TAKE n prog') /\
       EVERY is_data_inst (DROP n prog')` by
    (irule asm_data_split >> fs[asm_static_wf_def]) >>
  `FILTER is_data_inst (TAKE n prog') = []` by simp[FILTER_EQ_NIL] >>
  `FILTER is_data_inst (DROP n prog') = DROP n prog'` by simp[FILTER_EQ_ID] >>
  `FILTER is_data_inst prog' = DROP n prog'` by
    (`FILTER is_data_inst (TAKE n prog' ++ DROP n prog') = DROP n prog'` by
       (PURE_REWRITE_TAC [FILTER_APPEND] >> asm_rewrite_tac[APPEND]) >>
     fs[]) >>
  `DROP n prog' = FILTER is_data_inst prefix ++ [AsmDataHeader "code_end"]` by
    fs[FILTER_APPEND, is_data_inst_def] >>
  `?head. prog' = head ++ [AsmDataHeader "code_end"]` by
    (qexists_tac `TAKE n prog' ++ FILTER is_data_inst prefix` >>
     qpat_assum `DROP n prog' = _`
       (fn th => PURE_REWRITE_TAC [GSYM APPEND_ASSOC, GSYM th, TAKE_DROP]) >> REFL_TAC) >>
  `asm_encoding_wf prog'` by fs[asm_static_wf_def] >>
  `FLOOKUP (SND (compute_label_offsets prog')) "code_end" =
     SOME (LENGTH (assemble prog'))` by
    (irule immutable_code_end_length >> asm_rewrite_tac[] >>
     qexists_tac `head` >> simp[]) >>
  `~MEM (AsmLabel "code_end") prog` by
    (drule codegen_assembly_symbols >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  conj_tac
  >- (qpat_assum `~MEM (AsmLabel "code_end") prog` (fn absent =>
        qpat_assum `FLOOKUP (SND (compute_label_offsets prog')) _ = _` (fn offset =>
          simp_tac (srw_ss()) [lo_reloc_def, FLOOKUP_FUNION, FLOOKUP_DRESTRICT,
            absent, offset]))) >>
  Cases_on `compute_label_offsets prog'` >>
  fs[asm_encoding_wf_def, symbol_size_def] >>
  qpat_assum `!lbl off. FLOOKUP _ lbl = SOME off ==> _`
    (qspecl_then [`"code_end"`, `LENGTH (assemble prog')`] mp_tac) >>
  simp[] >> disch_then (mp_tac o MATCH_MP (Q.SPEC `2` encode_num_bytes_length_bound)) >>
  simp[EVAL ``256 ** 2 : num``]
QED
