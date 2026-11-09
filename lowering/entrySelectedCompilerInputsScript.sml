(* Source-selected joint compiler intervals and entry-control inputs. *)
Theory entrySelectedCompilerInputs
Ancestors
  entrySelectedRegistrationIntervals entrySelectedOwnership entryRegistrationOpen
  entryAcceptedCheckFacts entrySourcePackages entryRejectCode entryValueRejectFacts entryRuntimeSlice
  entryDispatchMem entryDispatchProps moduleLoweringProps compileVyper compileEnv
  supportedProgram supportedDecls e2eDefs vyperLoweringCorrect venomWf
  removeUnusedSsaProofs venomInst venomState fragExec finite_map list words

Theorem source_selected_compiler_inputs:
  lower_vyper_runtime_unit tops rp = SOME u /\ supported_program tops /\
  source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE) es = (INL (),es') /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?lbl ce pa mc pay key tr view rt sels fl sf sd sc sk cer registered completed.
    set_external_package_target rp.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)) =
      (lbl,ce,pa,mc,pay,F,key,tr,view,fbody,rt) /\
    compile_selector_dispatch_linear sels fl sf = ((),sd) /\
    fn_has_code sf sd efn /\ EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
    compile_entry_checks mc pay sc = ((),sk) /\ fn_has_code sc sk efn /\
    sd.cs_next_var <= sc.cs_next_var /\ sc.cs_current_insts = [] /\
    linear_dispatch_target vs.vs_call_ctx.cc_calldata sels fl = sc.cs_current_bb /\
    (pay \/ vs.vs_call_ctx.cc_callvalue = 0w) /\
    mc <= LENGTH vs.vs_call_ctx.cc_calldata /\
    fresh_vars_wrt sf (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) /\
    ~vs.vs_halted /\ elbl = sf.cs_current_bb /\ sf.cs_current_insts = [] /\
    vs.vs_allocas = FEMPTY /\
    compile_register_positional_args ce pa 4 sk = (cer,registered) /\
    compile_guarded_body cer F key tr view fbody rt registered = ((),completed) /\
    fn_has_code registered completed efn /\ fn_has_code sk registered efn /\
    fn_has_code sk completed efn /\ cs_extends sk registered /\
    fn_inst_ids_distinct efn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts efn)) /\
    ~block_is_terminated registered /\ sc.cs_current_bb = lbl
Proof
  strip_tac >> drule_all source_selected_guarded_code >> strip_tac >>
  drule_all lower_runtime_selected_source_packages >> strip_tac >>
  `MEM (lbl,ce,pa,mc,pay,F,key,tr,view,fbody,rt) exts` by
    (asm_rewrite_tac[] >> rewrite_tac[MEM_MAP] >>
     qexists `(mut,F,lookup_raw_return_or_F (NONE : num option)
       tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)` >>
     simp[combinTheory.o_THM] >>
     irule supported_external_lookup_classified >>
     conj_tac >- gvs[valid_vyper_call_def] >>
     simp[] >> qexists `tops` >>
     gvs[supported_program_def, supported_declaration_headers_def]) >>
  drule_all run_lowering_selected_registration_intervals >> strip_tac >>
  drule_all run_lowering_entry_label >> strip_tac >> gvs[] >>
  qexistsl [`MAP (\(sel,lbl,z). (sel,lbl))
    (build_selectors (type_env tops) (FST (classify_functions tops)))`, `fl`, `sf`, `sd'`, `sc`,
            `sk`, `cenv'`, `sa'`, `sb`] >> simp[] >>
  suspend "control"
QED

Resume source_selected_compiler_inputs[control]:
  `sc.cs_current_bb = "fn_" ++ tx.function_name` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[set_external_package_target_def, package_external_fn_def]) >>
  drule_all source_selected_entry_checks_pass >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~block_is_terminated sc` by simp[block_is_terminated_def] >>
  `~block_is_terminated sk` by metis_tac[entry_checks_preserve_open] >>
  `~block_is_terminated sa'` by metis_tac[registration_preserves_open] >>
  simp[] >>
  conj_tac >- irule (SRULE [] linear_selectors_lt) >>
  conj_tac >- (drule_all valid_call_linear_dispatch_target >> simp[]) >>
  rpt conj_tac >>
  all_tac
  >~ [`ALL_DISTINCT (MAP _ (fn_insts efn))`]
  >- gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
         MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  fs[initial_venom_state_rel_def, fresh_vars_wrt_def, lookup_var_def]
QED
Finalise source_selected_compiler_inputs
