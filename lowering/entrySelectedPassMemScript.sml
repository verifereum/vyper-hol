(* Selected dispatch and passing checks, with a consumer-owned registration continuation. *)
Theory entrySelectedPassMem
Ancestors
  entryPrefixMem entryAcceptedCheckFacts entryRejectCode entrySourcePackages
  entryRuntimeSlice entrySelectedOwnership entryDispatchMem entryDispatchProps entryValueRejectFacts fragExec compileEnv
  moduleLowering moduleLoweringProps words list supportedDecls supportedProgram
  e2eDefs vyperLoweringCorrect compileVyper venomInst venomState finite_map

Theorem selected_dispatch_checks_mem_safe[local]:
  compile_selector_dispatch_linear sels fl sf = ((),sd) /\
  fn_has_code sf sd fn /\ EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  compile_entry_checks mc pay sc = ((),sk) /\ fn_has_code sc sk fn /\
  sd.cs_next_var <= sc.cs_next_var /\ sc.cs_current_insts = [] /\
  linear_dispatch_target s.vs_call_ctx.cc_calldata sels fl = sc.cs_current_bb /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt sf s /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\ sf.cs_current_insts = [] /\
  (!t. vars_pc_only s t /\ fresh_vars_wrt sk t /\
       ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
       t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
       (!n. mem_safe_run n ctx fn t) /\
       (t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t)) ==>
  !n. mem_safe_blocks n ctx fn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (cj 2 compile_selector_dispatch_linear_mem_safe) >>
  simp[] >> qexistsl_tac [`fl`, `sels`, `sf`, `sd`] >> simp[] >>
  reverse conj_tac >- fs[] >>
  gen_tac >> strip_tac >>
  `fresh_vars_wrt sc t` by gvs[fresh_vars_wrt_def] >>
  drule vars_pc_only_fields >> strip_tac >>
  irule compile_entry_checks_pass_mem_safe_blocks >>
  simp[] >> qexistsl_tac [`mc`, `pay`, `sc`, `sk`] >> simp[] >>
  reverse conj_tac
  >- (strip_tac >>
      `sk = sc` by
        (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
         simp[compile_entry_checks_def, comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
      gvs[] >> first_x_assum drule >> simp[]) >>
  gen_tac >> strip_tac >>
  `vars_pc_only s t'` by metis_tac[vars_pc_only_trans] >>
  first_x_assum drule >> simp[]
QED

Theorem source_selected_entry_prefix_mem_safe:
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
  ?lbl ce pa mc pay key tr view rt sk cenv sa sb.
    set_external_package_target rp.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)) =
      (lbl,ce,pa,mc,pay,F,key,tr,view,fbody,rt) /\
    compile_register_positional_args ce pa 4 sk = (cenv,sa) /\
    compile_guarded_body cenv F key tr view fbody rt sa = ((),sb) /\
    fn_has_code sa sb efn /\ fn_inst_ids_distinct efn /\
    ((!t. vars_pc_only
           (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>) t /\
          fresh_vars_wrt sk t /\ ~t.vs_halted /\
          t.vs_current_bb = sk.cs_current_bb /\
          t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
          (!n. mem_safe_run n u.cu_context efn t) /\
          (t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n u.cu_context efn t)) ==>
      !n. mem_safe_blocks n u.cu_context efn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0|>))
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
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  drule_all run_lowering_entry_label >> strip_tac >> gvs[] >>
  qexistsl_tac [`sk`, `cenv'`, `sa'`, `sb`] >> simp[] >>
  suspend "prefix"
QED

Resume source_selected_entry_prefix_mem_safe[prefix]:
  `sc.cs_current_bb = "fn_" ++ tx.function_name` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[set_external_package_target_def, package_external_fn_def]) >>
  drule_all source_selected_entry_checks_pass >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~vs.vs_halted` by fs[initial_venom_state_rel_def] >>
  strip_tac >>
  rpt (qpat_x_assum `MEM _ _` kall_tac) >>
  rpt (qpat_x_assum `EVERY _ _` kall_tac) >>
  rpt (qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` kall_tac) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  irule selected_dispatch_checks_mem_safe >> simp[] >>
  goal_assum (drule_at (Pat `compile_selector_dispatch_linear _ _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `compile_entry_checks _ _ _ = _`)) >> simp[] >>
  conj_tac >- (drule_all valid_call_linear_dispatch_target >> simp[]) >>
  conj_tac >- irule (SRULE [] linear_selectors_lt) >>
  fs[initial_venom_state_rel_def, fresh_vars_wrt_def, lookup_var_def]
QED
Finalise source_selected_entry_prefix_mem_safe
