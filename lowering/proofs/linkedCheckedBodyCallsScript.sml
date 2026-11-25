Theory linkedCheckedBodyCalls
Ancestors
  bodyCallSupport whitelistCheckerDecls vyperTypeContractContext
  vyperTypeContractStaticMaps vyperTypeContract vyperTypeSystem
  vyperImportRefs vyperImportRefsProps vyperTypeCallGraph vyperTypeCallGraphSoundness
  vyperAST finite_map option list pair alist relation

Theorem check_contract_linked_body_calls_resolved:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  linked_body_calls_resolved mods cx
Proof
  strip_tac >> PURE_REWRITE_TAC [linked_body_calls_resolved_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `function_live cx.layouts cx.txn.target mods
      (live_functions cx.layouts cx.txn.target mods) (src,name)` by
    (qpat_assum `context_function_live cx (src,name)` mp_tac >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods`
       (fn th => simp_tac (srw_ss()) [th, context_function_live_def])) >>
  `!b checked_art. check_contract b cx.layouts cx.txn.target mods = SOME checked_art /\
      check_function_body_in_mode b vis ==>
      EVERY (\call. call IN FDOM checked_art.cta_fn_sigs) (function_int_calls dflts ss)` by
    (rpt gen_tac >> strip_tac >>
     drule_all check_contract_function_body_MEM >>
     simp[check_function_body_def] >> strip_tac >>
     qpat_assum `IS_SOME (type_stmts _ ret ss)` (strip_assume_tac o
       REWRITE_RULE [IS_SOME_EXISTS]) >>
     drule (cj 2 type_stmt_int_calls_fn_sigs) >>
     simp[function_entry_env_fn_sigs] >> strip_tac >>
     qpat_assum `well_typed_exprs (defaults_env _) dflts`
       (mp_tac o MATCH_MP (cj 4 well_typed_int_calls_fn_sigs)) >>
     simp[defaults_env_def, function_entry_env_fn_sigs, function_int_calls_def, EVERY_APPEND]) >>
  simp_tac std_ss [EVERY_MEM, FORALL_PROD, FST, SND] >>
  map_every qx_gen_tac [`call_src`, `call_name`] >> strip_tac >>
  qabbrev_tac `call_art = if vis = Deploy then art else runtime_art` >>
  qabbrev_tac `call_cx = if vis = Deploy then cx else cx with in_deploy := F` >>
  `check_contract call_cx.in_deploy cx.layouts cx.txn.target mods = SOME call_art /\
   check_function_body_in_mode call_cx.in_deploy vis` by
    (Cases_on `vis = Deploy` >>
     simp[Abbr `call_art`, Abbr `call_cx`, check_function_body_in_mode_def] >>
     fs[check_function_body_in_mode_def]) >>
  `?sig. FLOOKUP call_art.cta_fn_sigs (call_src,call_name) = SOME sig` by
    (simp[FLOOKUP_DEF] >>
     qpat_assum `!b checked_art. _ ==> EVERY _ _`
       (qspecl_then [`call_cx.in_deploy`, `call_art`] mp_tac) >>
     simp[EVERY_MEM] >> disch_then (qspec_then `(call_src,call_name)` mp_tac) >>
     asm_rewrite_tac[]) >>
  qpat_assum `check_contract call_cx.in_deploy _ _ _ = SOME call_art`
    (mp_tac o MATCH_MP (Q.INST [`cx` |-> `call_cx`] check_contract_linked_fn_sigs_declared)) >>
  simp[linked_fn_sigs_declared_def] >>
  disch_then (qspecl_then [`call_src`, `call_name`, `sig`] mp_tac) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`target_tops`,`target_vis`,`target_mut`,`target_nr`,
                              `target_raw`,`target_args`,`target_defaults`,`target_body`]
    strip_assume_tac) >>
  qexists_tac `target_tops` >> simp[supported_linked_callee_def] >>
  `IS_SOME (supported_function_decl target_tops (NONE,call_name) target_vis)` by
    (irule supported_function_decl_exists >> goal_assum (drule_at Any)) >>
  Cases_on `target_vis` >> fs[include_fn_sig_def] >>
  `vis = Deploy /\ cx.in_deploy` by
    (Cases_on `vis = Deploy` >> gvs[Abbr `call_cx`]) >>
  asm_rewrite_tac[] >> disj2_tac >>
  Cases_on `call_src = NONE` >> simp[] >>
  `check_toplevel_decl mods runtime_art src
     (FunctionDecl vis mut nr raw name args dflts ret ss)` by
    (qpat_assum `check_contract F _ _ mods = SOME runtime_art` (fn checked =>
       qpat_assum `ALOOKUP mods src = SOME tops` (fn code =>
         qpat_assum `MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops`
           (fn decl => ACCEPT_TAC
             (MATCH_MP check_contract_toplevel_decl_MEM_checked
               (CONJ checked (CONJ code decl))))))) >>
  `check_toplevel_decl mods runtime_art call_src
      (FunctionDecl Deploy target_mut target_nr target_raw call_name
        target_args target_defaults sig.ret_ty target_body)` by
    (qpat_assum `check_contract F _ _ mods = SOME runtime_art` (fn checked =>
       qpat_assum `ALOOKUP mods call_src = SOME target_tops` (fn code =>
         qpat_assum `MEM (FunctionDecl Deploy target_mut target_nr target_raw call_name
                      target_args target_defaults sig.ret_ty target_body) target_tops`
           (fn decl => ACCEPT_TAC
             (MATCH_MP check_contract_toplevel_decl_MEM_checked
               (CONJ checked (CONJ code decl))))))) >>
  `name = "__init__" /\ call_name = "__init__"` by
    fs[check_toplevel_decl_def, function_header_ok_def] >>
  Cases_on `src = NONE`
  >- (`MEM ((src,name),(src,name)) (contract_call_edges mods)` by
        (qpat_assum `ALOOKUP mods src = SOME tops` (fn code =>
           qpat_assum `MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops` (fn decl =>
             qpat_assum `MEM (call_src,call_name) (function_int_calls dflts ss)` (fn call =>
               mp_tac (MATCH_MP contract_call_edges_function
                 (CONJ (MATCH_MP ALOOKUP_MEM code) (CONJ decl call)))))) >>
         asm_rewrite_tac[]) >>
      `irreflexive (TC (call_edge_rel (contract_call_edges mods)))` by
        (drule checked_contract_call_graph_irreflexive >> simp[]) >>
      qpat_assum `irreflexive _`
        (mp_tac o Q.SPEC `(src,name)` o REWRITE_RULE [irreflexive_def]) >>
      simp[] >> irule TC_SUBSET >> simp[call_edge_rel_def] >>
      qpat_assum `src = NONE` (fn src_eq =>
        qpat_assum `name = "__init__"` (fn name_eq =>
          qpat_assum `MEM ((src,name),(src,name)) (contract_call_edges mods)`
            (ACCEPT_TAC o REWRITE_RULE [src_eq,name_eq])))) >>
  `imported_exprs_refs_ok dflts /\ imported_stmts_refs_ok ss` by
    (`EVERY imported_toplevel_refs_ok tops` by
       (Cases_on `src` >> fs[] >>
        qpat_assum `check_contract F _ _ mods = SOME runtime_art` (fn checked =>
          qpat_assum `ALOOKUP mods (SOME _) = SOME tops`
            (fn code => ACCEPT_TAC (MATCH_MP check_contract_imported_toplevel_refs_ok
              (CONJ checked (MATCH_MP ALOOKUP_MEM code)))))) >>
     qpat_assum `EVERY imported_toplevel_refs_ok tops` (fn refs =>
       qpat_assum `MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops`
         (mp_tac o MATCH_MP (REWRITE_RULE [EVERY_MEM] refs))) >>
     simp[imported_toplevel_refs_ok_def]) >>
  `(!e. imported_expr_refs_ok e ==> EVERY (\call. FST call <> NONE) (int_calls_expr e)) /\
   (!t. imported_base_target_refs_ok t ==> EVERY (\call. FST call <> NONE) (int_calls_target t)) /\
   (!es. imported_exprs_refs_ok es ==> EVERY (\call. FST call <> NONE) (int_calls_exprs es)) /\
   (!opt. imported_optional_expr_refs_ok opt ==> EVERY (\call. FST call <> NONE) (int_calls_opt opt)) /\
   (!kes. imported_field_refs_ok kes ==> EVERY (\call. FST call <> NONE)
        (int_calls_named_exprs kes))` by
    (ho_match_mp_tac int_calls_expr_ind >>
     simp[imported_expr_refs_ok_def, imported_call_refs_ok_def, int_calls_expr_def, EVERY_APPEND]) >>
  `!kes. imported_field_refs_ok kes ==> imported_exprs_refs_ok (MAP SND kes)` by
    (Induct >> simp[imported_expr_refs_ok_def] >> Cases >> simp[imported_expr_refs_ok_def]) >>
  `(!t. imported_target_refs_ok t ==> EVERY (\call. FST call <> NONE) (int_calls_atarget t)) /\
   (!ts. imported_targets_refs_ok ts ==> EVERY (\call. FST call <> NONE) (int_calls_atargets ts))` by
    (ho_match_mp_tac int_calls_atarget_ind >>
     simp[int_calls_atarget_def, imported_target_refs_ok_def, EVERY_APPEND]) >>
  `!positional keywords. int_calls_exprs (positional ++ keywords) =
        int_calls_exprs positional ++ int_calls_exprs keywords` by
    (Induct >> simp[int_calls_expr_def]) >>
  `!error. imported_error_refs_ok error ==>
    EVERY (\call. FST call <> NONE) (int_calls_exprs (custom_error_exprs error))` by
    (Cases >> rw[imported_error_refs_ok_def, custom_error_exprs_def,
                EVERY_APPEND]) >>
  `!iter. imported_iterator_refs_ok iter ==>
    EVERY (\call. FST call <> NONE) (int_calls_iterator iter)` by
    (Cases >> simp[imported_iterator_refs_ok_def, int_calls_iterator_def, EVERY_APPEND]) >>
  `!reason. imported_assert_refs_ok reason ==>
    EVERY (\call. FST call <> NONE) (int_calls_assert_reason reason)` by
    (Cases >> simp[imported_assert_refs_ok_def, int_calls_assert_reason_def]) >>
  `!reason. imported_raise_refs_ok reason ==>
    EVERY (\call. FST call <> NONE) (int_calls_raise_reason reason)` by
    (Cases >> simp[imported_raise_refs_ok_def, int_calls_raise_reason_def]) >>
  `(!s. imported_stmt_refs_ok s ==> EVERY (\call. FST call <> NONE) (int_calls_stmt s)) /\
   (!ss. imported_stmts_refs_ok ss ==> EVERY (\call. FST call <> NONE) (int_calls_stmts ss))` by
    (ho_match_mp_tac int_calls_stmt_ind >>
     simp[int_calls_stmt_def, imported_stmt_refs_ok_def, EVERY_APPEND]) >>
  `EVERY (\call. FST call <> NONE) (function_int_calls dflts ss)` by
    simp[function_int_calls_def, EVERY_APPEND] >>
  qpat_assum `EVERY _ (function_int_calls dflts ss)`
    (mp_tac o Q.SPEC `(call_src,call_name)` o REWRITE_RULE [EVERY_MEM]) >>
  simp[]
QED
