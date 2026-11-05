(* Label reservation boundaries for the runtime prefix before internal bodies. *)
Theory bodyIntCallPrefixLabels
Ancestors
  bodyIntCallSupportedStmtLabels bodyIntCallStmtHelperSoundLabels bodyIntCallAbiLabels
  bodyIntCallStmtControlLabels
  bodyIntCallLabelReservations bodyIntCallContextLabels moduleLowering
  context compileEnv emitHelper list vyperCompiler loweringShapeProps
  loweringShapeDefs pred_set combin emitHelperProps compileVyper supportedProgram supportedNames
Libs
  monadsyntax

Theorem compiler_label_hoare_decode_args:
  !args ce off load hi adj origin pending.
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_decode_args ce args off load hi adj)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_decode_args_def, compiler_label_hoare_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_decode_args_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >- suspend "primitive" >>
  IF_CASES_TAC >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_abi_decode_to_buf] >>
       rpt gen_tac >> BETA_TAC) >> simp[]
QED

Resume compiler_label_hoare_decode_args[primitive]:
  ntac 3 (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_abi_clamp_basetype] >>
    rpt gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Finalise compiler_label_hoare_decode_args

Theorem compiler_label_hoare_register_positional_args:
  !args ce off origin pending.
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_register_positional_args ce args off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_register_positional_args_def,
                compiler_label_hoare_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_decode_args]
QED

Theorem compiler_label_hoare_nonreentrant:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_nonreentrant_lock key trans view)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_nonreentrant_unlock key trans view)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `view` >> Cases_on `trans` >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def, comp_ignore_bind_def,
       compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  rpt (irule compiler_label_hoare_preserving_bind >>
       simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       rpt gen_tac >> BETA_TAC)
QED

Theorem compiler_label_hoare_guarded_body:
  supported_stmts tops bindings ss ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_guarded_body ce nr key trans view ss ret)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `nr` >> simp[compiler_label_hoare_nonreentrant,
        compiler_label_hoare_typed_primitives]) >>
  rpt gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- metis_tac[compiler_label_hoare_supported_stmts_general] >>
  rpt gen_tac >> BETA_TAC >> ho_match_mp_tac compiler_label_hoare_termination_read >>
  gen_tac >> IF_CASES_TAC >- simp[compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `nr` >> simp[compiler_label_hoare_nonreentrant,
        compiler_label_hoare_typed_primitives]) >>
  rpt gen_tac >> BETA_TAC >> Cases_on `ret` >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_label_hoare_external_function_body:
  supported_stmts tops bindings ss ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_external_function_body ce args nr key trans view ss ret)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_external_function_body_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_register_positional_args] >>
  metis_tac[compiler_label_hoare_guarded_body]
QED

Theorem compiler_label_hoare_fallback_body:
  supported_stmts tops bindings ss ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_fallback_body ce payable nr key trans view ss ret)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_fallback_body_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `payable` >> simp[compiler_label_hoare_typed_primitives] >>
      rpt (irule compiler_label_hoare_preserving_bind >>
           simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
           rpt gen_tac >> BETA_TAC)) >>
  rpt gen_tac >> BETA_TAC >> metis_tac[compiler_label_hoare_guarded_body]
QED

Theorem compiler_label_hoare_selector_checks:
  !sels method origin pending.
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_selector_checks method sels)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_selector_checks_def, compiler_label_hoare_typed_primitives] >>
  rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_selector_checks_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_context_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  ntac 2 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_context_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_context_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  gvs[pred_setTheory.DELETE_INSERT] >>
  `pending DELETE lbl DELETE lbl' = pending` by pred_setLib.ASM_SET_TAC [] >>
  simp[]
QED

Theorem compiler_label_hoare_selector_dispatch_linear:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_selector_dispatch_linear sels fallback)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  ntac 3 (irule compiler_label_hoare_preserving_bind >>
    simp[compiler_label_hoare_context_primitives] >> rpt gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_context_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  `pending DELETE lbl = pending` by pred_setLib.ASM_SET_TAC [] >>
  simp[pred_setTheory.DELETE_INSERT] >>
  ntac 2 (irule compiler_label_hoare_preserving_bind >>
    simp[compiler_label_hoare_context_primitives] >> rpt gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_selector_checks, compiler_label_hoare_context_primitives]
QED

Theorem compiler_label_hoare_entry_checks:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_entry_checks min_cds payable)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_entry_checks_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `payable` >> simp[compiler_label_hoare_typed_primitives] >>
      rpt (irule compiler_label_hoare_preserving_bind >>
           simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
           rpt gen_tac >> BETA_TAC)) >>
  rpt gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives] >>
  rpt (irule compiler_label_hoare_preserving_bind >>
       simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       rpt gen_tac >> BETA_TAC)
QED

Theorem compiler_label_hoare_external_fn_bodies:
  !fns origin pending.
  ALL_DISTINCT (MAP FST fns) /\ DISJOINT (set (MAP FST fns)) pending /\
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss) fns ==>
  compiler_label_hoare
    (compiler_label_reservation origin (set (MAP FST fns) UNION pending))
    (compile_external_fn_bodies fns)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >- simp[compile_external_fn_bodies_def, compiler_label_hoare_typed_primitives] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
  rewrite_tac[compile_external_fn_bodies_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  `((h0 INSERT set (MAP FST fns)) UNION pending) DELETE h0 =
    set (MAP FST fns) UNION pending` by pred_setLib.ASM_SET_TAC [] >>
  simp[] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_entry_checks] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- metis_tac[compiler_label_hoare_external_function_body] >>
  rpt gen_tac >> BETA_TAC >> first_x_assum irule >>
  pred_setLib.ASM_SET_TAC []
QED

Theorem compiler_label_hoare_runtime_prefix:
  ALL_DISTINCT (MAP FST external_fns) /\
  DISJOINT (set (MAP FST external_fns)) pending /\
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss) external_fns /\
  (case fallback_fn of NONE => T
   | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
       ?bindings. supported_stmts tops bindings ss) ==>
  compiler_label_hoare
    (compiler_label_reservation origin (set (MAP FST external_fns) UNION pending))
    (do fallback_lbl <- fresh_label "fallback";
        compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl;
        compile_external_fn_bodies external_fns;
        new_block fallback_lbl;
        (case fallback_fn of
           NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
         | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
             compile_fallback_body ce pay nr key tr view ss ret)
     od)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_selector_dispatch_linear] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_bind >>
  qexists_tac `\r out. compiler_label_reservation origin (lbl INSERT pending) out` >>
  reverse conj_tac >- suspend "external_list" >>
  gen_tac >> BETA_TAC >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV ETA_CONV))) >>
  irule compiler_label_hoare_new_block_bind >> simp[] >>
  rpt gen_tac >> BETA_TAC >>
  `pending DELETE lbl = pending` by pred_setLib.ASM_SET_TAC [] >>
  simp[pred_setTheory.DELETE_INSERT] >>
  namedCases_on `fallback_fn` ["", "fallback_data"] >>
  gvs[compiler_label_hoare_context_primitives] >>
  PairCases_on `fallback_data` >> gvs[] >>
  metis_tac[compiler_label_hoare_fallback_body]
QED

Resume compiler_label_hoare_runtime_prefix[external_list]:
  `lbl INSERT (set (MAP FST external_fns) UNION pending) =
   set (MAP FST external_fns) UNION (lbl INSERT pending)` by pred_setLib.SET_TAC [] >>
  asm_rewrite_tac [] >> irule compiler_label_hoare_external_fn_bodies >>
  simp[] >> pred_setLib.ASM_SET_TAC []
QED

Finalise compiler_label_hoare_runtime_prefix

Theorem compiler_label_reservation_initial_budget:
  EVERY (\l. ~compiler_label l /\ l <> entry) labels /\ ~compiler_label entry ==>
  compiler_label_reservation
    ((initial_compile_state entry) with cs_blocks :=
      MAP (\l. <|bb_label := l; bb_instructions := []|>) labels)
    (set labels) (initial_compile_state entry)
Proof
  simp[compiler_label_reservation_def, initial_compile_state_def,
       compile_state_ok_def, bound_labels_def, MAP_MAP_o, o_DEF,
       compiler_label_def, EVERY_MEM, SUBSET_DEF, label_external_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem compiler_label_reservation_noninternal:
  compiler_label_reservation origin pending out /\
  (!l. l IN bound_labels origin ==> ~internal_label_ok l) ==>
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks out)
Proof
  strip_tac >>
  `!l. l IN compiler_labels_future origin.cs_next_label ==> ~internal_label_ok l` by
    (rpt strip_tac >>
     `compiler_label l` by
       (simp[compiler_label_def] >>
        `compiler_labels_future origin.cs_next_label SUBSET compiler_labels_future 0` by
          (irule compiler_labels_future_antimono >> simp[]) >>
        fs[pred_setTheory.SUBSET_DEF]) >>
     drule compiler_label_prefix >> strip_tac >> gvs[internal_label_ok_def]) >>
  gvs[compiler_label_reservation_def, all_blocks_def, EVERY_MEM,
      bound_labels_def, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_MAP]
QED

Theorem runtime_prefix_noninternal:
  ALL_DISTINCT (MAP FST external_fns) /\
  EVERY (\l. ~compiler_label l /\ l <> "__entry" /\ ~internal_label_ok l)
    (MAP FST external_fns) /\
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss) external_fns /\
  (case fallback_fn of NONE => T
   | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
       ?bindings. supported_stmts tops bindings ss) /\
  (do fallback_lbl <- fresh_label "fallback";
      compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl;
      compile_external_fn_bodies external_fns;
      new_block fallback_lbl;
      (case fallback_fn of
         NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
           compile_fallback_body ce pay nr key tr view ss ret)
   od) (initial_compile_state "__entry") = (r,out) ==>
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks out)
Proof
  strip_tac >>
  qabbrev_tac `origin = (initial_compile_state "__entry") with cs_blocks :=
    MAP (\l. <|bb_label := l; bb_instructions := []|>) (MAP FST external_fns)` >>
  `compiler_label_reservation origin (set (MAP FST external_fns))
     (initial_compile_state "__entry")` by
    (simp[Abbr `origin`] >> irule compiler_label_reservation_initial_budget >>
     gvs[EVERY_MEM, compiler_label_def, compiler_labels_future_def,
         fresh_label_output_def]) >>
  `compiler_label_hoare
    (compiler_label_reservation origin (set (MAP FST external_fns) UNION {}))
    (do fallback_lbl <- fresh_label "fallback";
        compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl;
        compile_external_fn_bodies external_fns;
        new_block fallback_lbl;
        (case fallback_fn of
           NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
         | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
             compile_fallback_body ce pay nr key tr view ss ret)
     od) (\r out. compiler_label_reservation origin {} out)` by
    (irule compiler_label_hoare_runtime_prefix >> simp[] >> metis_tac[]) >>
  `compiler_label_reservation origin {} out` by
    (gvs[compiler_label_hoare_def] >> metis_tac[]) >>
  irule compiler_label_reservation_noninternal >>
  qexistsl_tac [`origin`, `{}`] >> simp[] >>
  simp[Abbr `origin`, bound_labels_def, initial_compile_state_def,
       MAP_MAP_o, o_DEF] >>
  gen_tac >> strip_tac >- gvs[internal_label_ok_def] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem compile_generate_runtime_noninternal_start:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  ALL_DISTINCT (MAP FST external_fns) /\
  EVERY (\l. ~compiler_label l /\ l <> "__entry" /\ ~internal_label_ok l)
    (MAP FST external_fns) /\
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss) external_fns /\
  (case fallback_fn of NONE => T
   | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
       ?bindings. supported_stmts tops bindings ss) ==>
  ?start.
    compile_internal_fn_bodies internal_fns start = ((),final) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  qabbrev_tac `prefix = do
    fallback_lbl <- fresh_label "fallback";
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors) fallback_lbl;
    compile_external_fn_bodies external_fns;
    new_block fallback_lbl;
    (case fallback_fn of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
         compile_fallback_body ce pay nr key tr view ss ret)
    od` >>
  `compile_generate_runtime selectors external_fns internal_fns fallback_fn
     Linear bucket_count fn_metadata_bytes dense_buckets entry_info =
   comp_ignore_bind prefix
     (comp_bind (compile_internal_fn_bodies internal_fns) (\x. comp_return ()))` by
    simp[compile_generate_runtime_def, Abbr `prefix`,
         comp_ignore_bind_def, comp_bind_assoc] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (prefix_result,start)` >> Cases_on `prefix_result` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qexists_tac `start` >> simp[] >>
  qpat_x_assum `prefix _ = _` mp_tac >>
  simp[Abbr `prefix`] >> strip_tac >>
  drule_at (Pos last) runtime_prefix_noninternal >> simp[] >>
  disch_then irule >> qexists_tac `tops` >> simp[]
QED

Theorem package_external_supported_body:
  supported_program tops /\ MEM src (FST (classify_functions tops)) ==>
  (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss)
    (set_external_package_target target (package_external_fn tops use_trans nkeys src))
Proof
  strip_tac >> PairCases_on `src` >>
  drule classify_functions_external_source >> strip_tac >>
  drule_all supported_program_function >>
  simp[supported_function_body_def, package_external_fn_def,
       set_external_package_target_def] >> metis_tac[]
QED

Theorem package_fallback_supported_body:
  supported_program tops ==>
  (case set_fallback_package_target target
     (package_fallback_fn tops use_trans nkeys
       (FST (SND (SND (classify_functions tops))))) of
     NONE => T
   | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
       ?bindings. supported_stmts tops bindings ss)
Proof
  strip_tac >>
  namedCases_on `FST (SND (SND (classify_functions tops)))` ["", "src"]
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  PairCases_on `src` >>
  drule classify_functions_fallback_mem >> strip_tac >>
  drule_all supported_program_function >>
  simp[supported_function_body_def, package_fallback_fn_def,
       set_fallback_package_target_def] >> metis_tac[]
QED

Theorem classified_external_names_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
    ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
      (FST (classify_functions tops)))
Proof
  Induct >> simp[classify_functions_def, supported_function_names_def] >>
  gen_tac >> fs[classify_functions_def] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> Cases_on `h` >>
  gvs[classify_function_def, supported_function_names_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> simp[] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM payload acc0` >> PairCases_on `payload` >> gvs[] >>
  `MEM (payload0,payload1,payload2,payload3,payload4,payload5,payload6,payload7)
    (FST (classify_functions tops))` by simp[classify_functions_def] >>
  drule classify_functions_external_source >>
  metis_tac[MEM_supported_function_names]
QED

Theorem supported_external_package_labels:
  supported_program tops ==>
  ALL_DISTINCT (MAP FST (MAP (set_external_package_target target o
    package_external_fn tops use_trans nkeys) (FST (classify_functions tops)))) /\
  EVERY (\l. ~compiler_label l /\ l <> "__entry" /\ ~internal_label_ok l)
    (MAP FST (MAP (set_external_package_target target o
      package_external_fn tops use_trans nkeys) (FST (classify_functions tops))))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (classify_functions tops)))` by
    (irule classified_external_names_distinct >>
     drule supported_program_names >>
     metis_tac[supported_declaration_names_unique]) >>
  conj_tac
  >- ( `MAP FST (MAP (set_external_package_target target o
         package_external_fn tops use_trans nkeys) (FST (classify_functions tops))) =
        MAP (\n. "fn_" ++ n)
          (MAP (\p. FST (SND (SND (SND p)))) (FST (classify_functions tops)))` by
         (simp[MAP_MAP_o, o_DEF] >> irule MAP_CONG >>
          simp[pairTheory.FORALL_PROD, package_external_fn_def,
               set_external_package_target_def]) >>
       asm_rewrite_tac [] >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
       package_external_fn_def, set_external_package_target_def] >>
  rpt gen_tac >> strip_tac >>
  simp[internal_label_ok_def] >> strip_tac >>
  drule compiler_label_prefix >> strip_tac >> gvs[]
QED

Theorem supported_runtime_prefix_descriptors:
  supported_program tops ==>
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,ss,ret).
    ?bindings. supported_stmts tops bindings ss)
    (MAP (set_external_package_target target o package_external_fn tops use_trans nkeys)
      (FST (classify_functions tops))) /\
  (case set_fallback_package_target target
     (package_fallback_fn tops use_trans nkeys
       (FST (SND (SND (classify_functions tops))))) of
     NONE => T
   | SOME (ce,pay,nr,key,tr,view,ss,ret) =>
       ?bindings. supported_stmts tops bindings ss)
Proof
  strip_tac >> conj_tac
  >- (simp[EVERY_MAP, EVERY_MEM, o_DEF] >> rpt strip_tac >>
      irule package_external_supported_body >> simp[]) >>
  irule package_fallback_supported_body >> simp[]
QED

Theorem compile_generate_runtime_source_noninternal_start:
  supported_program tops /\
  external_fns = MAP
    (set_external_package_target target o package_external_fn tops use_trans nkeys)
    (FST (classify_functions tops)) /\
  fallback_fn = set_fallback_package_target target
    (package_fallback_fn tops use_trans nkeys
      (FST (SND (SND (classify_functions tops))))) /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) ==>
  ?start.
    compile_internal_fn_bodies internal_fns start = ((),final) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >> drule_at (Pos hd) compile_generate_runtime_noninternal_start >>
  disch_then irule >>
  drule supported_external_package_labels >>
  disch_then (qspecl_then [`use_trans`, `target`, `nkeys`] strip_assume_tac) >>
  drule supported_runtime_prefix_descriptors >>
  disch_then (qspecl_then [`use_trans`, `target`, `nkeys`] strip_assume_tac) >>
  gvs[] >> qexists_tac `tops` >> simp[]
QED
