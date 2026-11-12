(* Checker-side extraction of runtime mutation-root safety. *)
Theory vyperCheckedRuntimeWriteSafety
Ancestors
  list pair option finite_map vyperAST vyperTypeSystem vyperRuntimeWriteSafety
  vyperTypeContract vyperTypeEnvExtension vyperTypeContractStaticMaps
  vyperTypeContractContext vyperContext vyperInterpreter vyperState alist
  vyperGetter vyperTypeContractGetter

Theorem well_typed_write_roots[local]:
  (!env e. well_typed_expr env e ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      expr_writes_ok (runtime_write_root R) e) /\
  (!env e. !vt. type_place_expr env e = SOME vt ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      expr_writes_ok (runtime_write_root R) e) /\
  (!env tgt. !vt. type_place_target env tgt = SOME vt ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      runtime_write_root R tgt /\ target_writes_ok (runtime_write_root R) tgt) /\
  (!env es. well_typed_exprs env es ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) es) /\
  (!env opt. well_typed_opt env opt ==> T) /\
  (!env kes. well_typed_named_exprs env kes ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) (MAP SND kes))
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rw[well_typed_expr_def, expr_writes_ok_def, runtime_write_root_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem well_typed_atarget_write_roots[local]:
  !env tgt ty. well_typed_atarget env tgt ty ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      atarget_writes_ok (runtime_write_root R) tgt
Proof
  recInduct well_typed_atarget_ind >> conj_tac
  >- (simp[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
      metis_tac[cj 3 well_typed_write_roots]) >>
  rw[well_typed_atarget_def, atarget_writes_ok_def] >>
  gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
  first_x_assum irule >> simp[MEM_EL] >> metis_tac[]
QED

Theorem atarget_accepts_write_roots[local]:
  atarget_accepts env tgt ty /\
  (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
  (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
  atarget_writes_ok (runtime_write_root R) tgt
Proof
  Cases_on `tgt`
  >- (simp[atarget_accepts_def, atarget_writes_ok_def] >>
      rpt strip_tac >> Cases_on `type_place_target env b` >> gvs[] >>
      rename1 `type_place_target env b = SOME vt` >> Cases_on `vt` >> gvs[] >>
      metis_tac[cj 3 well_typed_write_roots]) >>
  simp[atarget_accepts_def] >> metis_tac[well_typed_atarget_write_roots]
QED

Theorem type_stmt_write_roots[local]:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      stmt_writes_ok (runtime_write_root R) s) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
    !R. (!sid id ty. FLOOKUP env.bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      stmts_writes_ok (runtime_write_root R) ss)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  gvs[IS_SOME_EXISTS, well_typed_target_def]
  >~ [`well_typed_iterator env typ it`]
  >- (Cases_on `it` >> gvs[well_typed_iterator_def] >>
      metis_tac[cj 1 well_typed_write_roots]) >>
  all_tac >>~- ([`expr_writes_ok _ _`],
    metis_tac[cj 1 well_typed_write_roots]) >>
  gvs[well_typed_custom_error_def] >>~- ([`EVERY (expr_writes_ok _) _`],
    metis_tac[cj 4 well_typed_write_roots]) >>~- ([`runtime_write_root _ _`],
    metis_tac[cj 3 well_typed_write_roots]) >>~- ([`target_writes_ok _ _`],
    metis_tac[cj 3 well_typed_write_roots]) >>~- ([`atarget_writes_ok _ _`],
    metis_tac[atarget_accepts_write_roots]) >>
  gvs[extend_local_def] >> metis_tac[type_stmt_preserve_nonlocal_fields]
QED

Theorem check_function_body_write_roots:
  !layouts addr mods art src vis mut nr args dflts ret body R.
  check_function_body layouts addr mods art src vis mut nr args dflts ret body /\
  (!sid id ty. FLOOKUP art.cta_bare_global_assignable (sid,id) = SOME ty ==> R sid id) /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==> R sid id) ==>
  EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
  stmts_writes_ok (runtime_write_root R) body
Proof
  simp[check_function_body_def, IS_SOME_EXISTS] >> rpt strip_tac >>
  all_tac >>~- ([`EVERY (expr_writes_ok _) _`],
    irule (cj 4 well_typed_write_roots) >> goal_assum (drule_at Any) >>
    simp[defaults_env_def, function_entry_env_def,
         FOLDL_extend_local_args_static, artifact_env_def]) >>
  drule (CONJUNCT2 type_stmt_write_roots) >>
  disch_then (qspec_then `R` mp_tac) >>
  simp[function_entry_env_def, FOLDL_extend_local_args_static, artifact_env_def]
QED

Theorem well_typed_runtime_writes[local]:
  (!env e. well_typed_expr env e ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      expr_writes_ok (runtime_write_root R) e) /\
  (!env e. !vt. type_place_expr env e = SOME vt ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      expr_writes_ok (runtime_write_root R) e) /\
  (!env tgt. !vt. type_place_target env tgt = SOME vt ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      runtime_write_root R tgt /\ target_writes_ok (runtime_write_root R) tgt) /\
  (!env es. well_typed_exprs env es ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) es) /\
  (!env opt. well_typed_opt env opt ==> T) /\
  (!env kes. well_typed_named_exprs env kes ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) (MAP SND kes))
Proof
  conj_tac >- (rpt strip_tac >> irule (cj 1 well_typed_write_roots) >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule (cj 2 well_typed_write_roots) >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
    irule (cj 3 well_typed_write_roots) >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule (cj 4 well_typed_write_roots) >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> irule (cj 6 well_typed_write_roots) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem well_typed_atarget_runtime_writes[local]:
  !env tgt ty. well_typed_atarget env tgt ty ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      atarget_writes_ok (runtime_write_root R) tgt
Proof
  rpt strip_tac >> drule well_typed_atarget_write_roots >>
  disch_then irule >> simp[]
QED

Theorem atarget_accepts_runtime_writes[local]:
  atarget_accepts env tgt ty /\ env.bare_global_assignable = FEMPTY /\
  (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
  atarget_writes_ok (runtime_write_root R) tgt
Proof
  strip_tac >> drule atarget_accepts_write_roots >>
  disch_then irule >> simp[]
QED

Theorem type_stmt_runtime_writes[local]:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      stmt_writes_ok (runtime_write_root R) s) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
    !R. env.bare_global_assignable = FEMPTY /\
      (!sid id vt. FLOOKUP env.toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP env.bare_globals (sid,id) = NONE ==> R sid id) ==>
      stmts_writes_ok (runtime_write_root R) ss)
Proof
  conj_tac
  >- (rpt strip_tac >> drule (cj 1 type_stmt_write_roots) >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> drule (cj 2 type_stmt_write_roots) >>
  disch_then irule >> simp[]
QED

Theorem check_function_body_runtime_writes[local]:
  !layouts addr mods art src vis mut nr args dflts ret body R.
  check_function_body layouts addr mods
    (art with cta_bare_global_assignable := FEMPTY)
    src vis mut nr args dflts ret body /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==> R sid id) ==>
  EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
  stmts_writes_ok (runtime_write_root R) body
Proof
  rpt gen_tac >> strip_tac >> drule check_function_body_write_roots >>
  disch_then irule >> simp[]
QED

Theorem checked_runtime_function_writes[local]:
  !layouts addr mods art src ts vis mut nr raw fn args dflts ret body R.
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated layouts addr src ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts /\
  vis <> Deploy /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==> R sid id) ==>
  EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
  stmts_writes_ok (runtime_write_root R) body
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM (FunctionDecl _ _ _ _ _ _ _ _ bod) ts` >>
  `check_function_body layouts addr mods
    (art with cta_bare_global_assignable := FEMPTY)
    src vis mut nr args dflts ret bod` suffices_by
    metis_tac[check_function_body_runtime_writes] >>
  drule_all module_allocated_function_live >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `EVERY _ mods` mp_tac >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `(src,ts)` mp_tac) >>
  impl_tac >- metis_tac[ALOOKUP_MEM] >>
  simp[check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x ts ==> check_toplevel_body _ _ _ _ _ _ _ x`
    (qspec_then `FunctionDecl vis mut nr raw fn args dflts ret bod` mp_tac) >>
  simp[check_toplevel_body_def, check_function_body_in_mode_def,
       function_live_def]
QED

Theorem checked_singleton_callable_writes[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==> R sid id) ==>
  runtime_callable_writes_ok (ALOOKUP [(NONE,tops)]) R
Proof
  strip_tac >> rewrite_tac[runtime_callable_writes_ok_def] >> rpt gen_tac >>
  Cases_on `sid` >> simp[] >> strip_tac >> gvs[] >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  irule checked_runtime_function_writes >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`addr`,`art`,`layouts`,`[(NONE,tops)]`,`NONE`] >> simp[] >>
  irule check_contract_main_module_allocated >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem checked_runtime_write_roots[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\ tx.target = addr ==>
  !sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==>
    ?ts decl. get_module_code (initial_evaluation_context sources layouts tx entry) sid = SOME ts /\
      find_var_decl_by_name id ts = SOME decl
Proof
  strip_tac >> drule_all check_contract_toplevel_vtypes_consistent_initial >>
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `vt` >>
  first_x_assum drule >> strip_tac >>
  gvs[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]
QED

Theorem build_getter_writes_ok[local]:
  !e kt vt n args ret exp.
  build_getter e kt vt n = (args,ret,exp) ==>
  !P. expr_writes_ok P e ==> expr_writes_ok P exp
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >>
  simp[Once build_getter_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), expr_writes_ok_def] >>
  qpat_x_assum `(\(a,b,c). _) _ = _` mp_tac >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[expr_writes_ok_def]
QED

Theorem getter_writes_ok[local]:
  getter nr e kt vt = (mut,gnr,args,dflts,ret,bod) /\ expr_writes_ok P e ==>
  EVERY (expr_writes_ok P) dflts /\ stmts_writes_ok P bod
Proof
  simp[getter_def] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  simp[stmt_writes_ok_def] >> metis_tac[build_getter_writes_ok]
QED

Theorem external_getter_writes_ok[local]:
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,bod) ==>
  EVERY (expr_writes_ok P) dflts /\ stmts_writes_ok P bod
Proof
  Cases_on `decl` >> simp[external_getter_tuple_def]
  >- (rename1 `external_getter_tuple src (VariableDecl vis _ _ _ _)` >>
      Cases_on `vis` >> simp[external_getter_tuple_def] >>
      IF_CASES_TAC >> simp[] >> strip_tac >> gvs[stmt_writes_ok_def, expr_writes_ok_def] >>
      metis_tac[getter_writes_ok, expr_writes_ok_def]) >>
  rename1 `external_getter_tuple src (HashMapDecl vis _ _ _ _ _)` >>
  Cases_on `vis` >> simp[external_getter_tuple_def] >>
  metis_tac[getter_writes_ok, expr_writes_ok_def]
QED

Theorem checked_external_selected_writes[local]:
  !am tx mods art cx src ts mut nr args dflts ret bod R.
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code cx src = SOME ts /\
  ALOOKUP mods src = SOME ts /\ module_allocated am.layouts tx.target src ts /\
  lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,dflts,ret,bod) /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==> R sid id) ==>
  EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
  stmts_writes_ok (runtime_write_root R) bod
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lookup_exported_function_checked_cases_selected >> strip_tac
  >- (drule checked_runtime_function_writes >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[external_getter_writes_ok]
QED

(* A single source-level relation serves callable closure, selected entry safety,
   and semantic root resolution. No machine-value invariant is required. *)
Theorem checked_singleton_runtime_write_safety:
  !am tx tops art src ts mut nr args dflts ret bod.
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx src)
    am tx.function_name = SOME (mut,nr,args,dflts,ret,bod) ==>
  ?R. runtime_callable_writes_ok
        (get_module_code (initial_evaluation_context am.sources am.layouts tx src)) R /\
      runtime_write_roots_resolve
        (initial_evaluation_context am.sources am.layouts tx src) R /\
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) bod
Proof
  rpt gen_tac >> strip_tac >>
  qexists `\sid id. ?vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
                        FLOOKUP art.cta_bare_globals (sid,id) = NONE` >>
  conj_tac
  >- (drule checked_singleton_callable_writes >>
      disch_then (qspec_then `\sid id. ?vt.
        FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
        FLOOKUP art.cta_bare_globals (sid,id) = NONE` mp_tac) >>
      simp[] >>
      simp[runtime_callable_writes_ok_def, get_module_code_def,
           initial_evaluation_context_def]) >>
  conj_tac
  >- (simp[runtime_write_roots_resolve_def] >> rpt strip_tac >>
      simp[checked_runtime_write_roots]) >>
  `src = NONE /\ ts = tops` by
    (qpat_x_assum `get_module_code _ _ = _` mp_tac >>
     simp[get_module_code_def, initial_evaluation_context_def] >>
     Cases_on `src` >> simp[]) >>
  irule checked_external_selected_writes >>
  goal_assum (drule_at Any) >> gvs[] >>
  irule check_contract_main_module_allocated >>
  goal_assum (drule_at Any) >> simp[]
QED
