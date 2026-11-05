(* Callee entry invariants for the internal-call body simulation. *)
Theory bodyIntCallEntry
Ancestors
  bodySim bodySimEntry compileEnv intCallCallee vyperInterpreter vyperContext vyperState list compileVyper bodyIntCallEntryEnv
  vyperTypeEvalSoundness vyperTypeBindArguments vyperTypeInvariants exprSimHyps exprSimHypsDefs finite_map
  vyperTypeStoragePreservation vyperTypeEvalStoragePreservation
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend
  bodyIntCallTypingTransfer

Theorem body_inv_push_stack:
  body_inv tops ctx cenv cx ==>
  body_inv tops ctx cenv (cx with stk updated_by CONS src_fn)
Proof
  simp[body_inv_def, get_module_code_def, get_tenv_def]
QED

Theorem body_inv_push_function:
  body_inv tops ctx cenv cx /\
  push_function src_fn sc cx st = (INL cxf,st') ==>
  body_inv tops ctx cenv cxf
Proof
  simp[push_function_def, return_def] >> strip_tac >>
  gvs[] >> irule body_inv_push_stack >> simp[]
QED

(* The initial source environment contains exactly parameter locals; the
   runtime allocation check therefore supplies its local-size invariant. *)
Theorem locals_alloc_ok_params:
  EVERY (\(_,ty). type_memory_bytes cenv ty < 2 ** 64) params /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) params) ==>
  locals_alloc_ok cenv env
Proof
  simp[locals_alloc_ok_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* All source hypotheses here refer to the state after evaluating arguments. *)
Theorem bind_arguments_pushed_env_consistent:
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\
  env_body.current_src = src /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  (!id ty. MEM (id,ty) args ==>
     FLOOKUP env_body.var_types id = SOME ty /\
     FLOOKUP env_body.var_assignable id = SOME T) /\
  (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = id) /\
  (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
     ?id ty. MEM (id,ty) args /\ n = id /\ b = T) /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  env_consistent env_body (cx with stk updated_by CONS (src,fn))
    (st with scopes := [sc])
Proof
  rpt strip_tac >>
  drule_all intcall_default_env_side_conditions >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  simp[env_consistent_def] >> conj_tac
  >- (irule bind_arguments_env_scopes_consistent >>
      qexistsl_tac [`args`, `get_tenv cx`, `vs`] >>
      simp[get_tenv_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
            drule >> strip_tac >> simp[] >> goal_assum drule) >>
      rpt strip_tac >>
      qpat_x_assum `!id ty. MEM (id,ty) args ==> _` drule >> simp[]) >>
  qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
  simp[env_immutables_consistent_def] >> metis_tac[]
QED

Theorem bind_arguments_state_well_typed:
  state_well_typed st /\ bind_arguments tenv args vs = SOME sc ==>
  state_well_typed (st with scopes := [sc])
Proof
  strip_tac >> drule bind_arguments_scope_well_typed_from_success >>
  gvs[state_well_typed_def]
QED

Theorem bind_arguments_popped_empty:
  !tenv args vs sc n entry.
    bind_arguments tenv args vs = SOME sc /\ FLOOKUP sc n = SOME entry ==>
    entry.popped = []
Proof
  Induct_on `args` >-
    (Cases_on `vs` >> simp[bind_arguments_def, FLOOKUP_DEF]) >>
  Cases >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  Cases_on `n = q` >> gvs[] >> metis_tac[]
QED

Theorem bind_arguments_popped_keys_indexed:
  bind_arguments tenv args vs = SOME sc ==> popped_keys_indexed [sc]
Proof
  simp[popped_keys_indexed_def] >> rpt strip_tac >>
  drule_all bind_arguments_popped_empty >> simp[]
QED

(* Scope replacement and call-stack push change neither storage backend nor
   declared regions. This also transports the oracle's future payloads. *)
Theorem intcall_entry_storage:
  (contract_storage_well_formed (cx with stk updated_by f)
     (st with scopes := scopes) <=> contract_storage_well_formed cx st) /\
  (oracle_storage_ok (cx with stk updated_by f) (st with scopes := scopes) <=>
     oracle_storage_ok cx st)
Proof
  conj_tac
  >- simp[contract_storage_well_formed_def, well_formed_storage_def,
          storage_var_in_range_def, get_storage_backend_eq, oneline get_storage_def] >>
  simp[oracle_storage_ok_outcomes]
QED

(* The body environment is supplied by source type soundness, not reconstructed
   from the compiler's local map. Keep its parameter and static projections for
   the later compiler-entry transfer. *)
Theorem intcall_bound_body_typing:
  functions_well_typed cx /\ env_consistent env cx st /\
  state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\
  IS_SOME (FLOOKUP env.fn_sigs (src,fn)) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,ss) /\
  bind_arguments (get_tenv cx) args vs = SOME sc ==>
  ?env_body ret_tv env_after.
    env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret ss = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough ss) /\ stmts_no_control_escape ss /\
    (!id ty. MEM (id,ty) args ==>
       FLOOKUP env_body.var_types id = SOME ty /\
       FLOOKUP env_body.var_assignable id = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==> MEM (n,ty) args) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?ty. MEM (n,ty) args /\ b = T) /\
    env_consistent env_body (cx with stk updated_by CONS (src,fn))
      (st with scopes := [sc])
Proof
  rpt strip_tac >>
  drule_all callable_body_typing_from_env_consistent >> strip_tac >>
  qabbrev_tac `eb = env_body with var_assignable := (K T) o_f env_body.var_assignable` >>
  `(!id ty. MEM (id,ty) args ==>
       FLOOKUP eb.var_types id = SOME ty /\ FLOOKUP eb.var_assignable id = SOME T)` by
    (simp[Abbr `eb`] >> rpt strip_tac >>
     irule permission_true_map_lookup >>
     qpat_x_assum `!id typ. MEM (id,typ) args ==> _` drule >> simp[]) >>
  `(!n b. FLOOKUP eb.var_assignable n = SOME b ==>
       ?ty. MEM (n,ty) args /\ b = T)` by
    (simp[Abbr `eb`, FLOOKUP_o_f, AllCaseEqs()] >> rpt strip_tac >>
     metis_tac[]) >>
  `(!n. FLOOKUP env_body.var_assignable n = SOME T ==>
        FLOOKUP ((K T) o_f env_body.var_assignable) n = SOME T)` by
    simp[FLOOKUP_o_f] >>
  drule_all (cj 2 stmt_permission_transfer) >> strip_tac >>
  rename1 `type_stmts _ ret ss = SOME (env_after with var_assignable := perms)` >>
  `type_stmts eb ret ss = SOME (env_after with var_assignable := perms)` by
    simp[Abbr `eb`] >>
  `env_consistent eb (cx with stk updated_by CONS (src,fn))
     (st with scopes := [sc])` by
    (irule bind_arguments_pushed_env_consistent >>
     simp[Abbr `eb`] >> conj_tac
     >- (qexistsl_tac [`args`, `vs`] >> gvs[] >> metis_tac[]) >>
     qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`eb`, `ret_tv`, `env_after with var_assignable := perms`] >>
  gvs[Abbr `eb`] >> metis_tac[]
QED

Theorem body_inv_internal_prologue:
  body_inv tops ctx cenv cx /\
  compile_internal_prologue cenv params has_rb rt st0 = ((ce,pc),st1) ==>
  body_inv tops ctx (ce with ce_alloca_locals := T) cx
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[body_inv_def] >> qexistsl_tac [`rpolicy`, `unit`] >> simp[]
QED

Theorem body_inv_packaged_internal_entry:
  body_inv tops ctx caller cx /\ target = caller.ce_target /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys caller.ce_is_ctor 0
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st0 = ((ce2,pc),st1) /\
  push_function src_fn sc cx es = (INL cxf,es') ==>
  body_inv tops ctx (ce2 with ce_alloca_locals := T) cxf
Proof
  strip_tac >> drule_all body_inv_push_function >> strip_tac >>
  `body_inv tops ctx
     (build_compile_env tops Internal mut name args ret ss use_trans
        with <| ce_target := caller.ce_target;
                ce_is_ctor := caller.ce_is_ctor |>) cxf` by
    (irule body_inv_build_internal_env >> goal_assum drule) >>
  irule body_inv_internal_prologue >> goal_assum drule >>
  gvs[compileVyperTheory.package_internal_fn_def,
      compileVyperTheory.set_internal_package_target_def,
      compileVyperTheory.update_cenv_nonreentrant_def, body_inv_def] >>
  metis_tac[]
QED

(* Canonical maps are built from tops only, whereas get_tenv may include
   imported modules. These checked projections diagnose the entry interface;
   they are not counterexamples to body_intcall_case. *)
Theorem imported_flag_canonical_count_diagnostic:
  FLOOKUP
    (type_env_all_modules
      [(NONE, []); (SOME 0, [FlagDecl "Imported" ["member"]])])
    (SOME 0, "Imported") = SOME (FlagArgs 1) /\
  SND (build_flag_info [] (K (K 0)) (K 0))
    (nsid_to_string (SOME 0, "Imported")) = 0
Proof
  EVAL_TAC >> simp[FLOOKUP_FUNION, FLOOKUP_UPDATE]
QED

Theorem imported_struct_canonical_map_diagnostic:
  ~sfields_tenv_consistent (make_struct_fields_map [])
    (type_env_all_modules
      [(NONE, []); (SOME 0, [StructDecl "Imported" []])])
Proof
  simp[sfields_tenv_consistent_def, make_struct_fields_map_def,
       build_struct_fields_map_def] >>
  qexistsl_tac [`(SOME 0, "Imported")`, `[]`] >> EVAL_TAC >> simp[FLOOKUP_FUNION, FLOOKUP_UPDATE]
QED
