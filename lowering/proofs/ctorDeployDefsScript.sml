(* Definitions for the deployment composition (e2e_deploy_correctness).
 * TOP-LEVEL: deploy_phases, deploy_entry_state, deploy_source_ok, deploy_dead,
 * deploy_source_exempt, deploy_venom_result_rel.
 * Helper: deploy_venom_result_rel_terminates.  imm_len, mem_dead_bytes
 * and imm_section_dead are immSectionDead's.
 * deploy_venom_result_rel is the Venom-level counterpart of deploy_result_rel:
 * it relates load_contract's result to a run of the deployment unit, and the
 * creation-frame piece turns it into deploy_result_rel.
 *)
Theory ctorDeployDefs
Ancestors
  immSectionDead e2eDeployDefs e2eProducers ptrDiscipline passSimulationDefs
  venomExecSemantics venomState e2eEntry compileVyper compileEnv valueEncoding
  immutableSectionRel vyperValue vyperContext
  callCodeEval callCodeEvalPrims callCodeLookup
  supportedDecls supportedProgram supportedExprs supportedExprForms
  supportedExprTraverse constSubst exprLowering vyperInterpreter vyperState
  vyperStorageFootprint list
  vyperCallFiniteStorageSupport exprSimAbiEncodeArgsLabelReplay

val _ = Parse.hide "body";

(* Classification normalizes defaults and bodies, while constructor metadata
   still identifies the selected source declaration. *)
Theorem classify_function_ctor_source_step[local]:
  !top acc mut nr rr fname args defaults ret body.
    SND (SND (SND (classify_function top acc))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    top = FunctionDecl Deploy mut nr rr fname args defaults ret body \/
    SND (SND (SND acc)) = SOME (mut,nr,rr,fname,args,defaults,ret,body)
Proof
  rpt gen_tac >> PairCases_on `acc` >> Cases_on `top` >>
  simp[classify_function_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> rw[]
QED

Theorem classify_fold_ctor_mem[local]:
  !tops mut nr rr fname args defaults ret body.
    SND (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    MEM (FunctionDecl Deploy mut nr rr fname args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[] >> rpt gen_tac >>
  simp[] >> strip_tac >>
  drule classify_function_ctor_source_step >>
  strip_tac >- simp[] >> metis_tac[]
QED

Theorem classify_functions_ctor_mem:
  !tops mut nr rr fname args defaults ret body.
    SND (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,fname,args,defaults,ret,body) ==>
    ?raw_defaults raw_body.
      MEM (FunctionDecl Deploy mut nr rr fname args raw_defaults ret raw_body) tops /\
      subst_consts_fn (module_consts_env tops [])
        (mut,nr,rr,fname,args,raw_defaults,ret,raw_body) =
        (mut,nr,rr,fname,args,defaults,ret,body)
Proof
  rpt gen_tac >> simp[classify_functions_def] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  PairCases_on `z` >> gvs[constSubstTheory.subst_consts_fn_def] >>
  qexistsl_tac [`z5`, `z7`] >> simp[] >>
  qspec_then `tops` mp_tac classify_fold_ctor_mem >> simp[] >> metis_tac[]
QED

Theorem classify_fold_ctor_lookup[local]:
  !tops src name.
    case SND (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) of
      NONE => lookup_function src name Deploy tops = SOME (Payable,F,[],[],NoneT,[])
    | SOME (mut,nr,rr,fname,args,defaults,ret,body) =>
        fname = name ==>
        lookup_function src name Deploy tops = SOME (mut,nr,args,defaults,ret,body)
Proof
  Induct >- simp[vyperInterpreterTheory.lookup_function_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`src`, `name`] mp_tac) >>
  `?a b c d. FOLDR classify_function ([],[],NONE,NONE) tops = (a,b,c,d)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  simp[] >> strip_tac >> Cases_on `h` >>
  simp[classify_function_def, vyperInterpreterTheory.lookup_function_def]
  >~ [`VariableDecl vd`]
  >- (Cases_on `vd` >> simp[vyperInterpreterTheory.lookup_function_def])
  >~ [`HashMapDecl hd`]
  >- (Cases_on `hd` >> simp[vyperInterpreterTheory.lookup_function_def]) >>
  qmatch_goalsub_rename_tac `case vv of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vv` >> rw[]
QED

Theorem classify_functions_ctor_lookup:
  !tops src name.
    case SND (SND (SND (classify_functions tops))) of
      NONE =>
        vyperInterpreter$lookup_function src name Deploy tops =
          SOME (Payable,F,[],[],NoneT,[])
    | SOME (mut,nr,rr,fname,args,defaults,ret,body) =>
        fname = name ==>
        ?raw_defaults raw_body.
          vyperInterpreter$lookup_function src name Deploy tops =
            SOME (mut,nr,args,raw_defaults,ret,raw_body) /\
          subst_consts_fn (module_consts_env tops [])
            (mut,nr,rr,fname,args,raw_defaults,ret,raw_body) =
            (mut,nr,rr,fname,args,defaults,ret,body)
Proof
  rpt gen_tac >>
  qspecl_then [`tops`, `src`, `name`] mp_tac classify_fold_ctor_lookup >>
  simp[classify_functions_def] >> pairarg_tac >> simp[] >>
  Cases_on `ctor` >> simp[] >>
  PairCases_on `x` >> simp[constSubstTheory.subst_consts_fn_def] >>
  metis_tac[]
QED

(* Every artifact a successful compile_vyper (K SOME) produces for the
   deployment unit, as compile_vyper_runtime_phases does for the runtime unit. *)
Definition deploy_phases_def:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) <=>
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
    dout.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy dout.po_unit = SOME prog /\
    generate_context_plan dout.po_unit.cu_context = SOME cplan /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
           data_segment_asm dout.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    deploy_bc = assemble prog
End

(* The deployment unit's entry state: entry_venom_state with the alloca
   frontier past the immutables fixed region, which the constructor addresses
   by literal offsets rather than through an ALLOCA. *)
Definition deploy_entry_state_def:
  deploy_entry_state prog cplan tops es =
    entry_venom_state prog cplan es with vs_alloca_next := imm_len tops
End

(* deploy_entry_state with prog's layout over es's code, which has prog'
   in front of the constructor arguments. *)
Definition opt_deploy_entry_state_def:
  opt_deploy_entry_state prog prog' cplan tops es =
    opt_entry_state prog prog' cplan es with vs_alloca_next := imm_len tops
End

Theorem opt_deploy_entry_state_identity:
  !tops am tx prog cplan es.
    deploy_state_rel tops (assemble prog) am tx es ==>
    opt_deploy_entry_state prog prog cplan tops es =
    deploy_entry_state prog cplan tops es
Proof
  rw[deploy_state_rel_def, opt_deploy_entry_state_def,
     deploy_entry_state_def, opt_entry_state_def,
     venom_state_component_equality, entry_venom_state_frame_fields] >>
  gvs[listTheory.DROP_APPEND]
QED

Theorem deploy_txp_identity:
  !tops am tx prog cplan es.
    deploy_state_rel tops (assemble prog) am tx es ==>
    tx with code := (opt_deploy_entry_state prog prog cplan tops es).vs_code = tx
Proof
  rpt gen_tac >> rename1 `(opt_deploy_entry_state prog prog cplan tops es).vs_code` >>
  strip_tac >>
  qspecl_then [`tops`, `am`, `tx`, `prog`, `cplan`, `es`]
    (fn th => first_assum (SUBST1_TAC o MATCH_MP th)) opt_deploy_entry_state_identity >>
  gvs[deploy_state_rel_def, deploy_entry_state_def,
      entry_venom_state_frame_fields, call_txn_component_equality]
QED

(* Substitution may insert expressions at names, and folding may replace a
   SHA of a literal. Neither transformation erases a code accessor. *)
Theorem fold_const_builtin_code_accessor[local]:
  supported_expr_exists (\e. ?t xs. e = Builtin t (Acc Code) xs)
    (fold_const_builtin ty bi es) <=>
  supported_expr_exists (\e. ?t xs. e = Builtin t (Acc Code) xs)
    (Builtin ty bi es)
Proof
  Cases_on `bi` >>
  simp[constSubstTheory.fold_const_builtin_def, supported_expr_exists_def] >>
  Cases_on `es` >> simp[supported_expr_exists_def] >>
  Cases_on `t` >> simp[supported_expr_exists_def] >>
  Cases_on `h` >> simp[supported_expr_exists_def] >>
  rename1 `Literal aty l` >> Cases_on `l` >>
  simp[supported_expr_exists_def]
QED

Theorem folded_subst_code_accessor[local]:
  (!env e.
    supported_expr_exists (\x. ?t es. x = Builtin t (Acc Code) es) e ==>
    supported_expr_exists (\x. ?t es. x = Builtin t (Acc Code) es)
      (fold_const_expr (subst_consts_expr env e))) /\
  (!env t.
    supported_target_exists (\x. ?ty es. x = Builtin ty (Acc Code) es) t ==>
    supported_target_exists (\x. ?ty es. x = Builtin ty (Acc Code) es)
      (fold_const_btarget (subst_consts_btarget env t))) /\
  (!env es.
    supported_exprs_exists (\x. ?t xs. x = Builtin t (Acc Code) xs) es ==>
    supported_exprs_exists (\x. ?t xs. x = Builtin t (Acc Code) xs)
      (fold_const_exprs (subst_consts_exprs env es))) /\
  (!env d.
    supported_opt_exists (\x. ?t es. x = Builtin t (Acc Code) es) d ==>
    supported_opt_exists (\x. ?t es. x = Builtin t (Acc Code) es)
      (fold_const_opt (subst_consts_opt env d))) /\
  (!env fs.
    supported_fields_exists (\x. ?t es. x = Builtin t (Acc Code) es) fs ==>
    supported_fields_exists (\x. ?t es. x = Builtin t (Acc Code) es)
      (fold_const_fields (subst_consts_fields env fs)))
Proof
  ho_match_mp_tac constSubstTheory.subst_consts_expr_ind >>
  rw[constSubstTheory.subst_consts_expr_def,
     constSubstTheory.fold_const_expr_def, fold_const_builtin_code_accessor,
     supported_expr_exists_def] >> metis_tac[]
QED

Theorem supported_pure_no_code_accessor[local]:
  (!tops e. supported_pure_expr tops e ==>
    ~supported_expr_exists (\x. ?t es. x = Builtin t (Acc Code) es) e) /\
  (!tops es. supported_pure_exprs tops es ==>
    ~supported_exprs_exists (\x. ?t xs. x = Builtin t (Acc Code) xs) es) /\
  (!tops fs. supported_pure_fields tops fs ==>
    ~supported_fields_exists (\x. ?t es. x = Builtin t (Acc Code) es) fs) /\
  (!tops e. supported_place_expr tops e ==>
    ~supported_expr_exists (\x. ?t es. x = Builtin t (Acc Code) es) e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rw[supported_pure_expr_def, supported_expr_exists_def] >>
  Cases_on `es` >>
  gvs[supported_builtin_form_def, supported_expr_exists_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> Cases_on `t` >> fs[]
QED

Theorem supported_pure_expr_no_self_code:
  supported_pure_expr tops e ==> ~supported_expr_exists is_self_code e
Proof
  strip_tac >>
  drule_then assume_tac (cj 1 supported_pure_no_code_accessor) >>
  `!x. is_self_code x ==> ?t es. x = Builtin t (Acc Code) es` by
    (recInduct is_self_code_ind >> simp[is_self_code_def]) >>
  spose_not_then assume_tac >>
  qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
  simp[] >>
  irule (BETA_RULE (Q.SPECL [`is_self_code`, `e`,
    `\x. ?t es. x = Builtin t (Acc Code) es`] (cj 1 supported_expr_exists_mono))) >>
  simp[]
QED

Theorem folded_const_no_self_code[local]:
  supported_pure_expr tops (fold_const_expr (subst_consts_expr env e)) ==>
  ~supported_expr_exists is_self_code e
Proof
  strip_tac >>
  `!x. is_self_code x ==> ?t es. x = Builtin t (Acc Code) es` by
    (recInduct is_self_code_ind >> simp[is_self_code_def]) >>
  spose_not_then assume_tac >>
  `supported_expr_exists (\x. ?t es. x = Builtin t (Acc Code) es) e` by
    (irule (BETA_RULE (Q.SPECL [`is_self_code`, `e`,
      `\x. ?t es. x = Builtin t (Acc Code) es`] (cj 1 supported_expr_exists_mono))) >>
     simp[]) >>
  drule_then assume_tac (cj 1 supported_pure_no_code_accessor) >>
  metis_tac[Q.SPECL [`env`, `e`] (cj 1 folded_subst_code_accessor)]
QED

Theorem deploy_evaluation_context_code_update[local]:
  deploy_evaluation_context tops am (tx with code := c) =
  (deploy_evaluation_context tops am tx) with txn :=
    (deploy_evaluation_context tops am tx).txn with code := c
Proof
  simp[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_eval_no_self_code_update[local]:
  ~program_reads_self_code tops ==>
  (!ds. ~supported_exprs_exists is_self_code ds ==>
    eval_exprs (deploy_evaluation_context tops am (tx with code := c)) ds =
    eval_exprs (deploy_evaluation_context tops am tx) ds) /\
  (!ss. ~supported_stmts_expr_exists is_self_code ss ==>
    eval_stmts (deploy_evaluation_context tops am (tx with code := c)) ss =
    eval_stmts (deploy_evaluation_context tops am tx) ss)
Proof
  strip_tac >> rewrite_tac[deploy_evaluation_context_code_update] >>
  MATCH_MP_TAC (GEN_ALL evaluate_no_self_code_update) >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       get_module_code_def, alistTheory.ALOOKUP_def,
       lookup_callable_function_def, AllCaseEqs()] >>
  metis_tac[lookup_function_no_self_code]
QED

Theorem deploy_const_eval_code_update[local]:
  ~program_reads_self_code tops /\ ~supported_expr_exists is_self_code e ==>
  bind
    (eval_expr
      (set_current_module (deploy_evaluation_context tops am (tx with code := c)) NONE) e)
    (read_result
      (set_current_module (deploy_evaluation_context tops am (tx with code := c)) NONE)) st =
  bind (eval_expr (set_current_module (deploy_evaluation_context tops am tx) NONE) e)
    (read_result (set_current_module (deploy_evaluation_context tops am tx) NONE)) st
Proof
  strip_tac >>
  qabbrev_tac `cx = set_current_module (deploy_evaluation_context tops am tx) NONE` >>
  `set_current_module (deploy_evaluation_context tops am (tx with code := c)) NONE =
   cx with txn := cx.txn with code := c` by
    simp[Abbr `cx`, deploy_evaluation_context_code_update, set_current_module_def] >>
  asm_rewrite_tac[] >>
  `eval_exprs (cx with txn := cx.txn with code := c) [e] = eval_exprs cx [e]` by
    (mp_tac (Q.INST [`cx` |-> `cx`, `c` |-> `c`] evaluate_no_self_code_update) >>
     impl_tac >-
       (simp[Abbr `cx`, set_current_module_def, deploy_evaluation_context_def,
          initial_evaluation_context_def, get_module_code_def, alistTheory.ALOOKUP_def,
          lookup_callable_function_def, AllCaseEqs()] >>
        metis_tac[lookup_function_no_self_code]) >>
     disch_then (qspec_then `[e]` mp_tac o cj 1) >>
     simp[supported_expr_exists_def]) >>
  pop_assum (fn th => mp_tac (Q.AP_THM th `st`)) >>
  simp[abi_args_singleton_source] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
  Cases_on `bind (eval_expr (cx with txn := cx.txn with code := c) e)
    (read_result (cx with txn := cx.txn with code := c)) st` >>
  simp[bind_def, return_def] >>
  Cases_on `q` >> Cases_on `q'` >> simp[return_def]
QED

Theorem constants_env_trace_code_update[local]:
  !decls env acc.
    ~program_reads_self_code tops /\
    EVERY (supported_pure_expr tops o SND) (module_consts_env decls env) ==>
    constants_env_trace
      (set_current_module (deploy_evaluation_context tops am (tx with code := c)) NONE)
      installed tx.target NONE decls acc =
    constants_env_trace
      (set_current_module (deploy_evaluation_context tops am tx) NONE)
      installed tx.target NONE decls acc
Proof
  recInduct module_consts_env_ind >>
  simp[module_consts_env_def, constants_env_trace_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[]
  >~ [`constants_env_trace _ _ _ _ decls`]
  >- (qmatch_asmsub_rename_tac
        `module_consts_env decls (env ++ [(id,fold_const_expr (subst_consts_expr env e))])` >>
      `supported_pure_expr tops (fold_const_expr (subst_consts_expr env e))` by
        (qspec_then `decls`
          (qspec_then `env ++ [(id,fold_const_expr (subst_consts_expr env e))]`
            strip_assume_tac) module_consts_env_acc_prefix >>
         gvs[EVERY_APPEND]) >>
      drule folded_const_no_self_code >> strip_tac >>
      imp_res_tac deploy_const_eval_code_update >>
      gvs[deploy_evaluation_context_code_update, set_current_module_def,
          get_tenv_def, LET_THM, SF ETA_ss] >>
      rpt CASE_TAC >> gvs[])
  >> metis_tac[]
QED

Theorem deploy_function_trace_code_update[local]:
  supported_program tops /\ ~program_reads_self_code tops /\
  lookup_function NONE tx.function_name Deploy tops =
    SOME (mut,nr,args,ds,ret,ss) ==>
  call_external_function_trace orc gs installed
    (deploy_evaluation_context tops am (tx with code := c))
      nr mut tops [(NONE,tops)] args ds tx.args ss ret =
  call_external_function_trace orc gs installed
    (deploy_evaluation_context tops am tx)
      nr mut tops [(NONE,tops)] args ds tx.args ss ret
Proof
  strip_tac >>
  drule_all_then strip_assume_tac lookup_function_no_self_code >>
  mp_tac (Q.INST [`am` |-> `am`, `tx` |-> `tx`, `c` |-> `c`]
    deploy_eval_no_self_code_update) >>
  disch_then (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
  `!n. eval_external_defaults
         (deploy_evaluation_context tops am (tx with code := c)) (DROP n ds) =
       eval_external_defaults (deploy_evaluation_context tops am tx) (DROP n ds)` by
    (gen_tac >>
     qpat_x_assum `!es. _ ==> eval_exprs _ es = _`
       (qspec_then `DROP n ds` mp_tac) >>
     simp[no_self_code_operands] >> strip_tac >>
     asm_rewrite_tac[FUN_EQ_THM, eval_external_defaults_run]) >>
  `eval_stmts (deploy_evaluation_context tops am (tx with code := c)) ss =
   eval_stmts (deploy_evaluation_context tops am tx) ss` by
    (first_x_assum irule >> simp[]) >>
  `EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])` by
    fs[supported_program_def] >>
  `evaluate_module_constants_trace
      (deploy_evaluation_context tops am (tx with code := c)) installed tx.target [(NONE,tops)] =
    evaluate_module_constants_trace
      (deploy_evaluation_context tops am tx) installed tx.target [(NONE,tops)]` by
    (mp_tac (Q.SPECL [`tops`, `[]`, `FEMPTY`] constants_env_trace_code_update) >>
     impl_tac >- simp[] >>
     simp[evaluate_module_constants_trace_def, LET_THM]) >>
  gvs[call_external_function_trace_def, LET_THM, constants_order_def,
      send_call_value_def, deploy_evaluation_context_code_update,
      deploy_evaluation_context_def, initial_evaluation_context_def,
      vyperStateTheory.check_not_static_def]
QED

Theorem load_contract_trace_code_update:
  supported_program tops /\ ~program_reads_self_code tops ==>
  load_contract_trace orc gs am (tx with code := c) [(NONE,tops)] [] =
  load_contract_trace orc gs am tx [(NONE,tops)] []
Proof
  strip_tac >>
  simp[load_contract_trace_def, LET_THM, alistTheory.ALOOKUP_def,
       GSYM deploy_evaluation_context_def] >>
  Cases_on `initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)]` >>
  simp[] >>
  Cases_on `lookup_function NONE tx.function_name Deploy tops` >> simp[] >>
  rename1 `lookup_function NONE tx.function_name Deploy tops = SOME entry` >>
  PairCases_on `entry` >> simp[] >>
  gvs[deploy_function_trace_code_update]
QED

Theorem deploy_storage_checks_code_update[local]:
  (storage_well_formed_on (deploy_evaluation_context tops am (tx with code := c))
     st regions /\
   storage_trace_backends_well_formed
     (deploy_evaluation_context tops am (tx with code := c)) regions obs) <=>
  (storage_well_formed_on (deploy_evaluation_context tops am tx) st regions /\
   storage_trace_backends_well_formed
     (deploy_evaluation_context tops am tx) regions obs)
Proof
  `!st. storage_well_formed_on
          (deploy_evaluation_context tops am (tx with code := c)) st regions <=>
        storage_well_formed_on (deploy_evaluation_context tops am tx) st regions` by
    (gen_tac >> irule storage_well_formed_on_target >>
     simp[deploy_evaluation_context_code_update]) >>
  gvs[storage_trace_backends_well_formed_def, listTheory.EVERY_MEM] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >> simp[]
QED

Theorem deploy_storage_ok_code_update:
  supported_program tops /\ ~program_reads_self_code tops ==>
  (deploy_storage_ok tops am (tx with code := c) os gs <=>
   deploy_storage_ok tops am tx os gs)
Proof
  strip_tac >>
  `deploy_storage_trace (SOME os) gs am (tx with code := c) tops =
   deploy_storage_trace (SOME os) gs am tx tops` by
    simp[deploy_storage_trace_def, load_contract_trace_code_update] >>
  Cases_on `storage_trace_horizon (deploy_storage_trace (SOME os) gs am tx tops)` >>
  simp[deploy_storage_ok_def, deploy_storage_checks_code_update]
QED

Theorem deploy_call_result_rel_code_update:
  supported_program tops /\ ~program_reads_self_code tops ==>
  (deploy_call_result_rel tops runtime_bc am (tx with code := c) es r es' <=>
   deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  strip_tac >>
  simp[deploy_call_result_rel_def, deploy_storage_trace_def,
       load_contract_def, load_contract_trace_code_update, deploy_storage_ok_code_update,
       deploy_result_rel_def]
QED

(* The source-side hypotheses of e2e_deploy_correctness that hold at every
   gas filling; the finite storage guard deploy_storage_ok depends on the
   filling, so the unit theorem states it per filling. *)
Definition deploy_source_ok_def:
  deploy_source_ok tops am tx <=>
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx
End

(* The deployment's dead bytes, fixed before the run (so independent of its
   gas readings): the target's dead storage and transient storage bytes in
   the context load_contract runs the constructor in, as external_call_dead,
   and the dead bytes of the immutables section the run returns after the
   runtime code.  vs_immutables are not observed, so all of them are dead. *)
Definition deploy_dead_def:
  deploy_dead H tops runtime_bc am tx =
    <| d_stor := (\a st. if a = tx.target
                         then {(k,b) | storage_dead H F st (w2n k) b}
                         else {});
       d_trans := (\a st. if a = tx.target
                          then {(k,b) | storage_dead H T st (w2n k) b}
                          else {});
       d_imm := K UNIV;
       d_ret := (\r. {i | LENGTH runtime_bc <= i /\
                         imm_section_dead tops (DROP (LENGTH runtime_bc) r)
                           (i - LENGTH runtime_bc)}) |>
End

Definition deploy_source_exempt_def:
  deploy_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    case src of
      INR (Error e) => unspecified_behaviour_exempt tops e
    | _ => F
End

(* A successful constructor halts returning the runtime code followed by its
   immutables section, with the source's accounts (the target modulo code,
   its storage modulo storage_dead), transient storage (modulo storage_dead)
   and logs. Failures abort; a source Error may also halt
   only when it is exempt. *)
Definition deploy_venom_result_rel_def:
  deploy_venom_result_rel H tops runtime_bc tx
    (src : (abstract_machine # call_request list) + exception) vres <=>
    case (src, vres) of
      (INL (am', rqs), Halt ss) =>
        let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
        if ALOOKUP am'.sources tx.target = NONE then
          (* The constructor halted (selfdestruct): no source installed, the
           * unit halts with empty returndata, and the target is queued for
           * deletion on both sides. *)
          ss.vs_returndata = [] /\
          MEM tx.target ss.vs_pending_deletions /\
          accounts_agree H cx.txn.target am'.accounts
            (process_deletions ss.vs_pending_deletions ss.vs_accounts) /\
          transient_agree H cx.txn.target am'.tStorage ss.vs_transient /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs ss.vs_logs /\
          LIST_REL (request_agree H cx.txn.target) rqs ss.vs_requests
        else
        ?section.
          ss.vs_returndata = runtime_bc ++ section /\
          immutables_section_rel tops (account_immutables am' tx.target) section /\
          accounts_agree H cx.txn.target am'.accounts
            (process_deletions ss.vs_pending_deletions
               (update_account tx.target
                  (lookup_account tx.target ss.vs_accounts with
                     code := (lookup_account tx.target am'.accounts).code)
                  ss.vs_accounts)) /\
          transient_agree H cx.txn.target am'.tStorage ss.vs_transient /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs ss.vs_logs /\
          LIST_REL (request_agree H cx.txn.target) rqs ss.vs_requests
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error e), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End

Theorem deploy_venom_result_rel_terminates:
  deploy_venom_result_rel H tops runtime_bc tx src res ==> terminates res
Proof
  Cases_on `res` >> simp[terminates_def] >>
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> simp[deploy_venom_result_rel_def])
  >> rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_venom_result_rel_def]
QED
