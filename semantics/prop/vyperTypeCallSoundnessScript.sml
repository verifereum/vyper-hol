(*
 * Call-entry and internal-call soundness lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeCallSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeBuiltins vyperTypeExprSoundness
  vyperSourceSupplyDefs vyperTypeEvalSoundness vyperTypeStatePreservation
Libs
  wordsLib

(* ===== Parameter/default alignment ===== *)

Theorem fn_sig_argument_bounds:
  FLOOKUP env.fn_sigs (src, fn) = SOME sig /\
  well_typed_expr env (Call ty (IntCall (src,fn)) args drv) ==>
  LENGTH args <= LENGTH sig.param_types /\
  LENGTH sig.param_types - sig.num_defaults <= LENGTH args /\
  MAP expr_type args = TAKE (LENGTH args) sig.param_types /\
  type_widens_to env.type_defs sig.ret_ty ty
Proof
  rw[well_typed_expr_def] >> gvs[]
QED

Theorem defaults_env_erases_locals:
  (defaults_env env).var_types = FEMPTY /\ (defaults_env env).var_assignable = FEMPTY /\
  (defaults_env env).current_src = env.current_src /\
  (defaults_env env).type_defs = env.type_defs /\
  (defaults_env env).fn_sigs = env.fn_sigs /\
  (defaults_env env).bare_globals = env.bare_globals /\
  (defaults_env env).bare_global_assignable = env.bare_global_assignable /\
  (defaults_env env).toplevel_vtypes = env.toplevel_vtypes /\
  (defaults_env env).flag_members = env.flag_members
Proof
  simp[defaults_env_def]
QED

Theorem functions_well_typed_body:
  functions_well_typed cx /\ fn_sigs_consistent fn_sigs cx /\
  fn_sigs_declared_complete fn_sigs cx /\
  toplevel_vtypes_complete toplevel_vtypes cx /\
  bare_globals_complete bare_globals cx /\
  bare_global_assignable_complete bare_global_assignable cx /\
  flag_members_complete flag_members cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,fn_body) /\
  (* Concrete maps supplied by caller must satisfy the consistency side-condition. *)
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?ts. get_module_code cx src = SOME ts /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\ find_var_decl_by_name id ts = NONE /\
          ty <> NoneT) /\
  (!src id ty. FLOOKUP bare_global_assignable (src,id) = SOME ty ==>
     ?ts. get_module_code cx src = SOME ts /\
          FLOOKUP bare_globals (src,id) = SOME ty /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_immutable_decl id ts /\ find_var_decl_by_name id ts = NONE /\
          ty <> NoneT) /\
  (!src id vt ts.
     FLOOKUP toplevel_vtypes (src,id) = SOME vt /\ get_module_code cx src = SOME ts ==>
     ((?ty. vt = Type ty /\
         ((!is_transient typ id_str.
             find_var_decl_by_name id ts = SOME (StorageVarDecl is_transient typ,id_str) ==> typ = ty) /\
          (!is_transient kt hv id_str.
             find_var_decl_by_name id ts = SOME (HashMapVarDecl is_transient kt hv,id_str) ==> F) /\
          (find_var_decl_by_name id ts = NONE ==> IS_SOME (evaluate_type (get_tenv cx) ty)))) \/
      (?kt hv. vt = HashMapT kt hv /\
         ?is_transient id_str.
           find_var_decl_by_name id ts = SOME (HashMapVarDecl is_transient kt hv,id_str)))) /\
  (!src fid ls.
     FLOOKUP flag_members (src,fid) = SOME ls ==>
     ?ts. get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
          FLOOKUP (get_tenv cx) ((src,fid)) = SOME (FlagArgs (LENGTH ls))) ==>
  ?env_body ret_tv env_after.
    env_body.current_src = src /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = bare_globals /\
    env_body.bare_global_assignable = bare_global_assignable /\
    env_body.toplevel_vtypes = toplevel_vtypes /\
    env_body.flag_members = flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types id = SOME typ /\
       FLOOKUP env_body.var_assignable id = SOME T)
Proof
  rw[functions_well_typed_def] >> first_x_assum drule_all >>
  rw[] >> qexists_tac`env_body` >> gvs[] >> rw[] >>
  first_x_assum drule >> rw[]
QED

(* ===== Call soundness theorem shapes ===== *)

Theorem typed_expr_evaluation_sound:
  well_typed_expr env e /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv (Type (expr_type e))
   | INR _ => T)
Proof
  strip_tac >>
  qspecl_then [`cx`,`e`] strip_assume_tac (cj 5 eval_scc_type_sound_mutual) >>
  qpat_x_assum `!env st res st'. _ ==> (_ /\ _)` drule_all >>
  simp[]
QED

Theorem internal_call_no_type_error:
  well_typed_expr env (Call ty (IntCall (src,fn)) args drv) /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr (Call ty (IntCall (src,fn)) args drv)) ==>
  no_type_error_eval (eval_expr cx (Call ty (IntCall (src,fn)) args drv) st)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Call ty (IntCall (src,fn)) args drv) st` >>
  simp[no_type_error_eval_def, no_type_error_result_def] >>
  drule_all typed_expr_evaluation_sound >>
  simp[no_type_error_result_def]
QED

Theorem internal_call_success_value[local]:
  eval_expr cx (Call ty (IntCall (src,fn)) args drv) st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem internal_call_type_preservation:
  well_typed_expr env (Call ty (IntCall (src,fn)) args drv) /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr (Call ty (IntCall (src,fn)) args drv)) /\
  eval_expr cx (Call ty (IntCall (src,fn)) args drv) st = (INL tvl, st') ==>
  state_well_typed st' /\ expr_runtime_typed env (Call ty (IntCall (src,fn)) args drv) tvl
Proof
  strip_tac >>
  drule_all typed_expr_evaluation_sound >> strip_tac >> gvs[] >>
  drule internal_call_success_value >> strip_tac >>
  gvs[eval_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def]
QED

Theorem external_call_no_type_error:
  well_typed_expr env (Call ty (ExtCall stat skip_check fsig opts) args drv) /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr (Call ty (ExtCall stat skip_check fsig opts) args drv)) ==>
  no_type_error_eval (eval_expr cx (Call ty (ExtCall stat skip_check fsig opts) args drv) st)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Call ty (ExtCall stat skip_check fsig opts) args drv) st` >>
  simp[no_type_error_eval_def, no_type_error_result_def] >>
  drule_all typed_expr_evaluation_sound >>
  simp[no_type_error_result_def]
QED

Theorem special_call_no_type_error:
  well_typed_expr env (Call ty target args drv) /\
  target <> IntCall (src,fn) /\ (!stat skip_check fsig opts. target <> ExtCall stat skip_check fsig opts) /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ source_supply st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr (Call ty target args drv)) ==>
  no_type_error_eval (eval_expr cx (Call ty target args drv) st)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Call ty target args drv) st` >>
  simp[no_type_error_eval_def, no_type_error_result_def] >>
  drule_all typed_expr_evaluation_sound >>
  simp[no_type_error_result_def]
QED
