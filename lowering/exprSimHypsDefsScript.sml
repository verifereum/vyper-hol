(* Expression preconditions and induction judgments, before their proofs. *)
Theory exprSimHypsDefs
Ancestors
  exprSimStack exprSimDefs gasContext list finite_map pair exprCallBounds exprBopLowering
  exprLowering compileEnv vyperAST vyperInterpreter vyperState vyperTypeSystem
  vyperTypeCallGraph vyperTypeInvariants vyperRuntimeAccounts vyperPlaceInvariants
  vyperStorageLayoutSafety vyperTypeStoragePreservation supportedExprTraverse
  supportedProgram placeTypingProps allocLimits selectorDispatch

Definition outcomes_accounts_typed_def:
  outcomes_accounts_typed (oos : call_outcome list option) <=>
    !os. oos = SOME os ==>
         EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
                     (oc.co_success ==>
                      accounts_runtime_well_typed oc.co_accounts)) os
End

Definition popped_keys_indexed_def:
  popped_keys_indexed (scs : scope list) <=>
    EVERY (\sc. !id entry. FLOOKUP sc id = SOME entry ==>
                 popped_history_typed entry.type entry.popped /\
                 EVERY (\k. ?p i etv n.
                             k = p ++ [ValueSubscript i] /\
                             subscripts_type entry.type p =
                               SOME (ArrayTV etv (Dynamic n)))
                       (MAP FST entry.popped)) scs
End

(* An assignable immutable exists only in the constructor, lowered
   with the constructor's compile env; every immutable has its
   declared type in ce_module_var_type, where compile_get_target_ptr
   reads a place type; and distinct immutables' regions are disjoint,
   as the section layout places them. *)
Definition bare_globals_layout_def:
  bare_globals_layout cenv cx (env:typing_env) <=>
    (!src id ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
       (cenv.ce_is_ctor <=> cx.in_deploy)) /\
    (!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
       cenv.ce_module_var_type (src,id) = SOME ty) /\
    (!src id1 id2 ty1 ty2 off1 off2 tv1 tv2.
       id1 <> id2 /\
       FLOOKUP env.bare_globals (src,id1) = SOME ty1 /\
       FLOOKUP env.bare_globals (src,id2) = SOME ty2 /\
       FLOOKUP cenv.ce_module_vars (src,id1) = SOME (ImmutableLoc off1) /\
       FLOOKUP cenv.ce_module_vars (src,id2) = SOME (ImmutableLoc off2) /\
       evaluate_type (get_tenv cx) ty1 = SOME tv1 /\
       evaluate_type (get_tenv cx) ty2 = SOME tv2 ==>
       compileEnv$regions_disjoint off1 (type_memory_size tv1)
         off2 (type_memory_size tv2))
End

Definition expr_sim_inv_def:
  expr_sim_inv cenv cx env (es:evaluation_state) <=>
    env_consistent env cx es /\ state_well_typed es /\
    accounts_well_typed es.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             cenv.ce_var_type id = SOME ty) /\
    (!src fid ts ls mid i.
       get_module_code cx src = SOME ts /\ lookup_flag fid ts = SOME ls /\
       INDEX_OF mid ls = SOME i ==>
       cenv.ce_flag_member_id (nsid_to_string (src, fid)) mid = i) /\
    (!nsid m. FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
    (* The compile environment's method id of an external function is the
       selector of its signature, the four bytes the source sends first
       (build_ext_calldata); build_compile_env fills ce_method_id with
       exactly that, over its type environment. *)
    (!fname tys.
       cenv.ce_method_id fname tys =
       w2n (calldata_method_id
              (function_selector fname (vyper_to_abi_types (get_tenv cx) tys)))) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
                                     sz = type_memory_size tv) fields) /\
    outcomes_accounts_typed es.outcomes /\
    IS_SOME es.outcomes /\
    contract_storage_well_formed cx es /\ storage_layout_safe cx /\
    oracle_storage_ok cx es /\
    (* A storage or transient variable has its declared type in
       ce_module_var_type, where the lowering reads a pop's element type,
       and is not a mapping (build_var_type_map, build_hashmap_info). *)
    (!src id ts tr typ id_str.
       get_module_code cx src = SOME ts /\
       find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) ==>
       cenv.ce_hashmap_info (src,id) = NONE /\
       cenv.ce_module_var_type (src,id) = SOME typ) /\
    popped_keys_indexed es.scopes /\
    place_map_tables_agree_on_defined cenv env /\
    (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==>
               cenv.ce_hashmap_info nsid = NONE) /\
    (!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
       src = cenv.ce_module /\
       ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
             !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                  off + type_memory_size tv < dimword (:256)) /\
    bare_globals_layout cenv cx env
End

Definition word_value_type_def:
  word_value_type t <=> is_numeric_type t \/ is_bool_type t \/ is_flag_type t
End

Definition byte_widths_expr_def:
  byte_widths_expr (Name t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (TopLevelName t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (FlagMember t _ _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (IfExp t c x y) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr c /\ byte_widths_expr x /\
     byte_widths_expr y) /\
  byte_widths_expr (Literal t _) = (type_bits t MOD 8 = 0) /\
  byte_widths_expr (StructLit t _ kes) =
    (type_bits t MOD 8 = 0 /\ byte_widths_named_exprs kes) /\
  byte_widths_expr (Subscript t x y) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr x /\ byte_widths_expr y) /\
  byte_widths_expr (Attribute t x _) =
    (type_bits t MOD 8 = 0 /\ byte_widths_expr x) /\
  byte_widths_expr (Builtin t _ es) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es) /\
  byte_widths_expr (TypeBuiltin t _ _ es) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es) /\
  byte_widths_expr (Pop t tgt) =
    (type_bits t MOD 8 = 0 /\ byte_widths_target tgt) /\
  byte_widths_expr (Call t _ es dflt) =
    (type_bits t MOD 8 = 0 /\ byte_widths_exprs es /\ byte_widths_opt dflt) /\

  byte_widths_target (NameTarget _) = T /\
  byte_widths_target (TopLevelNameTarget _) = T /\
  byte_widths_target (SubscriptTarget tgt e) =
    (byte_widths_target tgt /\ byte_widths_expr e) /\
  byte_widths_target (AttributeTarget tgt _) = byte_widths_target tgt /\

  byte_widths_exprs [] = T /\
  byte_widths_exprs (e::es) = (byte_widths_expr e /\ byte_widths_exprs es) /\

  byte_widths_opt NONE = T /\
  byte_widths_opt (SOME e) = byte_widths_expr e /\

  byte_widths_named_exprs [] = T /\
  byte_widths_named_exprs ((_,e)::kes) =
    (byte_widths_expr e /\ byte_widths_named_exprs kes)
Termination
  (* the measure names the container sizes with `list_size`/`option_size` over
     `expr_size`, as in `vyperTypeCallGraph`, so that the obligations are
     arithmetic over one set of size functions. *)
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
                                      expr option + (identifier # expr) list).
    case x of
    | INL e => expr_size e
    | INR (INL tgt) => base_assignment_target_size tgt
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR kes))) =>
        list_size (pair_size (list_size char_size) expr_size) kes)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def] >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def,
       bnfPrelimsTheory.option_size_map, bnfPrelimsTheory.pair_size_map,
       listTheory.list_size_map, SF ETA_ss]
End

Definition expr_sim_pre_def:
  expr_sim_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e /\
    ~supported_expr_exists call_operands_effect_root e /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
End

Definition expr_body_pre_def:
  expr_body_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    call_evaluation_safe cx (int_calls_expr e) /\ ~expr_has_evm_run e /\
    ~supported_expr_exists call_operands_effect_root e /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops /\
                      IS_SOME (supported_function_decl tops c Internal))
          (int_calls_expr e) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
End

Definition expr_sim_ok_def:
  expr_sim_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
End

Definition expr_vv_ok_def:
  expr_vv_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_vv_sim ctx func cenv cx ty e es
End

Definition expr_ok_def:
  expr_ok cenv e <=> expr_sim_ok cenv e /\ expr_vv_ok cenv e
End

Definition expr_sim_below_def:
  expr_sim_below cenv n <=> !e. expr_size e < n ==> expr_ok cenv e
End

Definition expr_sim_case_def:
  expr_sim_case nocalls ctx func cenv cx e <=>
    !env ty es.
      expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
      expr_sim ctx func cenv cx ty e es
End

Definition expr_vv_case_def:
  expr_vv_case nocalls ctx func cenv cx e <=>
    !env ty es.
      expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
      expr_vv_sim ctx func cenv cx ty e es
End

Definition exprs_case_def:
  exprs_case nocalls ctx func cenv cx [] = T /\
  exprs_case nocalls ctx func cenv cx (e::es) =
    (expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      exprs_case nocalls ctx func cenv cx es))
End

(* The positional operands of an external call, evaluated in order and
   read only after the keyword operands (eval_expr_results): each one's
   judgments if the ones before it evaluate (bodySim's body_results_ok). *)
Definition results_case_def:
  results_case nocalls ctx func cenv cx [] = T /\
  results_case nocalls ctx func cenv cx (e::es) =
    (expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e /\
     ((?s r t. eval_expr cx e s = (INL r, t)) ==>
      results_case nocalls ctx func cenv cx es))
End

Definition names_builtin_def:
  (names_builtin AddMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin MulMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin PowMod256 [Name _ _; Name _ _] <=> T) /\
  (names_builtin _ _ <=> F)
End

Definition builtin_sim_ok_def:
  builtin_sim_ok cenv ann bi args <=>
    ~names_builtin bi args ==> expr_ok cenv (Builtin ann bi args)
End

Definition type_builtin_sim_ok_def:
  type_builtin_sim_ok cenv ann tb t args <=>
    expr_ok cenv (TypeBuiltin ann tb t args)
End


Theorem expr_sim_inv_gas_obs[simp]:
  expr_sim_inv cenv cx env (es with gas_obs := gs) <=>
  expr_sim_inv cenv cx env es
Proof
  `oracle_storage_ok cx (es with gas_obs := gs) <=>
   oracle_storage_ok cx es` by
    (irule oracle_storage_ok_outcomes >> simp[]) >>
  `contract_storage_well_formed cx (es with gas_obs := gs) <=>
   contract_storage_well_formed cx es` by
    (eq_tac >> strip_tac >>
     irule contract_storage_well_formed_storage_frame >>
     goal_assum (drule_at Any) >> Cases >>
     simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[expr_sim_inv_def]
QED

(* Stack-valued forms lift the counted value simulation to both judgments. *)
Theorem expr_ok_stack:
  !cenv e.
    expr_sim_ok cenv e /\
    (!ty sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!cx es tv es'. eval_expr cx e es = (INL tv, es') ==> ?v. tv = Value v) ==>
    expr_ok cenv e
Proof
  rw[expr_ok_def, expr_vv_ok_def] >> irule expr_vv_sim_stack >>
  gvs[expr_sim_ok_def] >> metis_tac[]
QED

Theorem compile_expr_body_builtin_dispatch:
  !f g h cenv ty ann bt args st.
    ~names_builtin bt args ==>
    compile_expr_body f g h cenv ty (Builtin ann bt args) st =
    g cenv ann ty bt args st
Proof
  rpt gen_tac >>
  Cases_on `args` >> simp[compile_expr_body_def, names_builtin_def,
                             vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (a::rest)` >>
  Cases_on `a` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, names_builtin_def,
                          vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (_::b::rest)` >>
  Cases_on `b` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest`
  >- (Cases_on `bt` >> simp[compile_expr_body_def, names_builtin_def,
                            vyperASTTheory.expr_type_def]) >>
  simp[compile_expr_body_def, names_builtin_def,
       vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (_::_::c::rest)` >>
  Cases_on `c` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, names_builtin_def,
                          vyperASTTheory.expr_type_def] >>
  Cases_on `bt` >> simp[compile_expr_body_def, names_builtin_def,
                        vyperASTTheory.expr_type_def]
QED

Theorem compile_expr_builtin_dispatch:
  !cenv ty ann bt args st.
    ~names_builtin bt args ==>
    compile_expr cenv ty (Builtin ann bt args) st =
    compile_builtin_dispatch cenv ann ty bt args st
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def),
       compile_expr_body_builtin_dispatch, vyperASTTheory.expr_size_def,
       list_size_def, basicSizeTheory.option_size_def]
QED
