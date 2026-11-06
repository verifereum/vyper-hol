(* Whitelist removal: clauses of supported_program that the contract checker
   already discharges.  Each row lemma takes a checker fact (check_contract on
   the single main module, or the type_stmt / well_typed_expr judgement a
   checked body gives) and concludes the whitelist clause, or its
   checker-side shape where the clause reads the lowering's own tables.
   TOP-LEVEL (row lemmas):
     check_contract_supported_struct_fields          (E9)
     well_typed_ext_call_opts_distinct               (E114)
     well_typed_static_call_no_value                 (E115)
     well_typed_ext_call_operand_count               (E116)
     well_typed_ext_call_no_default                  (E118)
     well_typed_send_shape                           (E119)
     well_typed_call_default_int_call                (E133)
     check_contract_event_indexed_indexable          (S15)
     check_contract_function_names_same_vis_distinct (S20)
     check_contract_event_names_distinct             (S21)
     check_contract_fallback_no_arguments            (S22)
     check_contract_function_header_bindings         (S23)
     check_contract_selectors_distinct               (S24)
     check_contract_body_bindings_not_args           (S26)
     type_stmt_assign_base_target_value              (S35)
     check_contract_log_event_fields                 (S48)
     type_stmt_augassign_word_target                 (S49)
     type_stmt_augassign_supported_binop             (S50)
     type_stmt_for_range_integer_type                (S56)
     type_stmt_for_range_bound_pos                   (S60)
     type_stmt_for_array_name_elem                   (S62)
     type_place_target_attribute_subscript_base      (S69) *)
Theory whitelistCheckerDecls
Ancestors
  list rich_list arithmetic finite_map pred_set pair option words
  vyperAST vyperValue vyperContext vyperInterpreter vyperTypeSystem
  vyperTypeContract vyperABIEntries
  vyperTypeContractStaticMaps vyperTypeContractContext vyperTypeEnvExtension
  vyperTypeEventLookup
  supportedTypes supportedDecls supportedNames supportedExprForms
  supportedStmtTraverse compileVyper selectorDispatch contractABI
  entryDispatchProps

(* ===== The single-module namespace facts ===== *)

Theorem check_contract_single_namespaces[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel F (NONE:num option)) tops)) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  ALL_DISTINCT (FLAT (MAP (event_keys_toplevel (NONE:num option)) tops)) /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  ALL_DISTINCT (abi_external_method_ids (type_env tops) tops)
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  rw[]
QED

Theorem check_contract_single_decl[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\ MEM tl tops ==>
  check_toplevel_decl [(NONE, tops)] art NONE tl
Proof
  strip_tac >> irule check_contract_toplevel_decl_MEM >> simp[] >>
  metis_tac[]
QED

Theorem check_contract_single_body[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  check_function_body layouts addr [(NONE, tops)] art NONE vis mut nr args
    dflts ret fbody
Proof
  strip_tac >> drule check_contract_main_module_allocated >> simp[] >>
  strip_tac >> drule check_contract_runtime_function_body_MEM >> simp[] >>
  disch_then drule_all >> simp[]
QED

(* ===== E9: no interface or flag blocks a declared struct ===== *)

Theorem supported_struct_fields_type_def_keys:
  !tops name fields.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    MEM (StructDecl name fields) tops ==>
    supported_struct_fields tops (NONE, name) = SOME fields
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[supported_struct_fields_def, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP,
      PULL_EXISTS, type_def_keys_toplevel_def] >>
  Cases_on `h` >> gvs[type_def_keys_toplevel_def] >>
  rw[] >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `StructDecl name fields` mp_tac) >>
  simp[type_def_keys_toplevel_def]
QED

Theorem check_contract_supported_struct_fields:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (StructDecl name fields) tops ==>
  supported_struct_fields tops (NONE, name) = SOME fields
Proof
  strip_tac >> drule check_contract_single_namespaces >> strip_tac >>
  irule supported_struct_fields_type_def_keys >> simp[]
QED

(* ===== E114-E119, E133: call operands ===== *)

Theorem well_typed_ext_call_opts_distinct:
  well_typed_expr env
    (Call ty (ExtCall static_call sk (fname, arg_types, ret) opts) args drv) ==>
  ALL_DISTINCT opts
Proof
  simp[well_typed_expr_def, ext_call_opts_ok_def] >> rpt strip_tac
QED

Theorem well_typed_static_call_no_value:
  well_typed_expr env
    (Call ty (ExtCall static_call sk (fname, arg_types, ret) opts) args drv) ==>
  (static_call ==> ~MEM EKValue opts)
Proof
  simp[well_typed_expr_def, ext_call_opts_ok_def] >> rpt strip_tac >> gvs[]
QED

Theorem well_typed_ext_call_operand_count:
  well_typed_expr env
    (Call ty (ExtCall static_call sk (fname, arg_types, ret) opts) args drv) ==>
  LENGTH args = 1 + LENGTH arg_types + LENGTH opts
Proof
  simp[well_typed_expr_def] >> rpt strip_tac
QED

Theorem well_typed_ext_call_no_default:
  well_typed_expr env
    (Call ty (ExtCall static_call sk (fname, arg_types, ret) opts) args drv) ==>
  drv = NONE
Proof
  simp[well_typed_expr_def] >> rpt strip_tac
QED

Theorem well_typed_send_shape:
  well_typed_expr env (Call ty (Send has_gas) args drv) ==>
  ty = NoneT /\ drv = NONE /\
  (if has_gas then ?a v g. args = [a; v; g] else ?a v. args = [a; v])
Proof
  simp[well_typed_expr_def] >> strip_tac >>
  `LENGTH args = if has_gas then 3 else 2` by
    (qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
     rw[]) >>
  Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]
QED

Theorem well_typed_call_default_int_call:
  well_typed_expr env (Call ty target args (SOME d)) ==>
  ?id. target = IntCall id
Proof
  Cases_on `target` >> simp[well_typed_expr_def] >>
  rename1 `ExtCall _ _ sg _` >> PairCases_on `sg` >>
  simp[well_typed_expr_def]
QED

(* ===== S15: indexed event fields ===== *)

Theorem check_contract_event_indexed_indexable:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (EventDecl name fields) tops /\ MEM ((fname, ty), T) fields ==>
  event_indexable_type ty
Proof
  strip_tac >> drule_all check_contract_single_decl >>
  simp[check_toplevel_decl_def, EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* ===== S20, S21: function and event names ===== *)

Theorem function_names_internal_sublist[local]:
  !tops.
    sublist (MAP (\n. (NONE, n))
               (supported_function_names (FILTER (\t. ?m nr rr n a d r b. t = FunctionDecl Internal m nr rr n a d r b) tops)))
            (FLAT (MAP (fn_sig_keys_toplevel F (NONE:num option)) tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  `!f. include_fn_sig F f <=> f = Internal` by (Cases >> simp[include_fn_sig_def]) >>
  rpt strip_tac >> Cases_on `h` >>
  simp[supported_function_names_def, fn_sig_keys_toplevel_def] >>
  rw[supported_function_names_def, GSYM sublist_cons]
QED

Theorem function_names_external_sublist[local]:
  !tops.
    sublist (MAP (\n. (NONE, n))
               (supported_function_names (FILTER (\t. ?m nr rr n a d r b. t = FunctionDecl External m nr rr n a d r b) tops)))
            (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  `!f src m nr rr n a d r b.
     external_name_keys_toplevel (src:num option)
       (FunctionDecl f m nr rr n a d r b) =
     if f = External then [(src,n)] else []`
    by (Cases >> simp[external_name_keys_toplevel_def]) >>
  rpt strip_tac >> Cases_on `h` >>
  TRY (rename1 `VariableDecl vv` >> Cases_on `vv`) >>
  TRY (rename1 `HashMapDecl vv` >> Cases_on `vv`) >>
  simp[supported_function_names_def, external_name_keys_toplevel_def,
       sublist_cons_include] >>
  rw[supported_function_names_def] >>
  gvs[external_name_keys_toplevel_def, GSYM sublist_cons]
QED

Theorem check_contract_function_names_same_vis_distinct:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\ vis <> Deploy ==>
  ALL_DISTINCT (supported_function_names
    (FILTER (\t. ?m nr rr n a d r b. t = FunctionDecl vis m nr rr n a d r b) tops))
Proof
  strip_tac >> drule check_contract_single_namespaces >> strip_tac >>
  irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\x. (NONE, x)` >>
  irule sublist_ALL_DISTINCT >> Cases_on `vis` >> gvs[]
  >- (qexists_tac `FLAT (MAP (external_name_keys_toplevel NONE) tops)` >>
      simp[function_names_external_sublist])
  >- (qexists_tac `FLAT (MAP (fn_sig_keys_toplevel F NONE) tops)` >>
      simp[function_names_internal_sublist])
QED

Theorem event_names_keys[local]:
  !tops. MAP (\n. (NONE, n)) (supported_event_names tops) =
         FLAT (MAP (event_keys_toplevel (NONE:num option)) tops)
Proof
  Induct >> simp[supported_event_names_def] >>
  Cases >> simp[event_keys_toplevel_def]
QED

Theorem check_contract_event_names_distinct:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_event_names tops)
Proof
  strip_tac >> drule check_contract_single_namespaces >> strip_tac >>
  irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\x. (NONE, x)` >>
  simp[event_names_keys]
QED

(* ===== S22, S23: function headers ===== *)

Theorem check_contract_fallback_no_arguments:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl External mut nr rr name args dflts ret fbody) tops ==>
  (name = "__default__" ==> NULL args)
Proof
  strip_tac >> drule_all check_contract_single_decl >>
  simp[check_toplevel_decl_def, function_header_ok_def]
QED

Theorem check_contract_function_header_bindings:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  supported_function_bindings tops args [] []
Proof
  strip_tac >> drule_all check_contract_single_decl >>
  simp[check_toplevel_decl_def, params_ok_def,
       supported_function_bindings_def]
QED

(* ===== S24: the compiler's selector table ===== *)

Theorem calldata_method_id_abi_method_id[local]:
  !bs. LENGTH bs = 4 ==>
       w2n (calldata_method_id bs) = FOLDL (\n b. 256 * n + w2n b) 0 bs
Proof
  rpt strip_tac >> gvs[LENGTH_EQ_NUM_compute] >>
  simp[calldata_method_id_def, w2n_n2w, dimword_def] >>
  `!x:word8. w2n x < 256` by
    (gen_tac >> assume_tac (INST_TYPE [alpha |-> ``:8``] w2n_lt) >> fs[dimword_8]) >>
  qmatch_goalsub_rename_tac
    `16777216 * w2n a + (65536 * w2n b + (256 * w2n c + w2n d))` >>
  `w2n a < 256 /\ w2n b < 256 /\ w2n c < 256 /\ w2n d < 256` by simp[] >>
  `16777216 * w2n a + (65536 * w2n b + (256 * w2n c + w2n d)) <
   115792089237316195423570985008687907853269984665640564039457584007913129639936`
    by simp[] >>
  simp[LESS_MOD]
QED

Theorem compute_selector_abi_method_id[local]:
  FST (compute_selector tenv fname tys) = abi_method_id tenv fname tys
Proof
  simp[compute_selector_def, abi_method_id_def] >>
  irule calldata_method_id_abi_method_id >> simp[function_selector_length]
QED

Theorem classify_function_fst[local]:
  !h acc. FST (classify_function h acc) =
    case h of
      FunctionDecl External mut nr rr fname fargs dflts ret fbody =>
        if fname = "__default__" then FST acc
        else (mut, nr, rr, fname, fargs, dflts, ret, fbody) :: FST acc
    | _ => FST acc
Proof
  rpt gen_tac >> PairCases_on `acc` >> Cases_on `h` >>
  simp[classify_function_def] >>
  BasicProvers.every_case_tac >> rw[]
QED

Theorem build_selectors_sublist[local]:
  !tops. sublist (MAP FST (build_selectors tenv (FST (classify_functions tops))))
                 (abi_external_method_ids tenv tops)
Proof
  Induct >- simp[classify_functions_def, build_selectors_def, sublist_nil] >>
  rpt gen_tac >>
  `abi_external_method_ids tenv (h::tops) =
     MAP (\(name,tys). abi_method_id tenv name tys) (abi_decl_signatures h) ++
     abi_external_method_ids tenv tops`
    by simp[abi_external_method_ids_def, abi_external_signatures_def] >>
  pop_assum SUBST1_TAC >>
  simp[classify_functions_def, classify_function_fst] >>
  fs[GSYM classify_functions_def] >>
  Cases_on `h` >> simp[sublist_append_include] >>
  rename1 `FunctionDecl fv` >> Cases_on `fv` >>
  simp[sublist_append_include, abi_decl_signatures_def] >>
  rw[sublist_append_include, abi_decl_signatures_def, build_selectors_def,
     compute_selector_abi_method_id] >>
  once_rewrite_tac[CONS_APPEND] >> irule sublist_append_pair >> simp[] >>
  irule sublist_member_sing >>
  simp[MEM_MAP, abi_function_signatures_def, PULL_EXISTS, EXISTS_PROD,
       abi_entries_member] >>
  qexists_tac `LENGTH l0` >> simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem check_contract_selectors_distinct:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  supported_selectors_distinct tops
Proof
  strip_tac >> drule check_contract_single_namespaces >> strip_tac >>
  simp[supported_selectors_distinct_def] >>
  irule sublist_ALL_DISTINCT >> metis_tac[build_selectors_sublist]
QED

(* ===== S26: no local or loop variable rebinds an argument ===== *)

Theorem type_stmt_fdom_mono[local]:
  type_stmt env ret s = SOME env' ==>
  FDOM env.var_types SUBSET FDOM env'.var_types
Proof
  rw[SUBSET_DEF] >>
  `FLOOKUP env.var_types x = SOME (env.var_types ' x)` by simp[FLOOKUP_DEF] >>
  drule_all type_stmt_var_types_preserve >> simp[FLOOKUP_DEF]
QED

Theorem type_stmt_bindings_fresh:
  (!env ret s env'.
     type_stmt env ret s = SOME env' ==>
     EVERY (\n. n NOTIN FDOM env.var_types)
       (MAP FST (supported_stmt_bindings T s ++
                 supported_stmt_bindings F s))) /\
  (!env ret ss env'.
     type_stmts env ret ss = SOME env' ==>
     EVERY (\n. n NOTIN FDOM env.var_types)
       (MAP FST (supported_stmts_bindings T ss ++
                 supported_stmts_bindings F ss)))
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >> rpt gen_tac >>
  simp[type_stmt_def, supported_stmt_bindings_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
  gvs[type_stmt_def, AllCaseEqs()] >>
  TRY (qpat_x_assum `type_stmt _ _ _ = SOME _`
         (assume_tac o MATCH_MP type_stmt_fdom_mono)) >>
  gvs[EVERY_MEM, SUBSET_DEF, extend_local_def] >> metis_tac[]
QED

Theorem function_entry_env_var_types_fdom:
  FDOM (function_entry_env art mods src vis args).var_types =
    set (MAP FST args)
Proof
  simp[function_entry_env_def] >>
  `!env. FDOM (FOLDL (\env (id,ty). extend_local env id ty (vis = Internal))
                 env args).var_types =
         FDOM env.var_types UNION set (MAP FST args)`
    suffices_by simp[artifact_env_def] >>
  Induct_on `args` >> simp[] >> Cases >>
  simp[extend_local_def, EXTENSION] >> metis_tac[]
QED

Theorem check_contract_body_bindings_not_args:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody ++ supported_stmts_bindings F fbody))
Proof
  strip_tac >> drule_all check_contract_single_body >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  drule (CONJUNCT2 type_stmt_bindings_fresh) >>
  simp[function_entry_env_var_types_fdom]
QED

(* ===== S35, S49, S50, S69: assignment targets ===== *)

Theorem type_stmt_assign_base_target_value:
  type_stmt env ret (Assign (BaseTarget bt) e) = SOME env' ==>
  ?ty. type_place_target env bt = SOME (Type ty) /\
       type_widens_to env.type_defs (expr_type e) ty
Proof
  simp[type_stmt_def, atarget_accepts_def] >>
  BasicProvers.every_case_tac >> rw[] >> gvs[]
QED

Theorem assignable_int_width[local]:
  (assignable_type tenv (BaseT (UintT n)) ==> supported_int_width n) /\
  (assignable_type tenv (BaseT (IntT n)) ==> supported_int_width n)
Proof
  simp[assignable_type_def, well_formed_type_def, evaluate_type_def,
       supported_int_width_def] >>
  rw[] >> CCONTR_TAC >> gvs[] >>
  `n MOD 8 < 8` by simp[] >> Cases_on `n < 8` >> gvs[]
QED

Theorem type_stmt_augassign_word_target:
  type_stmt env ret (AugAssign ty bt op e) = SOME env' ==>
  type_place_target env bt = SOME (Type ty) /\
  (supported_word_type ty \/ is_flag_type ty)
Proof
  simp[type_stmt_def, well_typed_target_def] >> strip_tac >>
  Cases_on `ty` >> gvs[supported_word_type_def] >>
  TRY (rename1 `BaseT b` >> Cases_on `b`) >> gvs[supported_word_type_def] >>
  imp_res_tac assignable_int_width >> Cases_on `op` >>
  gvs[well_typed_binop_def]
QED

Theorem nonneg_int_literal_supported[local]:
  nonneg_int_literal e ==> supported_nonnegative_literal e
Proof
  Cases_on `e` >> simp[nonneg_int_literal_def, int_literal_value_def,
    supported_nonnegative_literal_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  simp[int_literal_value_def, supported_nonnegative_literal_def]
QED

Theorem type_stmt_augassign_supported_binop:
  type_stmt env ret (AugAssign ty bt op e) = SOME env' /\
  ~is_flag_type ty /\
  (op = ShL \/ op = ShR ==> is_uint_type (expr_type e)) ==>
  supported_binop op ty (expr_type e) F (supported_nonnegative_literal e)
Proof
  simp[type_stmt_def, well_typed_target_def] >> strip_tac >>
  Cases_on `ty` >> gvs[] >>
  TRY (rename1 `BaseT b` >> Cases_on `b`) >> gvs[] >>
  Cases_on `op` >>
  gvs[well_typed_binop_def, supported_binop_def, supported_numeric_type_def,
      supported_integer_type_def, supported_unsigned_type_def,
      supported_word_type_def] >>
  imp_res_tac assignable_int_width >> gvs[supported_int_width_def] >>
  TRY (irule nonneg_int_literal_supported >> simp[])
QED

Theorem type_place_target_attribute_subscript_base:
  (type_place_target env (AttributeTarget b fld) = SOME vt ==>
   ?id. type_place_target env b = SOME (Type (StructT id))) /\
  (type_place_target env (SubscriptTarget b k) = SOME vt ==>
   (?kt vt'. type_place_target env b = SOME (HashMapT kt vt')) \/
   (?elem bd. type_place_target env b = SOME (Type (ArrayT elem bd))))
Proof
  conj_tac >> simp[well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[]
  >- (rename1 `attribute_type _ t0 _ = SOME _` >> Cases_on `t0` >>
      gvs[attribute_type_def]) >>
  rename1 `subscript_vtype vt0 _ = SOME _` >> Cases_on `vt0` >>
  gvs[subscript_vtype_def] >>
  rename1 `subscript_vtype (Type t0) _` >> Cases_on `t0` >>
  gvs[subscript_vtype_def]
QED

(* ===== S48: logged events ===== *)

Theorem add_module_static_maps_event_fields[local]:
  !tops a k fs.
    FLOOKUP (add_module_static_maps b src tops a).cta_event_fields k = SOME fs ==>
    (?name. k = (src, name) /\ MEM (EventDecl name fs) tops) \/
    FLOOKUP a.cta_event_fields k = SOME fs
Proof
  Induct >> simp[add_module_static_maps_def] >> rpt gen_tac >>
  strip_tac >>
  first_x_assum (drule o REWRITE_RULE [add_module_static_maps_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `FLOOKUP (FOLDL _ _ _).cta_event_fields _ = _` kall_tac >>
  Cases_on `h` >> gvs[add_toplevel_static_maps_def] >>
  BasicProvers.every_case_tac >> gvs[FLOOKUP_UPDATE] >>
  rpt (qpat_x_assum `(if _ then _ else _) = _` mp_tac) >> rw[] >> gvs[]
QED

Theorem supported_event_fields_event_keys[local]:
  !tops name fields.
    ALL_DISTINCT (FLAT (MAP (event_keys_toplevel (NONE:num option)) tops)) /\
    MEM (EventDecl name fields) tops ==>
    supported_event_fields tops (NONE, name) = SOME fields
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[supported_event_fields_def, ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP,
      PULL_EXISTS, event_keys_toplevel_def] >>
  Cases_on `h` >> gvs[event_keys_toplevel_def] >>
  rw[] >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `EventDecl name fields` mp_tac) >>
  simp[event_keys_toplevel_def]
QED

Theorem check_contract_log_event_fields:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmt env ret (Log id es) = SOME env' ==>
  ?fields. FLOOKUP env.event_fields id = SOME fields /\
           supported_event_fields tops id = SOME fields
Proof
  strip_tac >> drule check_contract_single_namespaces >> strip_tac >>
  gvs[type_stmt_def, AllCaseEqs()] >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def] >> strip_tac >> gvs[] >>
  gvs[build_contract_type_artifact_def] >>
  drule add_module_static_maps_event_fields >>
  simp[empty_contract_type_artifact_def] >> strip_tac >> gvs[] >>
  irule supported_event_fields_event_keys >> simp[]
QED

(* ===== S56, S60, S62: for loops ===== *)

Theorem type_stmt_for_range_integer_type:
  type_stmt env ret (For x ty (Range a b) n loop_body) = SOME env' ==>
  supported_integer_type ty
Proof
  simp[type_stmt_def, well_typed_iterator_def] >> strip_tac >>
  Cases_on `ty` >> gvs[] >> rename1 `BaseT bt'` >> Cases_on `bt'` >>
  gvs[supported_integer_type_def] >> imp_res_tac assignable_int_width
QED

Theorem type_stmt_for_range_bound_pos:
  type_stmt env ret (For x ty (Range a b) n loop_body) = SOME env' ==>
  case (a, b) of
    (Literal _ (IntL _), Literal _ (IntL _)) => T
  | _ => 0 < n
Proof
  simp[type_stmt_def] >> BasicProvers.every_case_tac >> simp[]
QED

Theorem type_stmt_for_array_name_elem:
  type_stmt env ret
    (For x ty (Array (Name (ArrayT elem bd) arr)) n loop_body) = SOME env' ==>
  elem = ty
Proof
  simp[type_stmt_def, well_typed_iterator_def, expr_type_def]
QED
