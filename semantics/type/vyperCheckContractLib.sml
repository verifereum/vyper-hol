structure vyperCheckContractLib :> vyperCheckContractLib = struct

open HolKernel boolLib bossLib
open vyperASTTheory vyperContextTheory vyperInterpreterTheory
open vyperTypeCallGraphTheory vyperTypeCallGraphSoundnessTheory
open vyperTypeContractTheory vyperTypeSystemTheory

 type check_input =
  {in_deploy : bool,
   layouts : term,
   address : term,
   modules : term}

val checker_defs =
  [check_contract_def,
   check_module_def,
   check_toplevel_body_def,
   custom_errors_stmt_ok_def,
   custom_error_resolved_def,
   vyperEventTheory.lookup_custom_error_args_in_def,
   order_custom_error_args_def,
   order_custom_error_kwargs_def,
   custom_error_exprs_def,
   check_function_body_in_mode_def,
   check_function_body_def,
   (* The constant-substituted body check_function_body also types. *)
   constSubstModsTheory.subst_consts_expr_mods_def,
   constSubstModsTheory.subst_consts_target_mods_def,
   constSubstModsTheory.subst_consts_iter_mods_def,
   constSubstModsTheory.subst_consts_error_mods_def,
   constSubstModsTheory.subst_consts_areason_mods_def,
   constSubstModsTheory.subst_consts_rreason_mods_def,
   constSubstModsTheory.subst_consts_stmt_mods_def,
   constSubstModsTheory.module_consts_env_mods_def,
   constSubstModsTheory.consts_env_mods_acc_def,
   constSubstModsTheory.consts_env_modules_order_def,
   constSubstModsTheory.consts_env_mods_def,
   constSubstTheory.fold_const_expr_def,
   constSubstTheory.fold_const_builtin_def,
   check_toplevel_decl_def,
   callee_write_ok_def,
   callee_writes_ok_def,
   stmt_loop_calls_ok_def,
   loop_iterator_place_def,
   function_header_ok_def,
   function_mutability_ok_def,
   call_mutability_ok_def,
   builtin_mutability_def,
   call_target_mutability_ok_def,
   toplevel_target_def,
   expr_mutability_ok_def,
   write_mutability_ok_def,
   atarget_mutability_ok_def,
   iterator_mutability_ok_def,
   reason_calls_ok_def,
   assert_reason_mutability_ok_def,
   raise_reason_mutability_ok_def,
   stmt_mutability_ok_def,
   toplevel_allocated_def,
   module_allocated_def,
   main_module_allocated_def,
   var_allocated_def,
   toplevel_function_keys_def,
   live_roots_def,
   call_closure_compute,
   live_functions_def,
   function_live_def,
   linked_main_roots_def,
   linked_export_roots_def,
   linked_live_functions_from_def,
   linked_toplevel_allocated_def,
   linked_state_ref_allocated_def,
   check_linked_state_ownership_def,
   vyperSubscriptOverlapTheory.constant_decl_def,
   vyperSubscriptOverlapTheory.accesses_expr_def,
   vyperSubscriptOverlapTheory.accesses_atarget_def,
   vyperSubscriptOverlapTheory.accesses_iterator_def,
   vyperSubscriptOverlapTheory.accesses_assert_reason_def,
   vyperSubscriptOverlapTheory.accesses_raise_reason_def,
   vyperSubscriptOverlapTheory.accesses_stmt_def,
   vyperSubscriptOverlapTheory.risky_builtin_def,
   vyperSubscriptOverlapTheory.risky_call_target_def,
   live_artifact_def,
   exports_ok_def,
   vyperABIEntriesTheory.abi_deployed_signatures_def,
   finite_mapTheory.DRESTRICT_FEMPTY,
   finite_mapTheory.DRESTRICT_FUPDATE,
   IN_function_live,
   IN_var_allocated,
   constant_expr_def,
   constant_binop_def,
   constant_builtin_def,
   constant_type_builtin_def,
   declared_constant_def,
   declared_immutable_def,
   runtime_constant_expr_def,
   runtime_constant_builtin_def,
   bool_literal_expr_def,
   check_value_type_def,
   artifact_env_def,
   function_entry_env_def,
   params_ok_def,
   lookup_var_slot_in_layouts_def,
   build_contract_type_artifact_def,
   add_module_static_maps_def,
   add_toplevel_static_maps_def,
   empty_contract_type_artifact_def,
   contract_type_artifact_accessors,
   contract_type_artifact_fn_updates,
   contract_type_artifact_updates_eq_literal,
   typing_env_accessors,
   typing_env_fn_updates,
   typing_env_updates_eq_literal,
   fn_sig_accessors,
   fn_sig_component_equality,
   fn_sig_fn_updates,
   include_fn_sig_def,
   fn_sig_of_def,
   contract_namespaces_ok_def,
   vyperImportRefsTheory.imported_type_refs_ok_def,
   vyperImportRefsTheory.imported_builtin_refs_ok_def,
   vyperImportRefsTheory.imported_call_refs_ok_def,
   vyperImportRefsTheory.imported_expr_refs_ok_def,
   vyperImportRefsTheory.imported_target_refs_ok_def,
   vyperImportRefsTheory.imported_iterator_refs_ok_def,
   vyperImportRefsTheory.imported_error_refs_ok_def,
   vyperImportRefsTheory.imported_assert_refs_ok_def,
   vyperImportRefsTheory.imported_raise_refs_ok_def,
   vyperImportRefsTheory.imported_stmt_refs_ok_def,
   vyperImportRefsTheory.imported_value_type_refs_ok_def,
   vyperImportRefsTheory.imported_toplevel_refs_ok_def,
   contract_keys_def,
   fn_sig_keys_toplevel_def,
   toplevel_vtype_keys_toplevel_def,
   flag_member_keys_toplevel_def,
   error_sig_keys_toplevel_def,
   type_def_keys_toplevel_def,
   self_member_keys_toplevel_def,
    external_name_keys_toplevel_def,
    vyperABIEntriesTheory.abi_external_method_ids_def,
    vyperABIEntriesTheory.abi_external_signatures_def,
    vyperABIEntriesTheory.abi_decl_signatures_def,
    vyperABIEntriesTheory.abi_function_signatures_def,
    vyperABIEntriesTheory.abi_entries_def,
    vyperABIEntriesTheory.abi_getter_args_def,
    vyperABIEntriesTheory.abi_array_getter_args_def,
   event_keys_toplevel_def,
   event_indexable_type_def,
   contract_call_graph_acyclic_def,
   rank_lt_def,
   edges_respect_rank_def,
   call_path_def,
   call_graph_cycle_def,
   call_graph_acyclic_def,
   contract_call_nodes_def,
   contract_call_edges_def,
   module_call_edges_def,
   toplevel_call_edges_def,
   function_int_calls_def,
   int_calls_expr_def,
   int_calls_atarget_def,
   int_calls_iterator_def,
   int_calls_assert_reason_def,
   int_calls_raise_reason_def,
   int_calls_stmt_def,
   direct_callees_def,
   reachable_nodes_compute,
   type_env_all_modules_def,
   type_env_for_module_def,
   type_env_def,
   lookup_nonreentrant_slot_def,
   lookup_function_def,
   lookup_callable_function_def,
   well_formed_type_def,
   is_numeric_type_def,
   is_uint_type_def,
   is_bool_type_def,
   is_uint256_type_def,
   is_bytes32_type_def,
   is_flag_type_def,
   is_sized_type_def,
   is_bytes_or_string_type_def,
   is_comparable_type_def,
   env_item_type_def,
   account_item_type_def,
   extract32_result_base_ok_def,
   assignable_type_def,
   abi_decode_bytes_widths_def,
   valid_conversion_def,
   hashmap_key_type_def,
   defaults_env_def,
   extend_local_def,
   target_mutable_def,
   well_typed_expr_compute,
   well_typed_target_def,
   well_typed_atarget_def,
   atarget_accepts_def,
   call_result_expr_def, call_target_static_def, expr_static_calls_def,
   well_typed_iterator_def,
   well_typed_custom_error_def,
   place_access_def,
   place_contains_def,
   expr_places_def,
   expr_writes_ok_def,
   atarget_writes_ok_def,
   stmt_writes_ok_def,
   iterator_unmodified_def,
   type_stmt_def,
   stmt_no_fallthrough_def,
   expr_no_fallthrough_def,
   stmt_no_control_escape_def,
   vyperValueTheory.evaluate_type_def,
   vyperASTTheory.bound_length_def,
   vyperValueTheory.type_slot_size_def,
   vfmConstantsTheory.word_size_def,
   vyperValueTheory.compatible_bound_def,
   vyperValueTheory.within_int_bound_def,
   vyperValueTheory.decimal_scale_def,
   vyperValueTheory.decimal_bits_def,
   vyperValueTheory.string_to_bytes_def,
   vyperValueTheory.decimal_bound_def,
   expr_type_def,
   well_typed_literal_def,
   well_typed_binop_def,
   integer_value_bits_def,
   power_exponent_ok_def,
   power_operands_ok_def,
   named_const_operand_def,
   builtin_operands_ok_def,
   augassign_shift_amount_ok_def, augassign_operand_ok_def,
   is_prim_word_type_def,
   well_typed_builtin_app_def,
   bytelike_type_bound_def,
   slice_operands_ok_def,
   int_literal_value_def,
   nonneg_int_literal_def,
   shift_amount_ok_def,
   is_int_type_def,
   bound_at_most_def,
   vtype_annotation_ok_def,
   subscript_type_ok_def,
   subscript_base_type_exact_def,
   subscript_vtype_def,
   attribute_type_def,
   attribute_type_ok_def,
   well_typed_type_builtin_args_def,
   type_builtin_result_ok_def,
   abi_encode_size_ok_def,
   abi_encode_method_id_size_def,
   vyperASTTheory.abi_encode_method_id_bytes_def,
   vyperABITheory.vyper_abi_size_bound_def,
   vyperABITheory.vyper_is_dynamic_def,
   contractABITheory.ceil32_def,
   raw_call_return_type_def,
   raw_call_kws_ok_def,
   ext_call_opts_ok_def,
   ext_call_kw_type_def,
   arg_type_fits_def,
   type_widens_to_def,
   create_arg_types_ok_compute,
   optionTheory.option_case_lazily,
   optionTheory.IS_SOME_DEF,
   optionTheory.IS_NONE_DEF,
   optionTheory.THE_DEF,
   pairTheory.FST,
   pairTheory.SND,
   pairTheory.UNCURRY_DEF,
   listTheory.LIST_REL_def,
   numposrepTheory.l2n_def] @
  (* Constants fold (contract_constants_ok): the constant evaluator, the
     immutables load_contract installs, and the value operations the constant
     builtins reach.  Other builtins' operations are deliberately absent;
     constant_value rejects those builtins before evaluating them. *)
  [contract_constants_ok_def,
   constants_fold_def,
   vyperInterpreterTheory.constants_order_def,
   constants_fold_module_def,
   merge_constant_imms_def,
   constant_value_def,
   constant_length_def,
   constant_context_def,
   empty_evaluation_context_def,
   empty_call_txn_def,
   get_tenv_def,
   initial_immutables_def,
   initial_immutables_module_def,
   vyperStateTheory.update_immutable_def,
   vyperStateTheory.empty_immutables_def,
   vyperStateTheory.get_source_immutables_def,
   vyperStateTheory.set_source_immutables_def,
   vyperStateTheory.find_var_decl_by_name_def,
   vyperStateTheory.evaluate_subscripts_def,
   builtin_args_length_ok_def,
   type_builtin_args_length_ok_def,
   evaluate_builtin_def,
   evaluate_type_builtin_def,
   vyperValueTheory.default_value_def,
   vyperValueTheory.make_array_value_def,
   vyperValueTheory.enumerate_static_array_def,
   vyperValueOperationTheory.evaluate_literal_def,
   vyperValueOperationTheory.array_index_def,
   vyperValueOperationTheory.array_elements_def,
   vyperValueOperationTheory.evaluate_attribute_def,
   vyperValueOperationTheory.evaluate_in_array_def,
   vyperValueOperationTheory.evaluate_binop_def,
   vyperValueOperationTheory.binop_negate_def,
   vyperValueOperationTheory.signed_int_mod_def,
   vyperValueOperationTheory.wrapped_int_op_def,
   vyperValueOperationTheory.bounded_int_op_def,
   vyperValueOperationTheory.bounded_decimal_op_def,
   vyperValueOperationTheory.evaluate_as_wei_value_def,
   vyperValueOperationTheory.evaluate_max_value_def,
   vyperValueOperationTheory.evaluate_min_value_def,
   vyperASTTheory.type_to_int_bound_def,
   vyperASTTheory.int_bound_bits_def,
   vyperASTTheory.is_Unsigned_def,
   intExtensionTheory.SGN_def,
   int_bitwiseTheory.int_and_def,
   int_bitwiseTheory.int_or_def,
   int_bitwiseTheory.int_xor_def,
   int_bitwiseTheory.int_bitwise_def,
   int_bitwiseTheory.int_shift_left_def,
   int_bitwiseTheory.int_shift_right_def,
   int_bitwiseTheory.int_not_def,
   int_bitwiseTheory.bits_of_int_def,
   int_bitwiseTheory.bits_of_num_def,
   int_bitwiseTheory.int_of_bits_def,
   int_bitwiseTheory.num_of_bits_def,
   int_bitwiseTheory.bits_bitwise_def,
   alistTheory.ADELKEY_def,
   optionTheory.OPTION_MAP_DEF]

(* This is deliberately fixed rather than derived from the global TypeBase. *)
val checker_datatypes =
  [``:vyperAST$toplevel``, ``:vyperAST$expr``, ``:vyperAST$stmt``,
   ``:vyperAST$type``, ``:vyperAST$base_type``, ``:vyperAST$value_type``,
   ``:vyperAST$int_bound``, ``:vyperAST$literal``, ``:vyperAST$binop``,
   ``:vyperAST$env_item``, ``:vyperAST$account_item``,
   ``:vyperAST$denomination``, ``:vyperAST$builtin``,
   ``:vyperAST$create_kind``, ``:vyperAST$call_target``,
   ``:vyperAST$type_builtin``, ``:vyperAST$base_assignment_target``,
   ``:vyperAST$assignment_target``,
   ``:vyperAST$iterator``, ``:vyperAST$assert_reason``,
   ``:vyperAST$raise_reason``, ``:vyperAST$function_visibility``,
   ``:vyperAST$custom_error``,
   ``:vyperAST$function_mutability``, ``:vyperAST$variable_visibility``,
   ``:vyperTypeContract$contract_type_artifact``,
   ``:vyperSubscriptOverlap$var_ref``, ``:vyperSubscriptOverlap$var_access``,
   ``:vyperTypeSystem$typing_env``, ``:vyperTypeSystem$fn_sig``,
   ``:vyperAST$variable_mutability``, ``:vyperValue$type_args``,
   ``:vyperAST$bound``, ``:vyperAST$raw_call_flags``, ``:vyperAST$ext_call_kw``,
   ``:string$char``,
   ``:vyperValue$type_value``, ``:vyperValue$value``,
   ``:vyperValue$array_value``, ``:vyperState$eval_result``,
   ``:vyperState$var_decl_info``, ``:vyperContext$evaluation_context``,
   ``:vyperContext$call_txn``, ``:'a + 'b``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

(* Freshness checks (`id NOTIN FDOM var_types`) compare each declared name
   with every earlier one. Through the generic rules each comparison walks
   every character with CONS_11 and ORD/CHR numeral arithmetic. These
   conversions decide literal string equality at the first differing
   character, and membership in an INSERT chain of literals one key at a
   time; they decline everything else. *)
local
  val string_ty = stringSyntax.string_ty
  val char_ty = stringSyntax.char_ty
  val c = mk_var ("c", char_ty)
  val c1 = mk_var ("c1", char_ty)
  val c2 = mk_var ("c2", char_ty)
  val s = mk_var ("s", string_ty)
  val s1 = mk_var ("s1", string_ty)
  val s2 = mk_var ("s2", string_ty)
  fun cons (h, t) = listSyntax.mk_cons (h, t)
  (* |- !c s1 s2. (c::s1 = c::s2) <=> (s1 = s2) *)
  val same_head = GENL [c, s1, s2] (RIGHT_CONV_RULE (REWRITE_CONV [])
    (PART_MATCH lhs listTheory.CONS_11 (mk_eq (cons (c, s1), cons (c, s2)))))
  (* |- !c1 c2 s1 s2. ((c1 = c2) <=> F) ==> ((c1::s1 = c2::s2) <=> F) *)
  val diff_head = let
    val hyp = mk_eq (mk_eq (c1, c2), F)
  in
    GENL [c1, c2, s1, s2] (DISCH hyp
      (RIGHT_CONV_RULE (REWRITE_CONV [ASSUME hyp])
        (PART_MATCH lhs listTheory.CONS_11
          (mk_eq (cons (c1, s1), cons (c2, s2))))))
  end
  val cons_nil = GENL [c, s] (EQF_INTRO
    (PART_MATCH (lhs o dest_neg) listTheory.NOT_CONS_NIL (cons (c, s))))
  val nil_cons = GENL [c, s] (EQF_INTRO
    (PART_MATCH (rhs o dest_neg) listTheory.NOT_NIL_CONS (cons (c, s))))
  val refl = INST_TYPE [alpha |-> string_ty] boolTheory.REFL_CLAUSE
  (* char_EQ_CONV results, indexed by the two character codes *)
  val char_cache : thm option Array.array = Array.array (256 * 256, NONE)
  fun char_ne c1 c2 = let
    val key = 256 * Char.ord (stringSyntax.fromHOLchar c1) +
              Char.ord (stringSyntax.fromHOLchar c2)
  in
    case Array.sub (char_cache, key) of
      SOME th => th
    | NONE => let
        val th = stringLib.char_EQ_CONV (mk_eq (c1, c2))
      in Array.update (char_cache, key, SOME th); th end
  end
  (* (l = r) <=> F for distinct literals l and r *)
  fun differ l r =
    case (Lib.total listSyntax.dest_cons l,
          Lib.total listSyntax.dest_cons r) of
      (SOME (c1, t1), SOME (c2, t2)) =>
        if aconv c1 c2 then TRANS (SPECL [c1, t1, t2] same_head) (differ t1 t2)
        else MP (SPECL [c1, c2, t1, t2] diff_head) (char_ne c1 c2)
    | (SOME (c, t), NONE) => SPECL [c, t] cons_nil
    | (NONE, SOME (c, t)) => SPECL [c, t] nil_cons
    | (NONE, NONE) => raise UNCHANGED
  val x = mk_var ("x", string_ty)
  val k = mk_var ("k", string_ty)
  val st = mk_var ("st", pred_setSyntax.mk_set_type string_ty)
  val in_empty = GEN x (EQF_INTRO (ISPEC x pred_setTheory.NOT_IN_EMPTY))
  val in_head = GENL [x, st] (EQT_INTRO
    (ISPECL [x, st] pred_setTheory.COMPONENT))
  val in_insert = ISPECL [x, k, st] pred_setTheory.IN_INSERT
  (* |- !x k st. (x IN st <=> T) ==> (x IN k INSERT st <=> T) *)
  val in_tail_t = let
    val h = mk_eq (pred_setSyntax.mk_in (x, st), T)
  in
    GENL [x, k, st] (DISCH h
      (RIGHT_CONV_RULE (REWRITE_CONV [ASSUME h]) in_insert))
  end
  (* |- !x k st. ((x = k) <=> F) ==> (x IN st <=> F) ==>
                 (x IN k INSERT st <=> F) *)
  val in_tail_f = let
    val h1 = mk_eq (mk_eq (x, k), F)
    val h2 = mk_eq (pred_setSyntax.mk_in (x, st), F)
  in
    GENL [x, k, st] (DISCH h1 (DISCH h2
      (RIGHT_CONV_RULE (REWRITE_CONV [ASSUME h1, ASSUME h2]) in_insert)))
  end
  fun member x set =
    case Lib.total pred_setSyntax.dest_insert set of
      SOME (k, rest) =>
        if aconv x k then SPECL [x, rest] in_head
        else let
          val th = member x rest
        in
          if Teq (rhs (concl th)) then MP (SPECL [x, k, rest] in_tail_t) th
          else MP (MP (SPECL [x, k, rest] in_tail_f) (differ x k)) th
        end
    | NONE => SPEC x in_empty
  fun literal_chain set =
    case Lib.total pred_setSyntax.dest_insert set of
      SOME (k, rest) =>
        stringSyntax.is_string_literal k andalso literal_chain rest
    | NONE => pred_setSyntax.is_empty set
in
  fun string_literal_eq_conv tm = let
    val (l, r) = dest_eq tm
  in
    if not (stringSyntax.is_string_literal l andalso
            stringSyntax.is_string_literal r) then raise UNCHANGED
    else if aconv l r then SPEC l refl
    else differ l r
  end
  fun string_literal_in_conv tm = let
    val (x, set) = pred_setSyntax.dest_in tm
  in
    if stringSyntax.is_string_literal x andalso literal_chain set
    then member x set else raise UNCHANGED
  end
end

(* Every base compset's equality entry already holds the list, int and
   numeral rules, and computeLib tries an entry's rules and conversions in
   the order they were added, so a conversion added with add_conv is never
   reached on strings. Rebuild the entry with the conversion first. Rules
   compiled before this keep the old entry. *)
fun add_conv_first (tm, arity, conv) cs = let
  val {Name, Thy, ...} = dest_thy_const tm
  val entry =
    case List.find (fn ((name, thy), _) => name = Name andalso thy = Thy)
           (computeLib.listItems cs) of
      SOME (_, transforms) => transforms
    | NONE => []
  val rules = List.concat
    (map (fn clauses.RRules ths => ths | _ => []) entry)
  val convs = List.mapPartial
    (fn clauses.Conversion c => SOME c | _ => NONE) entry
  val general = prim_mk_const {Name = Name, Thy = Thy}
in
  computeLib.scrub_const cs general
  |> computeLib.add_conv (tm, arity, conv)
  |> computeLib.add_thms rules
  |> (fn cs => foldl (fn (c, cs) => computeLib.add_conv (general, arity, c) cs)
                     cs convs)
end

fun build_checker_base () =
  reduceLib.num_compset
  |> computeLib.copy
  |> add_conv_first (inst [alpha |-> stringSyntax.string_ty]
                       boolSyntax.equality, 2, string_literal_eq_conv)
  |> add_conv_first (inst [alpha |-> stringSyntax.string_ty]
                       pred_setSyntax.in_tm, 2, string_literal_in_conv)
  |> listSimps.list_rws
  |> pred_setLib.add_pred_set_compset
  (* INSERT_CONV dedups every INSERT node with an IN_CONV over the tail, which
     makes each FDOM freshness check quadratic in the declared locals
     (HOL-Theorem-Prover/HOL#2101). Scrub it before anything else is added:
     a compiled rule such as FDOM_FUPDATE keeps the INSERT entry it saw. *)
  |> (fn cs => computeLib.scrub_const cs pred_setSyntax.insert_tm)
  |> combinLib.add_combin_compset
  |> numposrepLib.add_numposrep_compset
  |> ASCIInumbersLib.add_ASCIInumbers_compset
  |> intReduce.add_int_compset
  |> wordsLib.add_words_compset false
  |> integer_wordLib.add_integer_word_compset
  |> bitLib.add_bit_compset
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> stringLib.add_string_compset
  |> computeLib.extend_compset [computeLib.Tys checker_datatypes]
  |> computeLib.add_thms checker_defs
   (* Selector hashing uses the shared ABI definition and a checked CV
      evaluation, so checker results remain kernel theorems. *)
   |> computeLib.add_conv
        (prim_mk_const {Thy = "vyperABIEntries", Name = "abi_method_id"},
         3, cv_transLib.cv_eval)

fun inst_apply function argument = let
  val (domain_ty, _) = dom_rng (type_of function)
  val instantiated = Term.inst
    (Type.match_type domain_ty (type_of argument)) function
in
  mk_comb (instantiated, argument)
end

fun apply function arguments =
  foldl (fn (argument, applied) => inst_apply applied argument)
    function arguments

fun eta_expand_quantifier_predicate tm = let
  val (quantifier, predicate) = dest_comb tm
  val (domain_ty, _) = dom_rng (type_of predicate)
  val bound = genvar domain_ty
  val expanded = mk_abs (bound, mk_comb (predicate, bound))
in
  AP_TERM quantifier (SYM (ETA_CONV expanded))
end

val check_contract_compset = let
  (* These inner conversions have no call-graph or quantifier hooks, avoiding
     recursive invocation while certificates and quantified bodies compute. *)
  val call_graph_base_conv = computeLib.CBV_CONV (build_checker_base ())
  val quantifier_body_conv = computeLib.CBV_CONV (build_checker_base ())
  val call_graph_const = prim_mk_const
    {Thy = "vyperTypeCallGraph", Name = "contract_call_graph_acyclic"}
  val call_edges_const = prim_mk_const
    {Thy = "vyperTypeCallGraph", Name = "contract_call_edges"}
  val rank_check_const = prim_mk_const
    {Thy = "vyperTypeCallGraph", Name = "edges_respect_rank"}
  val cycle_check_const = prim_mk_const
    {Thy = "vyperTypeCallGraph", Name = "call_graph_cycle"}
  val node_ty = ``:num option # string``
  val rank_entry_ty = ``:(num option # string) # num``

  fun term_mem tm = List.exists (fn other => aconv tm other)
  fun term_insert tm terms = if term_mem tm terms then terms else tm::terms
  fun endpoints edge = pairSyntax.dest_pair edge

  (* This ML search is untrusted: both outcomes are rechecked by closed HOL
     predicates, and only their soundness theorems produce the final result. *)
  datatype graph_search = Ranked of term list | Cycle of term list
  exception CyclicCallGraph of term list

  fun topological_order edges = let
    val raw_nodes = List.concat (map (fn edge => let
      val (caller, callee) = endpoints edge
    in [caller, callee] end) edges)
    val nodes = rev
      (foldl (fn (tm, terms) => term_insert tm terms) [] raw_nodes)
    val temporary = ref ([] : term list)
    val permanent = ref ([] : term list)
    val postorder = ref ([] : term list)
    fun successors node = map (snd o endpoints)
      (List.filter
        (fn edge => aconv (fst (endpoints edge)) node) edges)
    fun path_from target [] =
          raise Fail "call-graph DFS lost its active target"
      | path_from target (node::rest) =
          if aconv node target then [node]
          else node :: path_from target rest
    fun visit node =
      if term_mem node (!permanent) then ()
      else if term_mem node (!temporary) then
        raise CyclicCallGraph (rev (path_from node (!temporary)))
      else let
        val () = temporary := node :: !temporary
        val () = List.app visit (successors node)
        val () = temporary :=
          List.filter (fn other => not (aconv other node)) (!temporary)
        val () = permanent := node :: !permanent
        val () = postorder := node :: !postorder
      in () end
    val () = List.app visit nodes
  in
    !postorder
  end

  fun rank_certificate nodes =
    listSyntax.mk_list
      (ListPair.mapEq
        (fn (node, index) =>
          pairSyntax.mk_pair (node, numSyntax.term_of_int index))
        (nodes, List.tabulate (length nodes, fn index => index)),
       rank_entry_ty)

  fun call_graph_conv tm = let
    val (head, arguments) = strip_comb tm
    val () = if aconv head call_graph_const andalso length arguments = 1
      then () else raise UNCHANGED
    val mods = hd arguments
    val () = if null (free_vars mods) then () else raise UNCHANGED
    val edges_tm = apply call_edges_const [mods]
    val edges_thm = call_graph_base_conv edges_tm
    val (actual_edges_tm, edges) = dest_eq (concl edges_thm)
    val () = if aconv actual_edges_tm edges_tm then ()
      else raise Fail "call-graph edge conversion changed its left-hand side"
    val (edge_terms, _) = listSyntax.dest_list edges
  in
    case (Ranked (topological_order edge_terms)
          handle CyclicCallGraph path => Cycle path) of
      Cycle path => let
        val path_tm = listSyntax.mk_list (path, node_ty)
        val certificate_tm = apply cycle_check_const [edges_tm, path_tm]
        val certificate_thm = call_graph_base_conv certificate_tm
        val certificate = EQT_ELIM certificate_thm
        val cyclic = MATCH_MP contract_call_graph_cycle certificate
        val () = if aconv (dest_neg (concl cyclic)) tm then ()
          else raise Fail "cycle certificate proved an unexpected proposition"
      in
        EQF_INTRO cyclic
      end
    | Ranked ordered_nodes => let
        val ranks = rank_certificate ordered_nodes
        val certificate_tm = apply rank_check_const [ranks, edges_tm]
        val certificate_thm = call_graph_base_conv certificate_tm
        val certificate = EQT_ELIM certificate_thm
        val acyclic = MATCH_MP contract_edges_respect_rank certificate
        val () = if aconv (concl acyclic) tm then ()
          else raise Fail "rank certificate proved an unexpected proposition"
      in
        EQT_INTRO acyclic
      end
  end

  val normalize_quantifier_predicate =
    SIMP_CONV bool_ss [vyperASTTheory.type_distinct]
  fun determined_quantifier_conv tm =
    (normalize_quantifier_predicate THENC
     TRY_CONV quantHeuristicsLib.SIMPLE_QUANT_INSTANTIATE_CONV THENC
     quantifier_body_conv THENC
     TRY_CONV eta_expand_quantifier_predicate THENC
     TRY_CONV quantHeuristicsLib.SIMPLE_QUANT_INSTANTIATE_CONV THENC
     quantifier_body_conv) tm
  fun normalized_universal_conv tm =
    (RAND_CONV (ABS_CONV quantifier_body_conv) THENC
     SIMP_CONV bool_ss [vyperASTTheory.type_distinct]) tm
in
  build_checker_base ()
  |> (fn cs => computeLib.scrub_const cs call_graph_const)
  |> computeLib.add_conv (call_graph_const, 1, call_graph_conv)
  |> computeLib.add_conv
       (boolSyntax.existential, 1, determined_quantifier_conv)
  |> computeLib.add_conv
       (boolSyntax.universal, 1, normalized_universal_conv)
  |> computeLib.seal
end

(* Plain call-by-value evaluation with the shared compset. *)
val plain_conv = computeLib.CBV_CONV check_contract_compset

(* check_contract_def binds the live functions and the restricted artifact with
   lets. CBV_CONV reduces a let argument only to weak head normal form, so the
   artifact's DRESTRICT maps reach every lookup in the body still unreduced and
   are restricted again at each one. For a full application the staged
   conversion unfolds check_contract_def and evaluates both lets to normal
   form before the body, so each lookup finds the maps already restricted.
   Every step is the checker's own conversion, so the result is the same
   check_contract_def equation, reached with fewer reductions. *)
local
  val check_contract_const = prim_mk_const
    {Thy = "vyperTypeContract", Name = "check_contract"}
  val let_conv = REWR_CONV LET_THM THENC BETA_CONV
in
  fun check_contract_conv tm = let
    val (head, arguments) = strip_comb tm
  in
    if same_const head check_contract_const andalso length arguments = 4
    then (REWR_CONV check_contract_def THENC
          RAND_CONV plain_conv THENC let_conv THENC
          RAND_CONV plain_conv THENC let_conv THENC
          plain_conv) tm
    else plain_conv tm
  end
end

fun mk_check_contract {in_deploy, layouts, address, modules} =
  let
    val arguments = [boolSyntax.mk_bool in_deploy, layouts, address, modules]
    val () = if List.all (null o free_vars) arguments then ()
      else raise Fail "check_contract input is open"
    val checker = prim_mk_const
      {Thy = "vyperTypeContract", Name = "check_contract"}
  in
    foldl (fn (argument, applied) => inst_apply applied argument)
      checker arguments
  end

fun check_contract_with conversion input = let
  val application = mk_check_contract input
  val theorem = conversion application
  val () = if null (hyp theorem) then ()
    else raise Fail "check_contract theorem has assumptions"
  val (lhs, result) = dest_eq (concl theorem)
  val () = if aconv lhs application then ()
    else raise Fail "check_contract theorem has an unexpected left-hand side"
  val artifact = if optionSyntax.is_some result
    then optionSyntax.dest_some result
    else raise Fail ("check_contract returned " ^ term_to_string result)
  val () = if null (free_vars artifact) then ()
    else raise Fail "check_contract returned an open artifact"
in
  theorem
end

fun check_contract input = check_contract_with check_contract_conv input

end
