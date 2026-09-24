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

val in_empty_eq =
  pred_setTheory.NOT_IN_EMPTY |> SPEC_ALL |> EQF_INTRO |> GEN_ALL

val checker_defs =
  [check_contract_def,
   check_module_def,
   check_toplevel_body_def,
   check_function_body_in_mode_def,
   check_function_body_def,
   check_toplevel_decl_def,
   constant_expr_def,
   constant_binop_def,
   constant_builtin_def,
   constant_type_builtin_def,
   declared_constant_def,
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
   contract_keys_def,
   fn_sig_keys_toplevel_def,
   toplevel_vtype_keys_toplevel_def,
   flag_member_keys_toplevel_def,
   type_def_keys_toplevel_def,
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
   lookup_nonreentrant_slot_def,
   lookup_function_def,
   lookup_callable_function_def,
   well_formed_type_def,
   pair_num_def,
   type_key_def,
   is_numeric_type_def,
   is_uint_type_def,
   is_bool_type_def,
   is_flag_type_def,
   is_sized_type_def,
   is_bytes_or_string_type_def,
   is_comparable_type_def,
   env_item_type_def,
   assignable_type_def,
   valid_conversion_def,
   hashmap_key_type_def,
   defaults_env_def,
   extend_local_def,
   well_typed_expr_def,
   well_typed_target_def,
   well_typed_atarget_def,
   well_typed_iterator_def,
   type_stmt_def,
   well_typed_stmt_def,
   well_typed_stmts_def,
   stmt_no_fallthrough_def,
   stmt_no_control_escape_def,
   vyperMiscTheory.string_to_num_def,
   vyperValueTheory.evaluate_type_def,
   vyperValueTheory.type_slot_size_def,
   vfmConstantsTheory.word_size_def,
   vyperValueTheory.compatible_bound_def,
   vyperValueTheory.within_int_bound_def,
   expr_type_def,
   well_typed_literal_def,
   well_typed_binop_def,
   well_typed_builtin_app_def,
   is_int_type_def,
   bound_at_most_def,
   vtype_annotation_ok_def,
   subscript_type_ok_def,
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
   raw_call_return_type_def,
   create_arg_types_ok_def,
   optionTheory.option_case_lazily,
   optionTheory.IS_SOME_DEF,
   optionTheory.THE_DEF,
   pairTheory.FST,
   pairTheory.SND,
   pairTheory.UNCURRY_DEF,
   listTheory.LIST_REL_def,
   numposrepTheory.l2n_def]

(* This mirrors listSimps.list_rws, except that LIST_TO_SET_THM is replaced
   by structural MEM computation. Installing LIST_TO_SET_THM makes definitions
   such as nub compile membership through finite sets, with pathological
   proof-producing performance. Keep this local copy until the upstream issue
   is resolved: https://github.com/HOL-Theorem-Prover/HOL/issues/2055 *)
local open listTheory in
val checker_list_rws =
  [ALL_DISTINCT, APPEND, APPEND_NIL, CONS_11, DROP_compute, EL_restricted,
   EL_simp_restricted, EVERY_DEF, EXISTS_DEF, FILTER, FIND_def, FLAT, FOLDL,
   FOLDR, FRONT_DEF, GENLIST_AUX_compute, GENLIST_NUMERALS, HD, INDEX_FIND_def,
   INDEX_OF_def, LAST_compute, LENGTH, LEN_DEF, LIST_APPLY_def, LIST_BIND_def,
   LIST_IGNORE_BIND_def, LIST_LIFT2_def, MEM, LLEX_def, LRC_def,
   LUPDATE_compute, MAP, MAP2, NOT_CONS_NIL, NOT_NIL_CONS, NULL_DEF, oEL_def,
   oHD_def, PAD_LEFT, PAD_RIGHT, REVERSE_REV, REV_DEF, SHORTLEX_def, SNOC,
   SUM_ACC_DEF, SUM_SUM_ACC, TAKE_compute, TL, UNZIP, ZIP,
   computeLib.lazyfy_thm list_case_compute, dropWhile_def, isPREFIX,
   list_size_def, nub_def, splitAtPki_def]
end

(* Install empty-set membership before the list rules so ALL_DISTINCT does not
   retain a problematic prior IN treatment, then restore general predicate-set
   computation after installing the structural list fragment. *)
fun add_list_compset cs =
  cs
  |> pred_setLib.add_pred_set_compset
  |> (fn cs' => computeLib.scrub_const cs' ``bool$IN``)
  |> computeLib.add_thms [in_empty_eq]
  |> computeLib.add_thms checker_list_rws
  |> pred_setLib.add_pred_set_compset

(* This is deliberately fixed rather than derived from the global TypeBase. *)
val checker_datatypes =
  [``:vyperAST$toplevel``, ``:vyperAST$expr``, ``:vyperAST$stmt``,
   ``:vyperAST$type``, ``:vyperAST$base_type``, ``:vyperAST$value_type``,
   ``:vyperAST$int_bound``, ``:vyperAST$literal``, ``:vyperAST$binop``,
   ``:vyperAST$env_item``, ``:vyperAST$account_item``,
   ``:vyperAST$denomination``, ``:vyperAST$builtin``,
   ``:vyperAST$create_kind``, ``:vyperAST$call_target``,
   ``:vyperAST$type_builtin``, ``:vyperAST$assignment_target``,
   ``:vyperAST$iterator``, ``:vyperAST$assert_reason``,
   ``:vyperAST$raise_reason``, ``:vyperAST$function_visibility``,
   ``:vyperAST$function_mutability``, ``:vyperAST$variable_visibility``,
   ``:vyperTypeContract$contract_type_artifact``,
   ``:vyperTypeSystem$typing_env``, ``:vyperTypeSystem$fn_sig``,
   ``:vyperAST$variable_mutability``, ``:vyperValue$type_args``,
   ``:vyperAST$bound``, ``:vyperAST$raw_call_flags``, ``:string$char``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

fun build_checker_base () =
  reduceLib.num_compset
  |> computeLib.copy
  |> add_list_compset
  |> combinLib.add_combin_compset
  |> numposrepLib.add_numposrep_compset
  |> ASCIInumbersLib.add_ASCIInumbers_compset
  |> intReduce.add_int_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> stringLib.add_string_compset
  |> computeLib.extend_compset [computeLib.Tys checker_datatypes]
  |> computeLib.add_thms checker_defs

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

fun check_contract_conv tm =
  computeLib.CBV_CONV check_contract_compset tm

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
