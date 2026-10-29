(* Source-derived assignment-order validation: checked frontend inputs,
   supported-program boundaries, exact bytecode parity and interpreter results. *)
Theory evalAssignmentOrder
Ancestors
  vyperInterpreter vyperTypeSystem jsonToVyper jsonConstEval
  compileVyper concretizeMemLocDefs supportedProgram supportedStmts
  vyperSmallStep vyperStorageBackend finite_map While alist byte integer_word option
Libs
  vyperCheckContractFrontendLib evalCompilerBytecodeLib finite_mapLib
  computeLib wordsLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../assignment-order/oracle", "../assignment-order/sources",
   "../assignment-order/fixtures.txt"]
val () = computeLib.upd_compset add_finite_map_compset

fun define_source_fixture name = let
  val path = "../assignment-order/oracle/" ^ name ^ ".json"
  val ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val checked = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = ast, storage_layout = layout}
  val deploy = vyperCheckContractFrontendLib.check_contract_result
    {in_deploy = true, address = ``0w : address``,
     annotated_ast = ast, storage_layout = layout}
  val input = #input checked
  val modules = #modules input
  val layouts = #layouts input
  val lookup = EVAL ``ALOOKUP ^modules NONE``
  val program = optionSyntax.dest_some (rhs (concl lookup))
  fun define suffix tm = let
    val def = new_definition (name ^ suffix ^ "_def",
      mk_eq (mk_var (name ^ suffix, type_of tm), tm))
    val () = computeLib.add_persistent_funs [name ^ suffix ^ "_def"]
    val () = cv_auto_trans def
  in def end
  val _ = define "_source_program" program
  val _ = define "_source_context"
    ``empty_evaluation_context with
      <|sources := [(0w, ^modules)]; layouts := ^layouts|>``
  val _ = save_thm (name ^ "_frontend_checked", #theorem checked)
  val _ = save_thm (name ^ "_frontend_checked_deploy", #theorem deploy)
in () end;

val fixture_names =
  evalCompilerBytecodeLib.read_all "../assignment-order/fixtures.txt"
  |> String.tokens (fn c => c = #"\n" orelse c = #"\r")
  |> List.map evalCompilerBytecodeLib.strip_comment
  |> List.filter (fn name => name <> "");
val () = List.app define_source_fixture fixture_names;

Definition assignment_empty_state_def:
  assignment_empty_state = empty_state with scopes := [FEMPTY]
End
val () = cv_auto_trans assignment_empty_state_def;

(* Every compiler fixture must be supported and match both byte lists. *)
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos]);

fun check_compiler_fixture name = let
  val program = prim_mk_const
    {Thy = "evalAssignmentOrder", Name = name ^ "_source_program"}
  val expected = evalCompilerBytecodeLib.read_hex_bytes_from
    ("../assignment-order/oracle/" ^ name ^ ".hex")
  val _ = save_thm (name ^ "_supported",
    EQT_ELIM (EVAL ``supported_program ^program``))
  val _ = save_thm (name ^ "_matches_python", EQT_ELIM (EVAL
    ``compile_vyper (K SOME) (o1_policy all_capabilities) ^program = SOME ^expected``))
in () end;

val () = List.app check_compiler_fixture
  ["c08_storage_arr_assign_computed_rhs", "c09_storage_map_assign_computed_rhs",
   "g6_write_order_side", "x04_assign_sideeffect_order",
   "s11_storage_map_assign_extcall_rhs", "g19_aug_rhs_modifies_target"];

Theorem flat_tuple_assignment_supported:
  supported_stmt []
    [("x",BaseT (UintT 256)); ("y",BaseT (UintT 256));
     ("pair",TupleT [BaseT (UintT 256); BaseT (UintT 256)])]
    (Assign (TupleTarget [BaseTarget (NameTarget "x"); BaseTarget (NameTarget "y")])
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair"))
Proof
  EVAL_TAC
QED

Theorem nested_tuple_lowering_remains_excluded:
  ~supported_stmt tops bindings
    (Assign (TupleTarget [TupleTarget targets]) rhs)
Proof
  simp[supported_stmt_def, supported_assignment_def]
QED

Theorem nested_pop_key_rejected[local]:
  ~supported_expr tops
    (Builtin ty (Bop Add) (Pop pty target :: rest))
Proof
  simp[supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def]
QED

Theorem nested_pop_assignment_rejected[local]:
  ~supported_stmt tops bindings
    (Assign (BaseTarget (SubscriptTarget (TopLevelNameTarget id)
      (Builtin ty (Bop Add) (Pop pty target :: rest)))) rhs)
Proof
  simp[supported_stmt_def, supported_assignment_def, supported_target_def,
       supportedTargetsTheory.supported_target_info_def, nested_pop_key_rejected]
QED

Theorem nested_pop_compiler_form_remains_excluded:
  ~supported_program assign_nested_popped_read_source_program
Proof
  strip_tac >> drule supported_program_declaration >>
  disch_then (qspec_then `EL 1 assign_nested_popped_read_source_program` mp_tac) >>
  simp[DB.fetch "evalAssignmentOrder" "assign_nested_popped_read_source_program_def",
       supported_declaration_body_def, supported_function_body_def,
       supported_stmts_list, nested_pop_assignment_rejected]
QED

Theorem assignment_cont_pre[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`ss`,`st`,`DoneK`] mp_tac (cj 2 eval_cps_eq) >>
  rw[cont_def] >> CASE_TAC >> CASE_TAC >> gvs[] >>
  rw[Once OWHILE_THM]
QED

Definition assignment_run_def:
  assignment_run cx program st =
    eval_stmts cx
      (case lookup_function NONE "f" External program of
       | SOME (_,_,_,_,_,ss) => ss
       | NONE => []) st
End
val () = cv_auto_trans (REWRITE_RULE [eval_stmts_eq_cont_cps] assignment_run_def);

Definition assignment_slot_def:
  assignment_slot cx st (slot:bytes32) =
    case get_storage_backend cx F st of
    | (INL storage,_) => lookup_storage slot storage
    | (INR _,_) => 0w
End
val () = cv_auto_trans assignment_slot_def;

Theorem assignment_rhs_side_effect_precedes_target:
  let (res,st) = assignment_run x04_assign_sideeffect_order_source_context
        x04_assign_sideeffect_order_source_program assignment_empty_state in
  res = INL () /\ assignment_slot x04_assign_sideeffect_order_source_context st 0w = 2w /\
  assignment_slot x04_assign_sideeffect_order_source_context st
    92458281274488595289803937127152923398167637295201432141969818930235769911599w = 0w /\
  assignment_slot x04_assign_sideeffect_order_source_context st
    105409183525425523237923285454331214386340807945685310246717412709691342439136w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_storage_read_is_delayed:
  let (res,st) = assignment_run assign_delayed_storage_read_source_context
        assign_delayed_storage_read_source_program assignment_empty_state in
  res = INL () /\ assignment_slot assign_delayed_storage_read_source_context st 0w = 1w /\
  assignment_slot assign_delayed_storage_read_source_context st
    92458281274488595289803937127152923398167637295201432141969818930235769911599w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_popped_element_remains_readable:
  FST (assignment_run assign_delayed_popped_read_source_context
    assign_delayed_popped_read_source_program assignment_empty_state) =
  INR (ReturnException (IntV 5))
Proof
  CONV_TAC cv_eval
QED

Theorem assignment_nested_pop_reads_updated_snapshot:
  let (res,st) = assignment_run assign_nested_popped_read_source_context
        assign_nested_popped_read_source_program assignment_empty_state in
  res = INL () /\
  assignment_slot assign_nested_popped_read_source_context st
    24465873643947496235832446106509767096567058095563226156125564318740882468607w = 1w /\
  assignment_slot assign_nested_popped_read_source_context st
    24465873643947496235832446106509767096567058095563226156125564318740882468608w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_assignment_reads_before_rhs:
  let (res,st) = assignment_run g19_aug_rhs_modifies_target_source_context
        g19_aug_rhs_modifies_target_source_program assignment_empty_state in
  res = INL () /\ assignment_slot g19_aug_rhs_modifies_target_source_context st 0w = 1w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_storage_write_retains_resolved_slot:
  let initial = SND (set_storage_backend aug_storage_shrink_source_context F
        (update_storage 0w 1w (update_storage 1w 5w empty_storage)) assignment_empty_state) in
  let (res,st) = assignment_run aug_storage_shrink_source_context
        aug_storage_shrink_source_program initial in
  res = INL () /\ assignment_slot aug_storage_shrink_source_context st 0w = 0w /\
  assignment_slot aug_storage_shrink_source_context st 1w = 10w
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_memory_shrink_succeeds:
  FST (assignment_run aug_memory_shrink_source_context
    aug_memory_shrink_source_program assignment_empty_state) =
  INR (ReturnException (IntV 0))
Proof
  CONV_TAC cv_eval
QED

Theorem augmented_memory_append_overwrites_stale_slot:
  FST (assignment_run aug_memory_shrink_append_source_context
    aug_memory_shrink_append_source_program assignment_empty_state) =
  INR (ReturnException (IntV 7))
Proof
  CONV_TAC cv_eval
QED

Definition assignment_pop_argument_state_def:
  assignment_pop_argument_state =
    SND (push_scope_with_var "a" (BaseTV (UintT 256)) (IntV 5) assignment_empty_state)
End
val () = cv_auto_trans assignment_pop_argument_state_def;

Theorem assignment_pop_precedes_target_bounds_check:
  FST (assignment_run x03_assign_elem_from_pop_source_context
    x03_assign_elem_from_pop_source_program assignment_pop_argument_state) =
    INR (Error (RuntimeError "evaluate_subscripts array_index"))
Proof
  CONV_TAC cv_eval
QED
