(* A source-derived, genuinely checked local tuple read admitted by main's
   nested-place whitelist, with the independent type boundary retained. *)
Theory sourceElaborationSupportTest
Ancestors
  sourceElaborationSupport supportedProgram supportedStmts exprLowering
  sourceExprElaborate supportedExprs supportedTypes supportedDecls supportedNames
  supportedStmtTraverse supportedExprTraverse compileVyper vyperTypeSystem integer
  sourceModuleElaborate sourceModuleDefs
  sourceModuleEnv sourceSyntax sourceConstAnnotation sourceConstAST
  vyperTypeContract vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib

Theorem source_expr_local_tuple_lowering_index:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Subscript ty (Name (TupleT ts) name) index) ==>
  literal_int_index index < LENGTH ts /\
  EL (literal_int_index index) ts = ty
Proof
  strip_tac >> drule source_expr_local_tuple_index >> strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  gvs[literal_int_index_def, integerTheory.INT_ABS]
QED

(* Checking removes the index gate, not unsupported tuple component types. *)
Theorem checked_local_tuple_unsupported_base_rejected:
  well_typed_expr env (Subscript ty (Name (TupleT ts) name) index) /\
  ~supported_place_type tops (TupleT ts) ==>
  ~supported_expr tops (Subscript ty (Name (TupleT ts) name) index)
Proof
  strip_tac >> drule checked_local_tuple_read_support >> simp[]
QED

Definition source_support_tuple_program_def:
  source_support_tuple_program = SourceProgram (SourceModule
    [SD_Function "f" [SX_Name "external"]
      [SourceArg "t" (SOME (SCA_Tuple
        [SCA_Name ["bool"]; SCA_Name ["uint256"]]))] []
      (SOME (SCA_Name ["uint256"]))
      [SS_Return (SOME (SX_Subscript (SX_Name "t")
        (SX_Binary SCB_Add (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 1)))))]] ) []
End

Definition source_support_tuple_tops_def:
  source_support_tuple_tops =
    [FunctionDecl External Nonpayable F F "f"
      [("t",TupleT [BaseT BoolT; BaseT (UintT 256)])] [] (BaseT (UintT 256))
      [Return (SOME (Subscript (BaseT (UintT 256))
        (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
        (Literal (BaseT (UintT 256)) (IntL 1))))]]
End

Definition source_support_tuple_trust_def:
  source_support_tuple_trust = <| smt_ids := [(["main"],NONE)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

val checked_tuple = sourceModuleFrontendLib.check
  {fuel=``30:num``,trust=``source_support_tuple_trust``,
   policies=``[(["main"],SourceModulePolicy F F)]``,keys=``[["main"]]``,
   program=``source_support_tuple_program``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val tuple_elaboration = save_thm ("source_support_tuple_elaboration_phase",
  #equation (#elaboration checked_tuple));
val _ = save_thm ("source_support_tuple_check_phase", #composition checked_tuple);
val tuple_checking = save_thm ("source_support_tuple_checking", #checking checked_tuple);

Theorem source_support_tuple_elaboration:
  source_module_elaborate 30 source_support_tuple_trust
    [(["main"],SourceModulePolicy F F)] [["main"]] source_support_tuple_program =
  SM_Ok (SourceRetained source_support_tuple_program [(NONE,source_support_tuple_tops)])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV tuple_elaboration)) >>
  EVAL_TAC
QED

Theorem source_support_tuple_supported:
  supported_program source_support_tuple_tops
Proof
  simp[source_support_tuple_tops_def, supported_program_def] >>
  conj_tac
  >- (simp[supported_declaration_headers_def, supported_declaration_header_def,
           supported_function_argument_def, supported_function_return_def,
           supported_place_type_def] >>
      simp[supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def,
           supported_int_width_def]) >>
  conj_tac
  >- (simp[supported_declaration_names_def, supported_function_names_def,
           supported_event_names_def, supported_function_header_names_def,
           supported_function_bindings_def] >>
      simp[supported_selectors_distinct_def, classify_functions_def,
           classify_function_def, build_selectors_def]) >>
  simp[supported_declaration_body_def, supported_function_body_def,
       supported_stmt_bindings_def, supported_function_bindings_def,
       supported_return_layout_def, supported_copy_types_def, expr_type_def] >>
  conj_tac
  >- (simp[supported_stmt_def, supported_local_tuple_read] >>
      simp[supported_place_type_def, supported_nested_type_def,
           supported_scalar_type_def, supported_word_type_def,
           supported_string_type_def, supported_int_width_def,
           supported_expr_def, supported_pure_expr_def]) >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def,
       expr_nonmain_type_root_def, supported_type_namespace_def, expr_type_def]
QED

Theorem source_support_tuple_checked_and_supported:
  source_module_elaborate 30 source_support_tuple_trust
    [(["main"],SourceModulePolicy F F)] [["main"]] source_support_tuple_program =
    SM_Ok (SourceRetained source_support_tuple_program [(NONE,source_support_tuple_tops)]) /\
  (?art. check_contract T
    [(0w:address,([]:storage_layout,[]:storage_layout))] (0w:address)
    [(NONE,source_support_tuple_tops)] = SOME art) /\
  supported_program source_support_tuple_tops
Proof
  simp[source_support_tuple_elaboration, source_support_tuple_supported] >>
  simp[source_support_tuple_tops_def, tuple_checking]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source support boundary kernel audit: " ^ name) end)
  (DB.thms "sourceElaborationSupportTest");
