Theory sourceMeaningAggregateTest
Ancestors
  sourceMeaningAggregateExample sourceMeaningModules sourceMeaningPolicy sourceMeaningCall
  sourceMeaningCallDefs sourceMeaningDecl sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningStmt
  sourceMeaningStmtDefs sourceMeaningRuntime sourceMeaningElaborate sourceMeaningCode
  sourceMeaningDefs sourceMeaningValue sourceMeaningConst sourceModuleDecl sourceModuleStmt
  sourceModuleEnv sourceModuleDefs sourceExprElaborate sourceExprDefs sourceResolve sourceSyntax
  sourceConstValue sourceConstEnv vyperInterpreter vyperState vyperContext vyperAST
  vyperValue vyperValueOperation vyperTypeSystem finite_map alist list
Libs
  intLib wordsLib

Definition source_meaning_aggregate_body_code_def:
  source_meaning_aggregate_body_code =
    [Return (SOME (Builtin source_meaning_aggregate_type (MakeArray NONE (Fixed 2))
      [Literal (BaseT (UintT 256)) (IntL 6);
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 6);Literal (BaseT (UintT 256)) (IntL 7)]]))]
End

Theorem source_meaning_aggregate_body_build:
  source_module_statements 8 source_meaning_aggregate_ctx source_meaning_aggregate_type
    [SS_Return (SOME (SX_Name "PAIR"))] =
    SM_Ok (source_meaning_aggregate_body_code,source_meaning_aggregate_ctx)
Proof
  rewrite_tac [source_meaning_aggregate_ctx_evaluated] >> EVAL_TAC
QED

Theorem source_meaning_aggregate_body_transport:
  get_tenv cx = FEMPTY ==>
  eval_stmts cx source_meaning_aggregate_body_code =
    source_meaning_execute cx
      [SBM_Return (SOME (SM_Constant source_meaning_aggregate_type source_meaning_aggregate_value))]
Proof
  strip_tac >> assume_tac source_meaning_aggregate_body_source >>
  assume_tac source_meaning_aggregate_body_build >>
  `get_tenv cx = source_meaning_aggregate_ctx.sm_env.type_defs` by
    (simp[source_meaning_aggregate_ctx_def, source_module_context_def,
      source_meaning_aggregate_trust_def]) >>
  `source_meaning_locals [] source_meaning_aggregate_ctx` by simp[source_meaning_locals_def] >>
  drule_all (CONJUNCT2 source_meaning_body_transport) >>
  simp[source_meaning_execute_def]
QED

Theorem source_meaning_aggregate_body_behavior:
  get_tenv cx = FEMPTY ==>
  !st. source_meaning_execute cx
      [SBM_Return (SOME (SM_Constant source_meaning_aggregate_type source_meaning_aggregate_value))] st =
    (INR (ReturnException (ArrayV (TupleV
      [IntV 6; ArrayV (make_array_value (BaseTV (UintT 256)) (Fixed 2) [IntV 6;IntV 7])]))),st)
Proof
  strip_tac >> simp[source_meaning_execute_def, source_meaning_run_def,
    source_meaning_eval_def, source_meaning_aggregate_type_def,
    source_meaning_aggregate_value_def, source_meaning_value_def,
    source_const_value_literal_def, OPT_MMAP_def, evaluate_type_def,
    lift_option_type_def, lift_option_def, bind_def, ignore_bind_def,
    return_def, raise_def, read_result_def, evaluate_literal_def]
QED

Theorem source_meaning_aggregate_global_source:
  source_meaning_declaration source_meaning_aggregate_ctx
    (SD_Variable "PAIR" (SCA_Qualified SCQ_Constant source_meaning_aggregate_annotation)
      (SOME source_meaning_aggregate_original))
    (SDM_Aggregate "PAIR" source_meaning_aggregate_type source_meaning_aggregate_value)
Proof
  simp[Once source_meaning_declaration_cases] >>
  qexists_tac `SourceTypeResolution (Type source_meaning_aggregate_type)
    [SCQ_Constant] [(SCE_Literal (SCL_Int 2),2)]` >>
  rewrite_tac [source_meaning_aggregate_ctx_evaluated] >>
  rpt conj_tac >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition source_meaning_aggregate_global_code_def:
  source_meaning_aggregate_global_code =
    case HD source_meaning_aggregate_body_code of
      Return (SOME e) => VariableDecl Private (Constant e) "PAIR" source_meaning_aggregate_type NONE
    | _ => FunctionDecl External Pure F F "impossible" [] [] NoneT []
End

Theorem source_meaning_aggregate_global_build:
  source_module_body 8 source_meaning_aggregate_ctx []
    (SD_Variable "PAIR" (SCA_Qualified SCQ_Constant source_meaning_aggregate_annotation)
      (SOME source_meaning_aggregate_original)) =
    SM_Ok [source_meaning_aggregate_global_code]
Proof
  rewrite_tac [source_meaning_aggregate_ctx_evaluated] >> EVAL_TAC
QED

Theorem source_meaning_aggregate_global_transport:
  source_meaning_decl_code FEMPTY
    (SDM_Aggregate "PAIR" source_meaning_aggregate_type source_meaning_aggregate_value)
    source_meaning_aggregate_global_code
Proof
  assume_tac source_meaning_aggregate_global_source >>
  assume_tac source_meaning_aggregate_global_build >>
  drule_all source_meaning_declaration_transport >> strip_tac >> gvs[] >>
  `source_meaning_aggregate_ctx.sm_env.type_defs = FEMPTY` by EVAL_TAC >> gvs[]
QED

Theorem source_meaning_aggregate_globals_installed:
  source_meaning_globals FEMPTY
    [SDM_Aggregate "PAIR" source_meaning_aggregate_type source_meaning_aggregate_value]
    FEMPTY = SOME (FEMPTY |+ ("PAIR",
      (TupleTV [BaseTV (UintT 256);ArrayTV (BaseTV (UintT 256)) (Fixed 2)],
       ArrayV (TupleV [IntV 6;
         ArrayV (make_array_value (BaseTV (UintT 256)) (Fixed 2) [IntV 6;IntV 7])]))))
Proof
  EVAL_TAC
QED

(* Three operands exercise recursive short circuit; the unselected local is
   absent in the runtime scope, so eager runtime evaluation would fail. *)
Definition source_meaning_boolean_original_def:
  source_meaning_boolean_original = SX_Boolean SCB_And
    [SX_Name "flag";SX_Literal (SCL_Bool T);SX_Name "tail"]
End
Definition source_meaning_boolean_terms_def:
  source_meaning_boolean_terms = source_meaning_boolean SCB_And
    [SM_Name (BaseT BoolT) ["flag"];SM_Literal (BaseT BoolT) (BoolL T);
     SM_Name (BaseT BoolT) ["tail"]]
End
Definition source_meaning_boolean_scopes_def:
  source_meaning_boolean_scopes = [[("flag",["flag"]);("tail",["tail"])]]
End
Definition source_meaning_boolean_table_def:
  source_meaning_boolean_table = [(["flag"],SR_Dynamic);(["tail"],SR_Dynamic)]
End
Definition source_meaning_boolean_types_def:
  source_meaning_boolean_types = [(["flag"],BaseT BoolT);(["tail"],BaseT BoolT)]
End
Definition source_meaning_boolean_bindings_def:
  source_meaning_boolean_bindings =
    [(["flag"],SE_Runtime (Name (BaseT BoolT) "flag"));
     (["tail"],SE_Runtime (Name (BaseT BoolT) "tail"))]
End
Definition source_meaning_boolean_env_def:
  source_meaning_boolean_env env = env with <|type_defs := FEMPTY;
    var_types := FEMPTY |+ ("flag",BaseT BoolT) |+ ("tail",BaseT BoolT)|>
End

Theorem source_meaning_boolean_source:
  source_meaning_source source_meaning_boolean_types source_meaning_boolean_scopes
    source_meaning_boolean_table [] (BaseT BoolT)
    source_meaning_boolean_original source_meaning_boolean_terms
Proof
  simp[source_meaning_boolean_original_def, source_meaning_boolean_terms_def] >>
  irule sourceMeaningDefsTheory.boolean >> simp[] >> conj_tac
  >- (rpt conj_tac
      >- (irule sourceMeaningDefsTheory.name >> simp[source_expr_path_def] >>
          EVAL_TAC >> simp[] >> EVAL_TAC)
      >- (irule sourceMeaningDefsTheory.constant >> qexists_tac `SCV_Bool T` >>
          EVAL_TAC >> simp[] >> EVAL_TAC) >>
      irule sourceMeaningDefsTheory.name >> simp[source_expr_path_def] >>
      EVAL_TAC >> simp[] >> EVAL_TAC) >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_boolean_build:
  source_expr_elaborate 8 (source_meaning_boolean_env env)
    source_meaning_boolean_scopes source_meaning_boolean_table []
    source_meaning_boolean_bindings (BaseT BoolT) source_meaning_boolean_original =
    SC_Value (source_expr_boolean_runtime SCB_And
      [Name (BaseT BoolT) "flag";Literal (BaseT BoolT) (BoolL T);Name (BaseT BoolT) "tail"])
Proof
  EVAL_TAC
QED

Theorem source_meaning_boolean_transport:
  get_tenv cx = FEMPTY ==>
  eval_expr cx (source_expr_boolean_runtime SCB_And
      [Name (BaseT BoolT) "flag";Literal (BaseT BoolT) (BoolL T);Name (BaseT BoolT) "tail"]) =
  source_meaning_eval cx (\p. source_meaning_local (LAST p)) source_meaning_boolean_terms
Proof
  strip_tac >>
  irule source_meaning_elaboration_sound_on >>
  qexistsl_tac [`source_meaning_boolean_bindings`,`[]`,`source_meaning_boolean_env ARB`,
    `8`,`source_meaning_boolean_original`,`source_meaning_boolean_scopes`,
    `source_meaning_boolean_table`,`BaseT BoolT`,`source_meaning_boolean_types`] >>
  simp[source_meaning_boolean_source, source_meaning_boolean_build,
    source_meaning_boolean_env_def] >> rpt conj_tac >>
  rw[source_meaning_binding_types_def, source_meaning_boolean_types_def,
    source_meaning_boolean_bindings_def, AllCaseEqs(), expr_type_def,
    source_meaning_local_agreement] >> simp[source_meaning_local_agreement]
QED

Theorem source_meaning_boolean_short_circuit:
  !st. source_meaning_eval cx (\p. source_meaning_local (LAST p))
    source_meaning_boolean_terms
    (st with scopes := [FEMPTY |+ ("flag",<|assignable := T; type := BaseTV BoolT;
      value := BoolV F|>)]) =
    (INL (Value (BoolV F)),
     st with scopes := [FEMPTY |+ ("flag",<|assignable := T; type := BaseTV BoolT;
      value := BoolV F|>)])
Proof
  EVAL_TAC >> simp[]
QED

Theorem source_meaning_boolean_eager_compile_error:
  source_expr_elaborate 8 (source_meaning_boolean_env env)
    source_meaning_boolean_scopes source_meaning_boolean_table []
    source_meaning_boolean_bindings (BaseT BoolT)
    (SX_Boolean SCB_And [SX_Name "flag";
      SX_Compare SCC_Eq (SX_Binary SCB_FloorDiv
        (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 0))) (SX_Literal (SCL_Int 0))]) =
  SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

fun audit thy = let
  fun check (name,th) = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in if null (hyp th) andalso null axioms andalso
      List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("aggregate source meaning audit: " ^ thy ^ "." ^ name) end
  val exports = DB.thms thy
  in List.app check exports;
    print ("SOURCE_AGGREGATE_KERNEL_CLOSED " ^ thy ^ " exports=" ^
      Int.toString (length exports) ^ "\n") end;
val () = List.app audit
  ["sourceMeaningValue","sourceMeaningDefs","sourceMeaningCode","sourceMeaningElaborate",
   "sourceMeaningRuntime","sourceMeaningCallDefs","sourceMeaningCall","sourceMeaningDecl",
   "sourceMeaningDispatch","sourceMeaningPolicy","sourceMeaningPolicyDecl","sourceMeaningModules",
   "sourceMeaningAggregateExample","sourceMeaningAggregateTest"];
