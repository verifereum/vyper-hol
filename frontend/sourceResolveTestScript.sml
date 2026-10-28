Theory sourceResolveTest
Ancestors
  sourceResolveProps sourceResolveModules sourceResolve sourceSyntax
  sourceConstAST sourceConstAnnotation sourceConstEnv sourceConstEval alist list
Libs
  intLib

(* Kernel-proved closed prelude expansion: do not recompute GENLIST and
   decimal type spellings at every name lookup in these regressions. *)
val () = computeLib.add_funs [EVAL ``source_resolve_prelude``];

Definition resolve_test_scope_def:
  resolve_test_scope =
    [("length",["alias";"length"]); ("m",["alias";"module"]);
     ("ByteBuffer",["alias";"Bytes"]); ("Four",["alias";"bytes4"]);
     ("N",["lib";"N"]); ("runtime",["main";"runtime"])]
End

Definition resolve_test_table_def:
  resolve_test_table =
    [(["alias";"length"],SR_Alias ["alias";"length2"]);
     (["alias";"length2"],SR_Alias ["$builtin";"len"]);
     (["$builtin";"len"],SR_Builtin SCB_Len);
     (["alias";"module"],SR_Alias ["lib"]);
     (["lib"],SR_Module); (["lib";"N"],SR_Constant);
     (["alias";"Bytes"],SR_Alias ["$builtin";"Bytes"]);
     (["$builtin";"Bytes"],SR_Bytes);
     (["alias";"bytes4"],SR_Alias ["$builtin";"bytes4"]);
     (["$builtin";"bytes4"],SR_FixedBytes 4);
     (["main";"runtime"],SR_Dynamic)]
End

Theorem resolve_aliases_and_canonical_paths:
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Call (SX_Name "length") [SX_Literal (SCL_String "abc")] []) =
      SOME (SCE_Builtin SCB_Len [SCE_Literal (SCL_String "abc")] []) /\
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Attribute (SX_Name "m") "N") = SOME (SCE_Name ["lib";"N"]) /\
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Name "runtime") = SOME SCE_Dynamic
Proof
  EVAL_TAC
QED

Theorem resolve_missing_is_not_dynamic:
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Name "missing") = NONE /\
  source_resolve_candidate [] resolve_test_table
    (SX_Call (SX_Name "len") [] []) = NONE /\
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Attribute (SX_Name "m") "missing") = NONE /\
  source_resolve_candidate [[("length",["missing"])];resolve_test_scope]
    resolve_test_table (SX_Call (SX_Name "length") [] []) = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_alias_cycles_and_missing_targets:
  source_resolve_name [[("x",["a"])]]
    [(["a"],SR_Alias ["b"]);(["b"],SR_Alias ["a"])] ["x"] = NONE /\
  source_resolve_name [[("x",["a"])]]
    [(["a"],SR_Alias ["missing"])] ["x"] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_kinds_shadow_builtins:
  source_resolve_candidate [[("length",["shadow"])];resolve_test_scope]
    ((["shadow"],SR_Function)::resolve_test_table)
    (SX_Call (SX_Name "length") [] []) =
      SOME (SCE_Call (SCE_Unsupported "function" []) [] []) /\
  source_resolve_candidate [[("length",["shadow"])];resolve_test_scope]
    ((["shadow"],SR_Dynamic)::resolve_test_table)
    (SX_Call (SX_Name "length") [] []) = SOME (SCE_Call SCE_Dynamic [] []) /\
  source_resolve_candidate [[("length",["shadow"])];resolve_test_scope]
    ((["shadow"],SR_Constant)::resolve_test_table)
    (SX_Call (SX_Name "length") [] []) = SOME (SCE_Call (SCE_Name ["shadow"]) [] []) /\
  source_resolve_candidate [[("length",["shadow"])];resolve_test_scope]
    ((["shadow"],SR_Type)::resolve_test_table)
    (SX_Call (SX_Name "length") [] []) =
      SOME (SCE_Call (SCE_Unsupported "type" []) [] []) /\
  source_resolve_candidate [[("length",["shadow"])];resolve_test_scope]
    ((["shadow"],SR_Module)::resolve_test_table)
    (SX_Call (SX_Name "length") [] []) =
      SOME (SCE_Call (SCE_Unsupported "module" []) [] [])
Proof
  EVAL_TAC
QED

Theorem resolve_only_modules_have_members:
  source_resolve_name [[("c",["c"])]]
    [(["c"],SR_Constant);(["c";"x"],SR_Constant)] ["c";"x"] = NONE /\
  source_resolve_name [[("c",["c"])]]
    [(["c"],SR_Type);(["c";"x"],SR_Builtin SCB_Len)] ["c";"x"] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_output_type_aliases:
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Call (SX_Name "length") []
      [("output_type",SX_Subscript (SX_Name "ByteBuffer") (SX_Name "N"))]) =
    SOME (SCE_Builtin SCB_Len []
      [("output_type",SCE_BytesType F (SCE_Name ["lib";"N"]))]) /\
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_Call (SX_Name "length") [] [("output_type",SX_Name "Four")]) =
    SOME (SCE_Builtin SCB_Len []
      [("output_type",SCE_BytesType T (SCE_Literal (SCL_Int 4)))]) /\
  source_resolve_candidate [resolve_test_scope] resolve_test_table (SX_Name "Four") =
    SOME (SCE_Unsupported "type" [])
Proof
  EVAL_TAC
QED

Theorem resolve_output_type_shadowing:
  source_resolve_candidate [[("Four",["local"])];resolve_test_scope]
    ((["local"],SR_Type)::resolve_test_table)
    (SX_Call (SX_Name "length") [] [("output_type",SX_Name "Four")]) =
    SOME (SCE_Builtin SCB_Len [] [("output_type",SCE_Unsupported "type" [])]) /\
  source_resolve_candidate [[("ByteBuffer",["local"])];resolve_test_scope]
    ((["local"],SR_Dynamic)::resolve_test_table)
    (SX_Call (SX_Name "length") []
      [("output_type",SX_Subscript (SX_Name "ByteBuffer") (SX_Name "N"))]) =
    SOME (SCE_Builtin SCB_Len []
      [("output_type",SCE_Subscript SCE_Dynamic (SCE_Name ["lib";"N"]))])
Proof
  EVAL_TAC
QED

Theorem resolve_full_expression_and_eager_missing:
  source_resolve_expr [resolve_test_scope] resolve_test_table F
    (SCE_Unsupported "outer"
      [SCE_Tuple [SCE_Unary SCU_Neg (SCE_Name ["m";"N"])];
       SCE_Boolean SCB_And [SCE_Literal (SCL_Bool F);SCE_Name ["runtime"]];
       SCE_Compare SCC_Eq (SCE_Name ["N"]) (SCE_Literal (SCL_Int 7))]) =
    SOME (SCE_Unsupported "outer"
      [SCE_Tuple [SCE_Unary SCU_Neg (SCE_Name ["lib";"N"])];
       SCE_Boolean SCB_And [SCE_Literal (SCL_Bool F);SCE_Dynamic];
       SCE_Compare SCC_Eq (SCE_Name ["lib";"N"]) (SCE_Literal (SCL_Int 7))]) /\
  source_resolve_expr [resolve_test_scope] resolve_test_table F
    (SCE_Boolean SCB_And [SCE_Literal (SCL_Bool F);SCE_Name ["missing"]]) = NONE /\
  source_resolve_expr [resolve_test_scope] resolve_test_table F
    (SCE_Unsupported "unsupported" [SCE_Name ["missing"]]) = NONE /\
  source_resolve_expr [resolve_test_scope] resolve_test_table F
    (SCE_Call (SCE_Name ["length"]) [] [("unused",SCE_Name ["missing"])]) = NONE /\
  source_resolve_expr [resolve_test_scope] resolve_test_table F
    (SCE_Builtin SCB_Len [] []) = NONE /\
  source_resolve_expr [resolve_test_scope] resolve_test_table T
    (SCE_BytesType T (SCE_Literal (SCL_Int 4))) = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_general_candidate_children:
  source_resolve_candidate [resolve_test_scope] resolve_test_table
    (SX_IfExp (SX_Name "runtime")
      (SX_Dict [(SX_Name "N",SX_Name "runtime")])
      (SX_Attribute (SX_Literal (SCL_Int 1)) "len")) =
    SOME (SCE_Unsupported "ifexp" [SCE_Dynamic;
      SCE_Unsupported "dict" [SCE_Name ["lib";"N"];SCE_Dynamic];
      SCE_Unsupported "attribute" [SCE_Literal (SCL_Int 1)]])
Proof
  EVAL_TAC
QED

Definition resolve_test_registry_def:
  resolve_test_registry =
    [(["main"],SourceModule
       [SD_Import [SI_Import "lib" (SOME "alias")];
        SD_Variable "M" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
          (SOME (SX_Binary SCB_Add (SX_Attribute (SX_Name "alias") "N")
            (SX_Literal (SCL_Int 1))))]);
     (["lib"],SourceModule
       [SD_Variable "N" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
         (SOME (SX_Literal (SCL_Int 7)))])]
End

Theorem resolve_registry_imported_constants:
  source_resolve_registry_constants resolve_test_registry =
    SOME (SCEnv_Resolved [(["lib";"N"],SC_Constant (SCV_Int 7));
                         (["main";"M"],SC_Constant (SCV_Int 8))])
Proof
  EVAL_TAC
QED

Theorem resolve_claims_validate_source_import_edges:
  source_resolve_claims_ok resolve_test_registry
    [SourceImportClaim ["main"] (SI_Import "lib" (SOME "alias")) ["lib"] 17] /\
  ~source_resolve_claims_ok resolve_test_registry
    [SourceImportClaim ["main"] (SI_Import "lib" (SOME "alias")) ["main"] 17] /\
  ~source_resolve_claims_ok resolve_test_registry []
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem resolve_relative_imports:
  source_resolve_import_target ["pkg";"main"]
    (SI_FromImport "" 1 "lib" (SOME "l")) = SOME ["pkg";"lib"] /\
  source_resolve_import_target ["pkg";"main"]
    (SI_FromImport "" 3 "lib" NONE) = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_duplicate_source_id_does_not_merge_modules:
  ~source_resolve_claims_ok
    [(["main"],SourceModule
      [SD_Import [SI_Import "left" NONE;SI_Import "right" NONE]]);
     (["left"],SourceModule []); (["right"],SourceModule [])]
    [SourceImportClaim ["main"] (SI_Import "left" NONE) ["left"] 5;
     SourceImportClaim ["main"] (SI_Import "right" NONE) ["right"] 5]
Proof
  EVAL_TAC
QED

Theorem resolve_registry_rejects_bad_inputs:
  source_resolve_registry_constants
    [(["x"],SourceModule []);(["x"],SourceModule [])] = NONE /\
  source_resolve_registry_constants [(["$builtin"],SourceModule [])] = NONE /\
  source_resolve_registry_constants
    [(["main"],SourceModule [SD_Import [SI_Import "missing" NONE]])] = NONE /\
  source_resolve_registry_constants [(["main"],SourceModule
    [SD_Variable "N" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"])) NONE])] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_dynamic_constant_is_rejected:
  source_resolve_registry_constants [(["main"],SourceModule
    [SD_Variable "runtime" (SCA_Name ["uint256"]) NONE;
     SD_Variable "N" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
       (SOME (SX_Name "runtime"))])] = SOME (SCEnv_NotConstant ["main";"N"])
Proof
  EVAL_TAC
QED

Theorem resolve_checked_builtin_and_primitive:
  source_resolve_module_candidate [(["main"],SourceModule [])] ["main"]
    (SX_Call (SX_Name "method_id") [SX_Literal (SCL_String "transfer(address,uint256)")]
      [("output_type",SX_Subscript (SX_Name "Bytes") (SX_Literal (SCL_Int 4)))]) =
    SOME (SCE_Builtin SCB_MethodId [SCE_Literal (SCL_String "transfer(address,uint256)")]
      [("output_type",SCE_BytesType F (SCE_Literal (SCL_Int 4)))]) /\
  source_resolve_module_candidate [(["main"],SourceModule [])] ["main"]
    (SX_Call (SX_Name "method_id") [] [("output_type",SX_Name "bytes4")]) =
    SOME (SCE_Builtin SCB_MethodId []
      [("output_type",SCE_BytesType T (SCE_Literal (SCL_Int 4)))]) /\
  source_resolve_module_candidate [(["main"],SourceModule [])] ["missing"]
    (SX_Name "len") = NONE
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem resolve_checked_source_shadowing:
  source_resolve_module_candidate [(["main"],SourceModule
    [SD_Function "len" [] [] [] NONE []])] ["main"]
    (SX_Call (SX_Name "len") [] []) =
      SOME (SCE_Call (SCE_Unsupported "function" []) [] []) /\
  source_resolve_module_candidate [(["main"],SourceModule
    [SD_Variable "len" (SCA_Name ["uint256"]) NONE])] ["main"]
    (SX_Call (SX_Name "len") [] []) = SOME (SCE_Call SCE_Dynamic [] []) /\
  source_resolve_module_candidate [(["main"],SourceModule
    [SD_Struct "bytes4" []])] ["main"]
    (SX_Call (SX_Name "method_id") [] [("output_type",SX_Name "bytes4")]) =
      SOME (SCE_Builtin SCB_MethodId [] [("output_type",SCE_Unsupported "type" [])])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem resolve_program_registry_keeps_distinct_bodies:
  source_resolve_program_registry
    (SourceProgram (SourceModule []) [SourceModule []]) [["left"];["right"]] =
    SOME [(["left"],SourceModule []);(["right"],SourceModule [])] /\
  source_resolve_program_registry
    (SourceProgram (SourceModule []) [SourceModule []]) [["same"];["same"]] = NONE /\
  source_resolve_program_registry
    (SourceProgram (SourceModule []) [SourceModule []]) [["one"]] = NONE
Proof
  rpt conj_tac >> EVAL_TAC
QED

(* Every export is kernel-closed: only standard persisted theorem tags. *)
fun audit_resolve_theory thy =
  List.app (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail ("source resolver audit failed: " ^ thy ^ "." ^ name)
    end) (DB.thms thy);
val () = List.app audit_resolve_theory
  ["sourceResolve", "sourceResolveModules", "sourceResolveProps", "sourceResolveTest"];
