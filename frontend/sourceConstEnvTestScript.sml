Theory sourceConstEnvTest
Ancestors
  sourceConstEnv sourceConstEnvProps sourceConstEval alist
Libs
  intLib

(* Kernel computation tests. Paths below are supplied resolved identities, not
   unresolved JSON import spellings. Aliases must already denote the same path.
   Nothing here claims an import decoder or whole-program checker connection. *)

Theorem source_const_env_forward:
  source_const_resolve []
    [(["main";"A"], SCE_Binary SCB_Add (SCE_Name ["main";"B"])
                        (SCE_Literal (SCL_Int 1)));
     (["main";"B"], SCE_Name ["main";"C"]);
     (["main";"C"], SCE_Literal (SCL_Int 41))] =
  SCEnv_Resolved
    [(["main";"C"], SC_Constant (SCV_Int 41));
     (["main";"B"], SC_Constant (SCV_Int 41));
     (["main";"A"], SC_Constant (SCV_Int 42))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_backward:
  source_const_resolve []
    [(["main";"A"], SCE_Literal (SCL_Int 7));
     (["main";"B"], SCE_Name ["main";"A"])] =
  SCEnv_Resolved
    [(["main";"A"], SC_Constant (SCV_Int 7));
     (["main";"B"], SC_Constant (SCV_Int 7))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_canonical_module_paths:
  source_const_resolve
    [(["package";"nested";"K"], SC_Constant (SCV_Int 40));
     (["main";"K"], SC_Constant (SCV_Int 2))]
    [(["main";"SUM"], SCE_Binary SCB_Add
        (SCE_Name ["package";"nested";"K"]) (SCE_Name ["main";"K"]))] =
  SCEnv_Resolved
    [(["package";"nested";"K"], SC_Constant (SCV_Int 40));
     (["main";"K"], SC_Constant (SCV_Int 2));
     (["main";"SUM"], SC_Constant (SCV_Int 42))]
Proof
  EVAL_TAC
QED

(* Distinct component sequences cannot collide through a joined spelling. *)
Theorem source_const_env_no_joined_string_collision:
  source_const_resolve []
    [(["a.b";"K"], SCE_Literal (SCL_Int 1));
     (["a";"b";"K"], SCE_Literal (SCL_Int 2))] =
  SCEnv_Resolved
    [(["a.b";"K"], SC_Constant (SCV_Int 1));
     (["a";"b";"K"], SC_Constant (SCV_Int 2))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_no_leaf_lookup:
  source_const_resolve [(["library";"K"], SC_Constant (SCV_Int 42))]
    [(["main";"A"], SCE_Name ["K"])] =
  SCEnv_Missing [(["main";"A"],["K"])]
Proof
  EVAL_TAC
QED

Theorem source_const_env_cross_module_forward:
  source_const_resolve []
    [(["main";"A"], SCE_Name ["library";"K"]);
     (["library";"K"], SCE_Literal (SCL_Int 42))] =
  SCEnv_Resolved
    [(["library";"K"], SC_Constant (SCV_Int 42));
     (["main";"A"], SC_Constant (SCV_Int 42))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_cycles:
  source_const_resolve [] [(["A"], SCE_Name ["A"])] = SCEnv_Cycle [["A"]] /\
  source_const_resolve []
    [(["A"], SCE_Name ["B"]); (["B"], SCE_Name ["A"])] =
    SCEnv_Cycle [["A"];["B"]] /\
  source_const_resolve []
    [(["D"], SCE_Name ["A"]); (["A"], SCE_Name ["B"]);
     (["B"], SCE_Name ["A"]); (["C"], SCE_Literal (SCL_Int 1))] =
    SCEnv_Cycle [["D"];["A"];["B"]]
Proof
  EVAL_TAC
QED

Theorem source_const_env_missing_before_cycle:
  source_const_resolve []
    [(["A"], SCE_Name ["A"]); (["B"], SCE_Name ["absent"])] =
  SCEnv_Missing [(["B"],["absent"])]
Proof
  EVAL_TAC
QED

Theorem source_const_env_duplicates:
  source_const_resolve []
    [(["A"], SCE_Literal (SCL_Int 1)); (["A"], SCE_Literal (SCL_Int 2))] =
    SCEnv_Duplicate [["A"];["A"]] /\
  source_const_resolve [(["A"], SC_DynamicBinding)]
    [(["A"], SCE_Literal (SCL_Int 42))] = SCEnv_Duplicate [["A"];["A"]] /\
  source_const_resolve
    [(["A"], SC_Constant (SCV_Int 1)); (["A"], SC_Constant (SCV_Int 2))] [] =
    SCEnv_Duplicate [["A"];["A"]]
Proof
  EVAL_TAC
QED

Theorem source_const_env_bad_identities:
  source_const_resolve [] [([], SCE_Literal (SCL_Int 1))] =
    SCEnv_BadIdentity [[]] /\
  source_const_resolve [(["module";""], SC_DynamicBinding)] [] =
    SCEnv_BadIdentity [["module";""]]
Proof
  EVAL_TAC
QED

Theorem source_const_env_bad_seed:
  source_const_resolve [(["A"], SC_Constant (SCV_Bytes [256]))] [] = SCEnv_BadSeed
Proof
  EVAL_TAC
QED

(* The caller records lexical resolution, including runtime/immutable names.
   Same-leaf imported constants do not turn those bindings into constants. *)
Theorem source_const_env_dynamic_not_substituted:
  source_const_resolve
    [(["main";"fn";"K"], SC_DynamicBinding);
     (["import";"K"], SC_Constant (SCV_Int 42))]
    [(["main";"A"], SCE_Name ["main";"fn";"K"])] =
    SCEnv_NotConstant ["main";"A"] /\
  source_const_resolve [(["main";"immutable"], SC_DynamicBinding)]
    [(["main";"A"], SCE_Name ["main";"immutable"])] =
    SCEnv_NotConstant ["main";"A"] /\
  source_const_resolve [] [(["A"], SCE_Dynamic)] = SCEnv_NotConstant ["A"]
Proof
  EVAL_TAC
QED

Theorem source_const_env_dynamic_dependency_not_cycle:
  source_const_resolve [(["runtime"], SC_DynamicBinding)]
    [(["A"], SCE_Name ["B"]); (["B"], SCE_Name ["runtime"])] =
    SCEnv_NotConstant ["B"]
Proof
  EVAL_TAC
QED

Theorem source_const_env_unsupported_not_cycle:
  source_const_resolve []
    [(["A"], SCE_Name ["B"]);
     (["B"], SCE_Unsupported "future" [SCE_Dynamic])] =
    SCEnv_Unsupported ["B"] (SCS_Syntax "future")
Proof
  EVAL_TAC
QED

Theorem source_const_env_invalid_not_dynamic:
  source_const_resolve []
    [(["A"], SCE_Binary SCB_Add SCE_Dynamic
      (SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                              (SCE_Literal (SCL_Int 0))))] =
    SCEnv_Invalid ["A"] SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_const_env_eager_dependencies:
  source_const_resolve []
    [(["A"], SCE_Boolean SCB_And
      [SCE_Literal (SCL_Bool F); SCE_Name ["missing"]])] =
    SCEnv_Missing [(["A"],["missing"])] /\
  source_const_resolve []
    [(["A"], SCE_Unsupported "future" [SCE_Name ["missing"]])] =
    SCEnv_Missing [(["A"],["missing"])]
Proof
  EVAL_TAC
QED

Theorem source_const_env_keyword_and_callee_dependencies:
  source_const_names
    (SCE_Call (SCE_Name ["callee"])
      [SCE_Tuple [SCE_Name ["arg"]]]
      [("flag",SCE_Unary SCU_Not (SCE_Name ["kw"]))]) =
    [["callee"];["arg"];["kw"]] /\
  source_const_names
    (SCE_Builtin SCB_MethodId [SCE_Name ["sig"]]
      [("output_type",SCE_Name ["type"])]) = [["sig"];["type"]]
Proof
  EVAL_TAC
QED

Theorem source_const_env_resolved_type_dependency:
  source_const_resolve []
    [(["T"], SCE_BytesType T (SCE_Name ["N"]));
     (["N"], SCE_Literal (SCL_Int 4))] =
    SCEnv_Resolved
      [(["N"], SC_Constant (SCV_Int 4));
       (["T"], SC_Constant (SCV_BytesType T 4))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_decimal_and_aggregate:
  source_const_resolve []
    [(["A"], SCE_List [SCE_Name ["D"]; SCE_Name ["D"]]);
     (["D"], SCE_Literal (SCL_Decimal 125 2))] =
    SCEnv_Resolved
      [(["D"], SC_Constant (SCV_Decimal 12500000000));
       (["A"], SC_Constant
          (SCV_List [SCV_Decimal 12500000000;SCV_Decimal 12500000000]))]
Proof
  EVAL_TAC
QED

Theorem source_const_env_empty_preserves_seed:
  source_const_resolve
    [(["main";"immutable"],SC_DynamicBinding);
     (["import";"K"],SC_Constant (SCV_Int 42))] [] =
    SCEnv_Resolved
      [(["main";"immutable"],SC_DynamicBinding);
       (["import";"K"],SC_Constant (SCV_Int 42))]
Proof
  EVAL_TAC
QED

(* Reject cheats, nonstandard axioms and open hypotheses in every export. *)
fun audit_env_theory thy =
  let
    val exports = DB.thms thy
    fun check (name, th) =
      let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles then ()
        else raise Fail ("source constant environment audit failed: " ^ thy ^ "." ^ name)
      end
  in
    List.app check exports;
    print ("SOURCE_CONST_ENV_KERNEL_CLOSED " ^ thy ^ " exports=" ^
           Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_env_theory
  ["sourceConstEnv", "sourceConstEnvProps", "sourceConstEnvTest"];
