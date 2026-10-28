Theory sourceMeaningTest
Ancestors
  sourceMeaningRuntime sourceMeaningEffects sourceMeaningElaborate sourceMeaningCode
  sourceMeaningDefs sourceMeaningConst sourceExprElaborate sourceExprDefs
  sourceConstEval sourceConstValue sourceResolve sourceSyntax
  vyperInterpreter vyperState vyperAST vyperValue vyperValueOperation vyperTypeSystem finite_map alist
Libs
  intLib wordsLib

Definition source_meaning_test_types_def:
  source_meaning_test_types = [(["x"],BaseT (UintT 256))]
End
Definition source_meaning_test_scopes_def:
  source_meaning_test_scopes = [[("x",["x"])]]
End
Definition source_meaning_test_table_def:
  source_meaning_test_table = [(["x"],SR_Dynamic)]
End
Definition source_meaning_test_bindings_def:
  source_meaning_test_bindings = [(["x"],SE_Runtime (Name (BaseT (UintT 256)) "x"))]
End
Definition source_meaning_test_env_def:
  source_meaning_test_env env = env with <|
    type_defs := FEMPTY; var_types := FEMPTY |+ ("x",BaseT (UintT 256)) |>
End
Definition source_meaning_test_original_def:
  source_meaning_test_original = SX_Binary SCB_Pow (SX_Name "x")
    (SX_Binary SCB_Add (SX_Literal (SCL_Int 1)) (SX_Literal (SCL_Int 2)))
End
Definition source_meaning_test_meaning_def:
  source_meaning_test_meaning = SM_Binary (BaseT (UintT 256)) SCB_Pow
    (SM_Name (BaseT (UintT 256)) ["x"])
    (SM_Literal (BaseT (UintT 256)) (IntL 3))
End
Definition source_meaning_test_code_def:
  source_meaning_test_code = Builtin (BaseT (UintT 256)) (Bop Exp)
    [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)]
End

(* Nonvacuity: the independent source derivation normalizes the constant
   exponent before applying the runtime operation to the dynamic base. *)
Theorem source_meaning_staged_power_source:
  source_meaning_source source_meaning_test_types source_meaning_test_scopes
    source_meaning_test_table [] (BaseT (UintT 256))
    source_meaning_test_original source_meaning_test_meaning
Proof
  simp[source_meaning_test_original_def, source_meaning_test_meaning_def] >>
  irule sourceMeaningDefsTheory.binary >> simp[] >> rpt conj_tac
  >- EVAL_TAC
  >- (EVAL_TAC >> simp[] >> EVAL_TAC)
  >- (irule sourceMeaningDefsTheory.name >> simp[source_expr_path_def] >>
      EVAL_TAC >> simp[] >> EVAL_TAC)
  >> irule sourceMeaningDefsTheory.constant >> qexists_tac `SCV_Int 3` >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem source_meaning_staged_power_build:
  source_expr_elaborate 6 (source_meaning_test_env env)
    source_meaning_test_scopes source_meaning_test_table []
    source_meaning_test_bindings (BaseT (UintT 256)) source_meaning_test_original =
  SC_Value source_meaning_test_code
Proof
  EVAL_TAC
QED

Theorem source_meaning_staged_power_sound:
  get_tenv cx = FEMPTY ==>
  !st. eval_expr cx source_meaning_test_code st =
    source_meaning_eval cx (\path. source_meaning_local "x") source_meaning_test_meaning st
Proof
  strip_tac >>
  assume_tac source_meaning_staged_power_source >>
  assume_tac (Q.INST [`env` |-> `ARB`] source_meaning_staged_power_build) >>
  `source_meaning_binding_types source_meaning_test_types source_meaning_test_bindings` by
    rw[source_meaning_binding_types_def, source_meaning_test_types_def,
       source_meaning_test_bindings_def, AllCaseEqs(), expr_type_def] >>
  `get_tenv cx = (source_meaning_test_env ARB).type_defs` by
    simp[source_meaning_test_env_def] >>
  `!path code. ALOOKUP source_meaning_test_bindings path = SOME (SE_Runtime code) ==>
    eval_expr cx code = (\path. source_meaning_local "x") path` by
    (rw[source_meaning_test_bindings_def, AllCaseEqs()] >>
     simp[source_meaning_local_agreement]) >>
  drule_all source_meaning_elaboration_sound >> simp[]
QED

Theorem source_meaning_eager_error_and_unbounded_stage:
  source_meaning_const []
    (SCE_Binary SCB_Add SCE_Dynamic
      (SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 0)))) =
    SC_Invalid SCErr_ZeroDivisor /\
  source_meaning_const []
    (SCE_Binary SCB_RShift
      (SCE_Binary SCB_LShift (SCE_Literal (SCL_Int 1)) (SCE_Literal (SCL_Int 256)))
      (SCE_Literal (SCL_Int 255))) = SC_Value (SCV_Int 2)
Proof
  EVAL_TAC
QED

(* The raw_revert source rule resolves a declaration identity, not its spelling.
   This is additional to the code simulation theorem covering its exact state. *)
Theorem source_meaning_effect_source:
  source_meaning_revert_source [] [[("boom",["R"])]] [(["R"],SR_Function)] []
    [(["R"],SE_RawRevert)] (SX_Name "boom") (SX_Literal (SCL_Bytes [65]))
    (BaseT (BytesT (Dynamic 1))) (SM_Literal (BaseT (BytesT (Dynamic 1))) (BytesL [65w]))
Proof
  simp[source_meaning_revert_source_def] >> conj_tac
  >- (qexists_tac `["boom"]` >> EVAL_TAC) >>
  irule sourceMeaningDefsTheory.constant >> qexists_tac `SCV_Bytes [65]` >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

val source_meaning_exists_equal = save_thm ("source_meaning_exists_equal",
  CONV_RULE (DEPTH_CONV ETA_CONV)
    (prove (``?(x:'a). y = x``, qexists_tac `y` >> simp[])));

Theorem source_meaning_effect_build:
  source_expr_elaborate 4 (source_meaning_test_env env)
    [[("boom",["R"])]] [(["R"],SR_Function)] []
    [(["R"],SE_Intrinsic SE_RawRevert)] NoneT
    (SX_Call (SX_Name "boom") [SX_Literal (SCL_Bytes [65])] []) =
  SC_Value (Call NoneT RawRevert
    [Literal (BaseT (BytesT (Dynamic 1))) (BytesL [65w])] NONE)
Proof
  EVAL_TAC >> simp[source_meaning_exists_equal] >> EVAL_TAC >>
  simp[source_meaning_exists_equal]
QED

Theorem source_meaning_effect_result:
  !cx meanings st.
    source_meaning_eval cx meanings
      (SM_Revert NoneT (SM_Literal (BaseT (BytesT (Dynamic 1))) (BytesL [65w]))) st =
    (INR (Error (RuntimeError "raw_revert")),st)
Proof
  simp[source_meaning_eval_def, source_meaning_args_def, bind_def, return_def,
       evaluate_literal_def, materialise_def, type_check_def, assert_def, raise_def,
       ignore_bind_def]
QED

Theorem source_meaning_conditional_skips_effect:
  !cx meanings st.
    source_meaning_eval cx meanings
      (SM_If (BaseT BoolT) (SM_Literal (BaseT BoolT) (BoolL F))
        (SM_Revert (BaseT BoolT) (SM_Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])))
        (SM_Literal (BaseT BoolT) (BoolL T))) st = (INL (Value (BoolV T)),st)
Proof
  simp[source_meaning_eval_def, bind_def, return_def, evaluate_literal_def, switch_BoolV_def]
QED

(* Fail the target if ANY exported definition/theorem has an axiom, open
   hypothesis or non-DISK_THM oracle tag. This also checks the rule packages. *)
fun audit_source_meaning thy =
  let
    fun check (name,th) =
      let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn tag => tag = "DISK_THM") oracles then ()
        else raise Fail ("source meaning kernel audit: " ^ thy ^ "." ^ name)
      end
    val exports = DB.thms thy
  in
    List.app check exports;
    print ("SOURCE_MEANING_KERNEL_CLOSED " ^ thy ^ " exports=" ^
      Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_source_meaning
  ["sourceMeaningConst", "sourceMeaningDefs", "sourceMeaningCode",
   "sourceMeaningElaborate", "sourceMeaningEffects", "sourceMeaningRuntime", "sourceMeaningTest"];
