Theory sourceMeaningLocationTest
Ancestors
  sourceMeaningLocationBody sourceMeaningLocationSource sourceMeaningLocationCode
  sourceMeaningLocationDefs sourceMeaningDefs sourceMeaningCode sourceMeaningConst
  sourceModuleDecl sourceModuleEnv sourceExprDefs sourceSyntax sourceResolve
  sourceConstValue sourceConstBuiltin sourceTypeDefs vyperAST vyperInterpreter
  vyperABI vyperState vyperContext vyperAbiOperand alist list finite_map words
Libs
  sourceMeaningLocationWitnessLib intLib wordsLib

open sourceMeaningLocationWitnessLib;
val scopes = ``[[
  ("xs",["xs"]);("pair",["pair"]);("i",["i"]);("j",["j"]);("flag",["flag"]);
  ("text",["text"]);("abi_encode",["$builtin";"abi_encode"]);
  ("len",["$builtin";"len"]);("keccak256",["$builtin";"keccak256"])]]``;
val table = ``[
  (["xs"],SR_Dynamic);(["pair"],SR_Dynamic);(["i"],SR_Dynamic);(["j"],SR_Dynamic);
  (["flag"],SR_Dynamic);(["text"],SR_Dynamic);
  (["$builtin";"abi_encode"],SR_Function);(["$builtin";"len"],SR_Builtin SCB_Len);
  (["$builtin";"keccak256"],SR_Builtin SCB_Keccak256)]``;
val uint = ``BaseT (UintT 256)``;
val array = ``ArrayT ^uint (Dynamic 4)``;
val pair = ``TupleT [^uint;BaseT BoolT]``;
val refs = ``[
  (["xs"],(^array,SMR_Local "xs"));(["pair"],(^pair,SMR_Local "pair"));
  (["i"],(^uint,SMR_Local "i"));(["j"],(^uint,SMR_Local "j"));
  (["flag"],(BaseT BoolT,SMR_Local "flag"));
  (["text"],(BaseT (StringT 40),SMR_Local "text"))]``;
val type_ids = ``[]: (string list # type) list``;
val constants = ``[]:(string list # source_const_binding) list``;
val tenv = ``FEMPTY:nsid |-> type_args``;
fun check name ty original runtime = let
  val (m,source) = derive refs type_ids scopes table constants ty original
  val bridge = code tenv m runtime
  val sound = MATCH_MP (CONJUNCT1(SPEC tenv source_location_code_evaluates)) bridge
  val _ = save_thm (name ^ "_original",source)
  val _ = save_thm (name ^ "_code",bridge)
  val _ = save_thm (name ^ "_all_states",sound)
  in () end;

val () = check "conditional_array_index" uint
  ``SX_Subscript (SX_Name "xs")
      (SX_IfExp (SX_Name "flag") (SX_Name "i") (SX_Name "j"))``
  ``Subscript ^uint (Name ^array "xs")
      (IfExp ^uint (Name (BaseT BoolT) "flag") (Name ^uint "i") (Name ^uint "j"))``;
val () = check "folded_tuple_index" ``BaseT BoolT``
  ``SX_Subscript (SX_Name "pair")
      (SX_Binary SCB_Add (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 1)))``
  ``Subscript (BaseT BoolT) (Name ^pair "pair") (Literal ^uint (IntL 1))``;
val () = check "dynamic_array_length" uint
  ``SX_Call (SX_Name "len") [SX_Name "xs"] []``
  ``Builtin ^uint Len [Name ^array "xs"]``;
val () = check "dynamic_keccak" ``BaseT (BytesT (Fixed 32))``
  ``SX_Call (SX_Name "keccak256") [SX_Name "text"] []``
  ``Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [Name (BaseT (StringT 40)) "text"]``;
val () = check "abi_conditional_projection" ``BaseT (BytesT (Dynamic 36))``
  ``SX_Call (SX_Name "abi_encode")
    [SX_Subscript (SX_Name "xs")
      (SX_IfExp (SX_Name "flag") (SX_Name "i") (SX_Name "j"))]
    [("ensure_tuple",SX_Literal (SCL_Bool F));
     ("method_id",SX_Literal (SCL_Bytes [222;173;190;239]))]``
  ``TypeBuiltin (BaseT (BytesT (Dynamic 36)))
    (AbiEncode F (SOME [222w;173w;190w;239w])) (TupleT [^uint])
    [Subscript ^uint (Name ^array "xs")
      (IfExp ^uint (Name (BaseT BoolT) "flag") (Name ^uint "i") (Name ^uint "j"))]``;

(* Actual cell metadata, captures and delayed reads, not a value-only model. *)
Definition source_location_capture_state_def:
  source_location_capture_state = empty_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T;
      type := ArrayTV (BaseTV BoolT) (Dynamic 2);
      value := ArrayV (DynArrayV [BoolV T;BoolV F]) |>)]
End

Theorem source_location_capture_reads_cell_type:
  !ty. FST (source_location_abi empty_evaluation_context
    (SML_Reference ty (SMR_Local "a")) source_location_capture_state) =
      INL (AbiMemory 0 0 (ArrayTV (BaseTV BoolT) (Dynamic 2)))
Proof
  gen_tac >> EVAL_TAC
QED

Theorem source_location_complex_capture_is_delayed:
  FST ((do
    args <- source_location_abis empty_evaluation_context
      [SML_Reference (ArrayT (BaseT BoolT) (Dynamic 2)) (SMR_Local "a")];
    assign_target empty_evaluation_context (BaseTargetV (ScopedVar "a") []) PopOp;
    stage_abi_operands empty_evaluation_context args
  od) source_location_capture_state) = INL [ArrayV (DynArrayV [BoolV T])]
Proof
  EVAL_TAC
QED

Definition source_location_index_state_def:
  source_location_index_state = empty_state with scopes :=
    [FEMPTY |+ ("rows", <| assignable := T;
      type := ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 2)) (Dynamic 2);
      value := ArrayV (DynArrayV
        [ArrayV (DynArrayV [BoolV T;BoolV F]);ArrayV (DynArrayV [BoolV F;BoolV T])]) |>)
      |+ ("i", <| assignable := T; type := BaseTV (UintT 256); value := IntV 1 |> )
      |+ ("flag", <| assignable := T; type := BaseTV BoolT; value := BoolV T |>)]
End

(* Mutating both the branch condition and index after capture must not replay
   either. A later write to the selected backing cell must still be observed. *)
Theorem source_location_conditional_index_captured_once:
  FST ((do
    args <- source_location_abis empty_evaluation_context
      [SML_Subscript (ArrayT (BaseT BoolT) (Dynamic 2))
        (SML_Reference (ArrayT (ArrayT (BaseT BoolT) (Dynamic 2)) (Dynamic 2)) (SMR_Local "rows"))
        (SML_If (BaseT (UintT 256))
          (SML_Reference (BaseT BoolT) (SMR_Local "flag"))
          (SML_Reference (BaseT (UintT 256)) (SMR_Local "i"))
          (SML_Core (SM_Literal (BaseT (UintT 256)) (IntL 0))))];
    assign_target empty_evaluation_context (BaseTargetV (ScopedVar "flag") []) (Replace (BoolV F));
    assign_target empty_evaluation_context (BaseTargetV (ScopedVar "i") []) (Replace (IntV 0));
    assign_target empty_evaluation_context
      (BaseTargetV (ScopedVar "rows") [ValueSubscript (IntV 1)]) PopOp;
    stage_abi_operands empty_evaluation_context args
  od) source_location_index_state) = INL [ArrayV (DynArrayV [BoolV F])]
Proof
  EVAL_TAC
QED

Theorem source_location_failed_encode_releases_captures:
  (SND (source_location_eval empty_evaluation_context
    (SML_TypeApply (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
      (TupleT [ArrayT (BaseT BoolT) (Dynamic 2);ArrayT (BaseT BoolT) (Dynamic 2)])
      [SML_Reference (ArrayT (BaseT BoolT) (Dynamic 2)) (SMR_Local "a");
       SML_Reference (ArrayT (BaseT BoolT) (Dynamic 2)) (SMR_Local "missing")])
    source_location_capture_state)).abi_memory = []
Proof
  EVAL_TAC
QED

(* Every export of the new semantic definitions, rules and proofs is audited. *)
val () = List.app (fn thy => let val exports = DB.thms thy in
  List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag(Thm.tag th)
    in if null(hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail ("source location kernel audit: " ^ thy ^ "." ^ name) end) exports;
  print("SOURCE_LOCATION_KERNEL_CLOSED " ^ thy ^ " exports=" ^
    Int.toString(List.length exports) ^ "\n") end)
  ["sourceMeaningLocationDefs","sourceMeaningLocationSource","sourceMeaningLocationCode",
   "sourceMeaningLocationBody","sourceMeaningLocationTest"];
