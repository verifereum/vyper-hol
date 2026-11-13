(*
 * Compiler subset fixtures for supported internal-call ABI return shapes.
 *
 * The program terms are copied verbatim from the TASK_090 candidate audit.
 *)

Theory evalCompilerSubsetAbiInternalCalls
Ancestors evalCompiler

(* Hand-written HOL input paired with sources/internal_tuple_call.vy. *)
Definition task090_internal_tuple_call_program_def:
  task090_internal_tuple_call_program =
    [FunctionDecl Internal Pure F F "combine"
       [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT);
        ("tag", BaseT (BytesT (Fixed 4)))]
       ([] : expr list)
       (TupleT [BaseT (IntT 128); BaseT BoolT;
                BaseT (BytesT (Fixed 4))])
       [Return (SOME
          (Builtin
             (TupleT [BaseT (IntT 128); BaseT BoolT;
                      BaseT (BytesT (Fixed 4))])
             (MakeArray NONE (Fixed 3))
             [Name (BaseT (IntT 128)) "delta";
              Name (BaseT BoolT) "enabled";
              Name (BaseT (BytesT (Fixed 4))) "tag"]))];
     FunctionDecl External Pure F F "call_combine"
       [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT);
        ("tag", BaseT (BytesT (Fixed 4)))]
       ([] : expr list)
       (TupleT [BaseT (IntT 128); BaseT BoolT;
                BaseT (BytesT (Fixed 4))])
       [Return (SOME
          (Call
             (TupleT [BaseT (IntT 128); BaseT BoolT;
                      BaseT (BytesT (Fixed 4))])
             (IntCall (NONE, "combine"))
             [Name (BaseT (IntT 128)) "delta";
              Name (BaseT BoolT) "enabled";
              Name (BaseT (BytesT (Fixed 4))) "tag"] NONE))]]
End

(* Hand-written HOL input paired with sources/internal_struct_call.vy. *)
Definition task090_internal_struct_call_program_def:
  task090_internal_struct_call_program =
    [StructDecl "Pair"
       [("left", BaseT (UintT 256));
        ("right", BaseT (BytesT (Fixed 32)))];
     FunctionDecl Internal Pure F F "build_pair"
       [("left", BaseT (UintT 256));
        ("right", BaseT (BytesT (Fixed 32)))]
       ([] : expr list) (StructT (NONE, "Pair"))
       [Return (SOME
          (StructLit (StructT (NONE, "Pair")) (NONE, "Pair")
             [("left", Name (BaseT (UintT 256)) "left");
              ("right", Name (BaseT (BytesT (Fixed 32))) "right")]))];
     FunctionDecl External Pure F F "call_build_pair"
       [("left", BaseT (UintT 256));
        ("right", BaseT (BytesT (Fixed 32)))]
       ([] : expr list) (StructT (NONE, "Pair"))
       [Return (SOME
          (Call (StructT (NONE, "Pair"))
             (IntCall (NONE, "build_pair"))
             [Name (BaseT (UintT 256)) "left";
              Name (BaseT (BytesT (Fixed 32))) "right"] NONE))]]
End

(* Hand-written HOL input paired with sources/internal_bytes_call.vy. *)
Definition task090_internal_bytes_call_program_def:
  task090_internal_bytes_call_program =
    [FunctionDecl Internal Pure F F "choose_bytes"
       [("data", BaseT (BytesT (Dynamic 16))); ("enabled", BaseT BoolT)]
       ([] : expr list) (BaseT (BytesT (Dynamic 16)))
       [If (Name (BaseT BoolT) "enabled")
          [Return (SOME
             (Name (BaseT (BytesT (Dynamic 16))) "data"))] [];
        Return (SOME
          (Literal (BaseT (BytesT (Dynamic 16))) (BytesL [])))];
     FunctionDecl External Pure F F "call_choose_bytes"
       [("data", BaseT (BytesT (Dynamic 16))); ("enabled", BaseT BoolT)]
       ([] : expr list) (BaseT (BytesT (Dynamic 16)))
       [Return (SOME
          (Call (BaseT (BytesT (Dynamic 16)))
             (IntCall (NONE, "choose_bytes"))
             [Name (BaseT (BytesT (Dynamic 16))) "data";
              Name (BaseT BoolT) "enabled"] NONE))]]
End
