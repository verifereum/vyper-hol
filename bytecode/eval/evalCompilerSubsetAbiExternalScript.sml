(*
 * Compiler subset fixtures for external ABI values.
 *
 * The program terms are copied verbatim from the TASK_090 candidate audit.
 *)

Theory evalCompilerSubsetAbiExternal
Ancestors evalCompiler

(* Hand-written HOL input paired with sources/external_scalars.vy. *)
Definition task090_external_scalars_program_def:
  task090_external_scalars_program =
    [FunctionDecl External Pure F F "scalar_roundtrip"
       [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT);
        ("owner", BaseT AddressT); ("tag", BaseT (BytesT (Fixed 4)))]
       ([] : expr list)
       (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                BaseT (BytesT (Fixed 4))])
       [Return (SOME
          (Builtin
             (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                      BaseT (BytesT (Fixed 4))])
             (MakeArray NONE (Fixed 4))
             [Name (BaseT (IntT 128)) "delta";
              Name (BaseT BoolT) "enabled";
              Name (BaseT AddressT) "owner";
              Name (BaseT (BytesT (Fixed 4))) "tag"]))];
     FunctionDecl External Pure F F "tuple_roundtrip"
       [("item",
         TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                 BaseT (BytesT (Fixed 4))])]
       ([] : expr list)
       (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                BaseT (BytesT (Fixed 4))])
       [Return (SOME
          (Name
             (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                      BaseT (BytesT (Fixed 4))]) "item"))]]
End

(* Hand-written HOL input paired with sources/external_dynamic.vy. *)
Definition task090_external_dynamic_program_def:
  task090_external_dynamic_program =
    [FunctionDecl External Pure F F "dynamic_roundtrip"
       [("text", BaseT (StringT 16));
        ("data", BaseT (BytesT (Dynamic 16)))]
       ([] : expr list)
       (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
       [Return (SOME
          (Builtin
             (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
             (MakeArray NONE (Fixed 2))
             [Name (BaseT (StringT 16)) "text";
              Name (BaseT (BytesT (Dynamic 16))) "data"]))]]
End

(* Hand-written HOL input paired with sources/external_arrays.vy. *)
Definition task090_external_arrays_program_def:
  task090_external_arrays_program =
    [FunctionDecl External Pure F F "fixed_roundtrip"
       [("values", ArrayT (BaseT (IntT 128)) (Fixed 3))]
       ([] : expr list) (ArrayT (BaseT (IntT 128)) (Fixed 3))
       [Return (SOME
          (Name (ArrayT (BaseT (IntT 128)) (Fixed 3)) "values"))];
     FunctionDecl External Pure F F "dynamic_roundtrip"
       [("values", ArrayT (BaseT (BytesT (Fixed 4))) (Dynamic 3))]
       ([] : expr list)
       (ArrayT (BaseT (BytesT (Fixed 4))) (Dynamic 3))
       [Return (SOME
          (Name (ArrayT (BaseT (BytesT (Fixed 4))) (Dynamic 3))
             "values"))]]
End

(* Hand-written HOL input paired with sources/external_struct.vy. *)
Definition task090_external_struct_program_def:
  task090_external_struct_program =
    [StructDecl "Record"
       [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT);
        ("owner", BaseT AddressT); ("tag", BaseT (BytesT (Fixed 4)))];
     FunctionDecl External Pure F F "record_roundtrip"
       [("item", StructT (NONE, "Record"))]
       ([] : expr list) (StructT (NONE, "Record"))
       [Return (SOME (Name (StructT (NONE, "Record")) "item"))]]
End
