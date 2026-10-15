(*
 * Compiler subset fixtures for static and dynamic ABI builtins.
 *
 * The program terms are copied verbatim from the TASK_090 candidate audit.
 *)

Theory evalCompilerSubsetAbiBuiltins
Ancestors evalCompiler

(* Hand-written HOL input paired with sources/abi_static.vy. *)
Definition task090_abi_static_program_def:
  task090_abi_static_program =
    [FunctionDecl External Pure F F "encode_static"
       [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT);
        ("owner", BaseT AddressT); ("tag", BaseT (BytesT (Fixed 4)))]
       ([] : expr list) (BaseT (BytesT (Dynamic 132)))
       [AnnAssign "value"
          (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                   BaseT (BytesT (Fixed 4))])
          (Builtin
             (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                      BaseT (BytesT (Fixed 4))])
             (MakeArray NONE (Fixed 4))
             [Name (BaseT (IntT 128)) "delta";
              Name (BaseT BoolT) "enabled";
              Name (BaseT AddressT) "owner";
              Name (BaseT (BytesT (Fixed 4))) "tag"]);
        Return (SOME
          (TypeBuiltin (BaseT (BytesT (Dynamic 132)))
             (AbiEncode F (SOME [222w; 173w; 190w; 239w]))
             (TupleT
                [TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                         BaseT (BytesT (Fixed 4))]])
             [Name
                (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                         BaseT (BytesT (Fixed 4))]) "value"]))];
     FunctionDecl External Pure F F "decode_static"
       [("data", BaseT (BytesT (Dynamic 128)))]
       ([] : expr list)
       (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                BaseT (BytesT (Fixed 4))])
       [Return (SOME
          (TypeBuiltin
             (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                      BaseT (BytesT (Fixed 4))])
             (AbiDecode F)
             (TupleT [BaseT (IntT 128); BaseT BoolT; BaseT AddressT;
                      BaseT (BytesT (Fixed 4))])
             [Name (BaseT (BytesT (Dynamic 128))) "data"]))]]
End

(* Hand-written HOL input paired with sources/abi_dynamic.vy. *)
Definition task090_abi_dynamic_program_def:
  task090_abi_dynamic_program =
    [FunctionDecl External Pure F F "encode_dynamic"
       [("text", BaseT (StringT 16));
        ("payload", BaseT (BytesT (Dynamic 16)))]
       ([] : expr list) (BaseT (BytesT (Dynamic 196)))
       [AnnAssign "value"
          (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
          (Builtin
             (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
             (MakeArray NONE (Fixed 2))
             [Name (BaseT (StringT 16)) "text";
              Name (BaseT (BytesT (Dynamic 16))) "payload"]);
        Return (SOME
          (TypeBuiltin (BaseT (BytesT (Dynamic 196)))
             (AbiEncode F (SOME [222w; 173w; 190w; 239w]))
             (TupleT
                [TupleT
                   [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))]])
             [Name
                (TupleT [BaseT (StringT 16);
                         BaseT (BytesT (Dynamic 16))]) "value"]))];
     FunctionDecl External Pure F F "decode_dynamic"
       [("data", BaseT (BytesT (Dynamic 192)))]
       ([] : expr list)
       (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
       [Return (SOME
          (TypeBuiltin
             (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
             (AbiDecode F)
             (TupleT [BaseT (StringT 16); BaseT (BytesT (Dynamic 16))])
             [Name (BaseT (BytesT (Dynamic 192))) "data"]))]]
End
