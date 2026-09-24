(*
 * Compiler subset fixtures for interface calls and value sending.
 *
 * The program terms are copied verbatim from the TASK_090 candidate audit.
 *)

Theory evalCompilerSubsetAbiExternalCalls
Ancestors evalCompiler

(* Hand-written HOL input paired with sources/interface_calls.vy. *)
Definition task090_interface_calls_program_def:
  task090_interface_calls_program =
    [InterfaceDecl "Peer"
       [("inspect",
         [("delta", BaseT (IntT 128)); ("enabled", BaseT BoolT)],
         TupleT [BaseT (IntT 128); BaseT BoolT], View);
        ("update", [("x", BaseT (UintT 256))], BaseT BoolT, Payable)];
     FunctionDecl External View F F "query_peer"
       [("target", BaseT AddressT); ("delta", BaseT (IntT 128));
        ("enabled", BaseT BoolT)]
       ([] : expr list) (TupleT [BaseT (IntT 128); BaseT BoolT])
       [Return (SOME
          (Call (TupleT [BaseT (IntT 128); BaseT BoolT])
             (ExtCall T
                ("inspect", [BaseT (IntT 128); BaseT BoolT],
                 TupleT [BaseT (IntT 128); BaseT BoolT]))
             [Name (BaseT AddressT) "target";
              Name (BaseT (IntT 128)) "delta";
              Name (BaseT BoolT) "enabled"] NONE))];
     FunctionDecl External Payable F F "update_peer"
       [("target", BaseT AddressT); ("x", BaseT (UintT 256))]
       ([] : expr list) (BaseT BoolT)
       [Return (SOME
          (Call (BaseT BoolT)
             (ExtCall F ("update", [BaseT (UintT 256)], BaseT BoolT))
             [Name (BaseT AddressT) "target";
              Builtin (BaseT (UintT 256)) (Env ValueSent) [];
              Name (BaseT (UintT 256)) "x"] NONE))]]
End

(* Hand-written HOL input paired with sources/send_value.vy. *)
Definition task090_send_value_program_def:
  task090_send_value_program =
    [FunctionDecl External Payable F F "forward_value"
       [("recipient", BaseT AddressT); ("amount", BaseT (UintT 256))]
       ([] : expr list) NoneT
       [Expr
          (Call NoneT Send
             [Name (BaseT AddressT) "recipient";
              Name (BaseT (UintT 256)) "amount"] NONE)]]
End
