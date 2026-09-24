(*
 * Compiler subset fixture for mixed static and dynamic event ABI fields.
 *
 * The program term is copied verbatim from the TASK_090 candidate audit.
 *)

Theory evalCompilerSubsetAbiEvents
Ancestors evalCompiler

(* Hand-written HOL input paired with sources/mixed_event_types.vy. *)
Definition task090_mixed_event_types_program_def:
  task090_mixed_event_types_program =
    [EventDecl "Mixed"
       [(("owner", BaseT AddressT), T);
        (("label", BaseT (StringT 16)), T);
        (("tag", BaseT (BytesT (Fixed 4))), T);
        (("delta", BaseT (IntT 128)), F);
        (("enabled", BaseT BoolT), F);
        (("payload", BaseT (BytesT (Dynamic 16))), F)];
     FunctionDecl External Nonpayable F F "emit_mixed"
       [("owner", BaseT AddressT); ("label", BaseT (StringT 16));
        ("tag", BaseT (BytesT (Fixed 4))); ("delta", BaseT (IntT 128));
        ("enabled", BaseT BoolT);
        ("payload", BaseT (BytesT (Dynamic 16)))]
       ([] : expr list) NoneT
       [Log (NONE, "Mixed")
          [Name (BaseT AddressT) "owner";
           Name (BaseT (StringT 16)) "label";
           Name (BaseT (BytesT (Fixed 4))) "tag";
           Name (BaseT (IntT 128)) "delta";
           Name (BaseT BoolT) "enabled";
           Name (BaseT (BytesT (Dynamic 16))) "payload"]]]
End
