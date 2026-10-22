(* Definition-interface witnesses for imported callee allocations. *)
Theory calleeMemoryWitness
Ancestors
  concretizeMemLocDefs words
Libs wordsLib

Definition witness_leaf_def:
  witness_leaf = (mk_raw_function "leaf" []) with
    fn_mems_used := [(Allocation 100,0,32); (Allocation 101,32,32)]
End

Definition witness_arm_def:
  witness_arm name = (mk_raw_function name []) with
    fn_mems_used := witness_leaf.fn_mems_used
End

Definition witness_ctx_def:
  witness_ctx = mk_venom_context
    [witness_leaf; witness_arm "left"; witness_arm "right"] (SOME "caller")
End

Definition witness_call_def:
  witness_call id name = mk_inst id INVOKE [Label name] []
End

Definition witness_zero_def:
  witness_zero = mk_raw_function "caller"
    [<| bb_label := "entry"; bb_instructions :=
       [witness_call 1 "leaf"; mk_inst 2 STOP [] []] |>]
End

Definition witness_ls_def:
  witness_ls fn =
    let cfg = cfg_analyze fn in
    context_mem_livesets 20 witness_ctx fn (bp_analyze_fuel 20 cfg fn) cfg
End

Theorem raw_function_mems_empty_Witness:
  (mk_raw_function name blocks).fn_mems_used = []
Proof
  simp[venomInstTheory.mk_raw_function_def]
QED

Theorem diamond_identity_Witness:
  imported_mems_used witness_ctx
    (mk_raw_function "diamond"
      [<| bb_label := "entry"; bb_instructions :=
        [witness_call 1 "left"; witness_call 2 "right"] |>]) =
    [(Allocation 100,0,32); (Allocation 101,32,32)]
Proof
  EVAL_TAC
QED

Theorem zero_local_import_Witness:
  imported_liveset_info (imported_mems_used witness_ctx witness_zero)
    (witness_ls witness_zero) =
  [(Allocation 100,[("entry",0)],0,32);
   (Allocation 101,[("entry",0)],32,32)]
Proof
  EVAL_TAC
QED

Definition witness_one_def:
  witness_one = mk_raw_function "caller"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 3 ALLOCA [Lit (32w:256 word)] ["ptr"];
       mk_inst 4 MSTORE [Var "ptr"; Lit 1w] [];
       witness_call 5 "leaf";
       mk_inst 6 MLOAD [Var "ptr"] ["out"];
       mk_inst 7 STOP [] []] |>]
End

Theorem one_local_import_Witness:
  FLOOKUP (witness_ls witness_one) (Allocation 100) =
    SOME [("entry",2)] /\
  context_alloca_size witness_one
    (imported_mems_used witness_ctx witness_one) (Allocation 3) = 32
Proof
  EVAL_TAC
QED

Definition witness_loop_def:
  witness_loop = mk_raw_function "caller"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 10 JMP [Label "loop"] []] |>;
     <| bb_label := "loop"; bb_instructions :=
         [witness_call 11 "leaf";
          mk_inst 12 JNZ [Lit 1w; Label "loop"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions :=
         [mk_inst 13 STOP [] []] |>]
End

Theorem loop_import_liveness_Witness:
  FLOOKUP (witness_ls witness_loop) (Allocation 100) =
    SOME [("loop",0); ("loop",1)]
Proof
  EVAL_TAC
QED

(* The immediate callee can already carry allocations imported from its own
   callees: collection must retain them even if it has no local ALLOCAs. *)
Theorem transitive_chain_Witness:
  imported_mems_used witness_ctx
    (mk_raw_function "caller"
      [<| bb_label := "entry"; bb_instructions :=
          [witness_call 1 "left"] |>]) = witness_leaf.fn_mems_used /\
  context_alloca_size witness_zero witness_leaf.fn_mems_used
    (Allocation 101) = 32
Proof
  EVAL_TAC
QED

Theorem absent_liveset_keeps_metadata_Witness:
  imported_liveset_info witness_leaf.fn_mems_used
    (FEMPTY |+ (Allocation 100,[("entry",0)])) =
      [(Allocation 100,[("entry",0)],0,32)] /\
  LENGTH witness_leaf.fn_mems_used = 2
Proof
  EVAL_TAC
QED
