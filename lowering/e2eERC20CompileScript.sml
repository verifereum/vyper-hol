(* Concrete compilation certificate for the ERC20 lifecycle fixture. *)
Theory e2eERC20Compile
Ancestors
  compileVyper venomPipelineDriver supportedProgram concretizeMemLocDefs
  codegenReadyCompute alist integer_word
Libs
  finite_mapLib computeLib cv_transLib wordsLib intReduce

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.add_funs
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos,
   cv_eval ``function_selector "transfer" [Address; Uint 256]``];

Definition erc20_tops_def:
  erc20_tops =
    [HashMapDecl Private F "balances" (BaseT AddressT)
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
       [Assign
          (BaseTarget (SubscriptTarget
            (TopLevelNameTarget (NONE, "balances"))
            (Builtin (BaseT AddressT) (Env Sender) [])))
          (Literal (BaseT (UintT 256)) (IntL 100))];
     FunctionDecl External Nonpayable F F "transfer"
       [("to", BaseT AddressT); ("amount", BaseT (UintT 256))]
       [] (BaseT BoolT)
       [AugAssign (BaseT (UintT 256))
          (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
            (Builtin (BaseT AddressT) (Env Sender) []))
          Sub (Name (BaseT (UintT 256)) "amount");
        AugAssign (BaseT (UintT 256))
          (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
            (Name (BaseT AddressT) "to"))
          Add (Name (BaseT (UintT 256)) "amount");
        Return (SOME (Literal (BaseT BoolT) (BoolL T)))]]
End

val erc20_compile_eval =
  EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) erc20_tops``;

val (erc20_deploy_bytes, erc20_runtime_bytes) =
  pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl erc20_compile_eval)));

Definition erc20_deploy_bc_def:
  erc20_deploy_bc : word8 list = ^erc20_deploy_bytes
End

Definition erc20_runtime_bc_def:
  erc20_runtime_bc : word8 list = ^erc20_runtime_bytes
End

Theorem erc20_compile:
  compile_vyper (K SOME) (o1_policy all_capabilities) erc20_tops =
    SOME (erc20_deploy_bc, erc20_runtime_bc)
Proof
  PURE_REWRITE_TAC
    [erc20_compile_eval, erc20_deploy_bc_def, erc20_runtime_bc_def] >> REFL_TAC
QED
