(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringPrefix
Ancestors
  ctorDeployLoweringDefs o1PassContract vyperTypeContractSoundness
  vyperContext e2eDefs vyperInterpreter

Theorem deploy_prefix_abi_not_binding:
  vyper_to_abi_list FEMPTY [BaseT (UintT 256)] [IntV (-1)] =
    SOME [NumV (Num (-1))] /\
  bind_arguments FEMPTY [("x", BaseT (UintT 256))] [IntV (-1)] = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem deploy_prefix_negative_tx_typed:
  call_tx_well_typed (empty_call_txn with args := [IntV (-1)])
Proof
  simp[call_tx_well_typed_def, empty_call_txn_def]
QED

Theorem deploy_prefix_binding_error_not_exempt:
  !tops. ~unspecified_behaviour_exempt tops (RuntimeError "call bind_arguments")
Proof
  simp[unspecified_behaviour_exempt_def]
QED

Theorem deploy_prefix_negative_no_start:
  !am tx mut nr body am_c es0.
  tx.function_name = "__init__" /\ tx.args = [IntV (-1)] ==>
  ~deploy_ctor_start
    [FunctionDecl Deploy Payable F F "__init__"
       [("x", BaseT (UintT 256))] [] NoneT []]
    am tx (mut,nr,body,am_c,es0)
Proof
  simp[deploy_ctor_start_def, lookup_function_def, type_env_all_modules_def,
       type_env_def] >> EVAL_TAC >> simp[]
QED

Theorem deploy_prefix_negative_source_probe:
  let tops = [FunctionDecl Deploy Payable F F "__init__"
                [("x", BaseT (UintT 256))] [] NoneT []] in
  let tx = empty_call_txn with <|function_name := "__init__";
                                args := [IntV (-1)]|> in
  deploy_source_ok tops initial_machine_state tx /\
  (!gobs. load_contract NONE gobs initial_machine_state tx [(NONE,tops)] [] =
          INR (Error (RuntimeError "call bind_arguments")))
Proof
  EVAL_TAC >>
  simp[vyperStateTheory.find_var_decl_by_name_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
       vyperStateTheory.raise_def, COND_RAND, COND_RATOR]
QED

(* When the source fails before the constructor body (the value transfer
   into a non-payable constructor, the reentrancy lock), so does the unit:
   its payable check and lock come first too. *)
Theorem deploy_ctor_prefix_fail:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
    ?fuel. !gobs.
      deploy_venom_result_rel tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context fuel dunit.cu_context vs)
Proof
  cheat
QED
