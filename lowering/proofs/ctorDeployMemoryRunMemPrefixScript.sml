(* When the source fails before the constructor body (deploy_ctor_start has
 * no witness: the value transfer into a non-payable constructor, the
 * reentrancy lock), the unit's run is memory-safe: the payable check, the
 * immutables region, the argument decode and the lock it runs before
 * failing stay below the frontier.
 * TOP-LEVEL: deploy_ctor_prefix_fail_run_mem_safe (admitted until proved).
 *)
Theory ctorDeployMemoryRunMemPrefix
Ancestors
  ctorDeployLoweringDefs gasSummary memSafeRun venomInst
  ctorDeployMemoryRunMemPrefixPrimitive ctorDeployMemoryRunMemPrefixFrontier
  ctorDeployMemoryRunMemPrefixBytes ctorDeployMemoryRunMemPrefixDynamic

Theorem ctor_prefix_unsigned_negative_encoding[local]:
  vyper_to_abi_base (UintT 256) (vyperValue$IntV (-1)) =
    SOME (contractABI$NumV 1)
Proof
  EVAL_TAC
QED

Theorem ctor_prefix_unsigned_negative_cast[local]:
  safe_cast (BaseTV (UintT 256)) (vyperValue$IntV (-1)) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem ctor_prefix_unsigned_negative_binding[local]:
  bind_arguments tenv [("x", BaseT (UintT 256))]
    [vyperValue$IntV (-1)] = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem ctor_prefix_binding_error_not_exempt[local]:
  ~deploy_source_exempt tops
    (INR (Error (RuntimeError "call bind_arguments")))
Proof
  simp[ctorDeployDefsTheory.deploy_source_exempt_def,
       e2eDefsTheory.unspecified_behaviour_exempt_def]
QED

Theorem ctor_prefix_unsigned_positive_encoding[local]:
  vyper_to_abi_base (UintT 256) (vyperValue$IntV 1) =
    SOME (contractABI$NumV 1)
Proof
  EVAL_TAC
QED

Theorem ctor_prefix_unsigned_positive_binding[local]:
  IS_SOME (bind_arguments tenv [("x", BaseT (UintT 256))]
    [vyperValue$IntV 1])
Proof
  EVAL_TAC >> simp[]
QED

Theorem deploy_ctor_prefix_fail_run_mem_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb cf fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
