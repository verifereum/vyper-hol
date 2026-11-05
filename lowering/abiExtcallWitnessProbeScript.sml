(* Full compile_expr shape audit; invariant satisfiability is separate. *)
Theory abiExtcallWitnessProbe
Ancestors
  abiExtcallWrapReachProbe exprSimHypsDefs exprLowering vyperAST compileEnv exprCallBounds

Definition witness_target_def:
  witness_target = Literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w]))
End
Definition witness_gas_def:
  witness_gas = Literal (BaseT (UintT 256)) (IntL 10000)
End
Definition witness_expr_def:
  witness_expr = Call reach_return
    (ExtCall T T ("probe",[],reach_return) [EKGas])
    [witness_target; witness_gas] NONE
End

Theorem witness_literal_types:
  well_typed_literal (BaseT AddressT) (BytesL (REPLICATE 18 0w ++ [1w;0w])) /\
  well_typed_literal (BaseT (UintT 256)) (IntL 10000)
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_target_word:
  typed_val_to_w256 (BaseTV AddressT)
    (BytesV (REPLICATE 18 0w ++ [1w;0w])) = 256w
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

Theorem witness_target_compile:
  compile_expr cenv (BaseT AddressT) witness_target st =
    (StackValue (BaseT AddressT) (Lit 256w), st)
Proof
  simp[witness_target_def, Once compile_expr_def,
       compile_literal_vv_def, witness_target_word, expr_type_def, comp_return_def]
QED

Theorem witness_gas_compile:
  compile_expr cenv (BaseT (UintT 256)) witness_gas st =
    (StackValue (BaseT (UintT 256)) (Lit 10000w), st)
Proof
  simp[witness_gas_def, Once compile_expr_def, compile_literal_vv_def] >>
  EVAL_TAC >> simp[]
QED

Theorem witness_child_bounds:
  expr_size witness_target < expr_size witness_expr /\
  expr_size witness_gas < expr_size witness_expr
Proof
  simp[witness_expr_def, expr_size_def] >> decide_tac
QED

Theorem witness_target_callback:
  expr_child_callback (expr_size witness_expr) compile_expr cenv
    (BaseT AddressT) witness_target st =
    (StackValue (BaseT AddressT) (Lit 256w),st)
Proof
  simp[expr_child_callback_def, witness_child_bounds, witness_target_compile]
QED

Theorem witness_gas_callback:
  expr_child_callback (expr_size witness_expr) compile_expr cenv
    (BaseT (UintT 256)) witness_gas st =
    (StackValue (BaseT (UintT 256)) (Lit 10000w),st)
Proof
  simp[expr_child_callback_def, witness_child_bounds, witness_gas_compile]
QED

(* Pending shape lemma: direct evaluation exceeds tactic budget on address BytesL.
Theorem witness_compile_shape:
  compile_expr reach_cenv reach_return witness_expr wrap_probe_start =
    (LocatedValue reach_return (mk_ptr (FST reach_compile) LocMemory),
     SND reach_compile)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``compile_external_call_kwargs``, ``function_selector``]) >> simp[]
QED
*)

(* Remaining full witness specification / premise table.
   Frozen theorem instantiation:
     nocalls=T, ann=reach_return, is_static=T, skip=T,
     sig=("probe",[],reach_return), opts=[EKGas],
     args=[witness_target;witness_gas], dflt=NONE.
   Simulation entry: ty=reach_return, sa=wrap_probe_start,
     (vv,sb)=compile_expr result in witness_compile_shape.
   Candidate cx: empty_evaluation_context with txn.block_number=1 and
     sources=[(0w,[(NONE,[])])], layouts=[(0w,(FEMPTY,FEMPTY))].
   Candidate es: empty_state with scopes=[], outcomes=SOME[reach_outcome].
   Candidate env: artifact_env empty_contract_type_artifact [(NONE,[])] NONE.
   Candidate cenv: all variable/global/type maps empty, module=NONE,
     ce_is_ctor=F, ce_struct_fields=FEMPTY, selector field exactly
     (\name tys. w2n(calldata_method_id(function_selector name
                             (vyper_to_abi_types FEMPTY tys)))).
   Do NOT use reach_cenv's ARB fields as invariant satisfaction evidence.
   Candidate s0: init_venom_state entry, outcomes=[reach_outcome], with
     call/transaction/block contexts matching cx.txn via call_ctx_rel.
   Candidate func: compiled blocks followed by current block with STOP tail;
     function metadata/parameters/return fields fixed empty as appropriate.
   Exact missing goals (none inferred from shape computation):
   - exprs_case T ctx func cenv cx [witness_target] and [witness_gas].
     Exported compile_literal_case_sim : expr_ok cenv (Literal ann l)
     (exprSimLeaves) plus expr_sim_pre from expr_body_pre for no internal
     calls supplies both. It is inherited admitted source, not new proof.
     results_case [] is definitional, as are the two gated list slices.
   - expr_body_pre: expr_sim_inv below; well_typed_expr env witness_expr;
     byte_widths_expr; alloc_limits_expr; call_evaluation_safe [];
     ~expr_has_evm_run; no call_operands_effect_root; internal calls=[];
     ABI-target occurrence premise vacuous for this extcall/no TypeBuiltin;
     dynamic type implication follows equal empty type environments.
   - expr_sim_inv: env_consistent, state_well_typed, accounts_well_typed,
     context_well_typed, functions_well_typed; local var representation/type
     clauses vacuous; flag clauses vacuous; selector equality by definition;
     sfields_tenv_consistent and structure clause empty; outcome accounts
     typed and return length32<2^256; IS_SOME outcomes; contract storage
     wellformed/layout safe/oracle_storage_ok for empty layouts/globals;
     module var and popped history clauses empty; place-map agreement and
     immutable bounds vacuous with empty env maps.
   - Simulation entry: fn_has_code and fn_inst_ids_distinct including STOP's
     fresh id; local_ptrs_reserved empty; gas_admissible source; stmt_state_rel
     including stack/local pointers, accounts/storage/transient/immutables,
     logs, matching call context, nonstatic outer frame, oracle queue and
     empty requests/deletions; s0 not halted and entry/index0.
   - Source run for EVERY gas_obs suffix must yield Error(RuntimeError
     "abi_decode invalid"); source target literal must be accepted by
     typing as AddressT (verify, do not assume IntL is legal for AddressT).
   - Target full run must Halt after STOP with malformed return consumed;
     identify all-count Abort exclusion via gas_path_exit/fuel_mono.
     tops=[] excludes exemption, as audited in abiExtcallErrorPostProbe.
   The above are explicit construction goals, not proved preconditions.
   The actual compile_expr adds no instructions before reach_compile: the
   target and explicit gas are immediate words, so IDs and ALLOCA base are
   exactly those from the checked helper trace. *)
