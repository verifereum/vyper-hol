Theory runtimeSymSrcStatementExitClosed
Ancestors
  runtimeSymSrcStatementExits runtimeSymSrcStatementReturns
  runtimeSymSrcStatementLogs runtimeSymSrcStatementReasons
  runtimeSymSrcInterfaces runtimeSymSrcContextTyped runtimeSymSrcContextComplete
  runtimeSymSrcContext runtimeSymSrcGeneratorContracts
  runtimeSymSrcModuleBodies runtimeSymSrcLiteralEnv runtimeSymSrcOpenValues
  stmtLowering compileEnv supportedStmts

(* ABI encoding remains the literal external contract owned by C1.1.3.5.
   All statement-local dispatch and available context primitives are closed. *)
Theorem runtime_sym_return_none_closed:
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Return NONE)
Proof
  irule runtime_sym_return_none >> metis_tac[runtime_sym_nonreentrant_unlock]
QED

Theorem runtime_sym_return_some_closed:
  runtime_sym_expr_contract tops compile_expr ce ty e /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Return (SOME e))
Proof
  strip_tac >> irule runtime_sym_return_some >> simp[] >> rpt conj_tac
  >- metis_tac[runtime_sym_nonreentrant_unlock]
  >- metis_tac[runtime_sym_alloc_buffer]
  >- metis_tac[runtime_sym_store_memory_typed]
  >- (rpt gen_tac >> strip_tac >> irule runtime_sym_external_return >>
      metis_tac[runtime_sym_alloc_buffer, runtime_sym_nonreentrant_unlock])
  >- (mp_tac runtime_sym_internal_return_from_env >>
      (impl_tac >- (conj_tac
        >- metis_tac[runtime_sym_store_memory]
        >> metis_tac[runtime_sym_nonreentrant_unlock])) >>
      simp[]) >>
  metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_raise_reason_closed:
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Raise (RaiseReason e))
Proof
  strip_tac >> irule runtime_sym_stmt_raise_reason >> simp[] >>
  conj_tac >- metis_tac[runtime_sym_unwrap_value] >>
  conj_tac >- metis_tac[runtime_sym_bytelike_literal] >>
  metis_tac[runtime_sym_alloc_buffer]
QED

Theorem runtime_sym_assert_bare_closed:
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond AssertBare)
Proof
  strip_tac >> irule runtime_sym_stmt_assert_bare >> simp[] >>
  mp_tac runtime_sym_lower_value >>
  (impl_tac >- metis_tac[runtime_sym_unwrap_value]) >>
  rewrite_tac[runtime_sym_lower_value_clause_def] >> metis_tac[]
QED

Theorem runtime_sym_assert_unreachable_closed:
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond AssertUnreachable)
Proof
  strip_tac >> irule runtime_sym_stmt_assert_unreachable >> simp[] >>
  mp_tac runtime_sym_lower_value >>
  (impl_tac >- metis_tac[runtime_sym_unwrap_value]) >>
  rewrite_tac[runtime_sym_lower_value_clause_def] >> metis_tac[]
QED

Theorem runtime_sym_assert_reason_closed:
  runtime_sym_expr_contract tops compile_expr ce (BaseT BoolT) cond /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Assert cond (AssertReason e))
Proof
  strip_tac >> irule runtime_sym_stmt_assert_reason >> simp[] >> rpt conj_tac
  >- metis_tac[runtime_sym_unwrap_value]
  >- (mp_tac runtime_sym_lower_value >>
      (impl_tac >- metis_tac[runtime_sym_unwrap_value]) >>
      rewrite_tac[runtime_sym_lower_value_clause_def] >> metis_tac[])
  >- metis_tac[runtime_sym_bytelike_literal] >>
  metis_tac[runtime_sym_alloc_buffer]
QED

Theorem runtime_sym_log_closed:
  (!e. MEM e args ==> runtime_sym_expr_contract tops compile_expr ce (expr_type e) e) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Log id args)
Proof
  strip_tac >> rewrite_tac[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  mp_tac runtime_sym_stmt_log >>
  (impl_tac >-
    (rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         drule_at (Pat `compile_materialize_vv _ _ _ _ = _`)
           runtime_sym_materialize_vv >>
         simp[runtime_sym_value_def])
     >- (mp_tac runtime_sym_lower_value >>
         (impl_tac >- metis_tac[runtime_sym_unwrap_value]) >>
         rewrite_tac[runtime_sym_lower_value_clause_def] >> metis_tac[])
     >- metis_tac[runtime_sym_encode_log_topic]
     >- metis_tac[runtime_sym_store_memory]
     >- metis_tac[runtime_sym_alloc_buffer]
     >> metis_tac[])) >>
  rewrite_tac[runtime_sym_stmt_contract_def] >>
  disch_then drule_all >> simp[]
QED
