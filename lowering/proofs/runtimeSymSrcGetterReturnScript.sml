Theory runtimeSymSrcGetterReturn
Ancestors
  runtimeSymSrcStatementReturns runtimeSymSrcModuleBodies
  runtimeSymSrcContextTyped runtimeSymSrcContextComplete runtimeSymSrcContext
  runtimeSymSrcOpenValues runtimeSymSrcLiteralEnv runtimeSymSrcInterfaces
  runtimeSymSrcEmission
  stmtLowering exprLowering moduleLowering compileEnv context venomInst list
  stackPlanTypes emitHelper loweringShapeDefs

(* Raw safety deliberately has no supported-syntax premise. *)
Theorem runtime_sym_return_some_raw[local]:
  (!s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_stmt ce lc ty (Return (SOME e)) s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ce` |-> `ce`, `e` |-> `e`,
    `ty` |-> `ty`, `lc` |-> `lc`] runtime_sym_return_some_step) >>
  impl_tac
  >- (rpt conj_tac
      >- FIRST_ASSUM ACCEPT_TAC
      >- metis_tac[runtime_sym_unwrap_value]
      >- (match_mp_tac runtime_sym_internal_return_from_env >>
          metis_tac[runtime_sym_store_memory, runtime_sym_nonreentrant_unlock])
      >- (match_mp_tac runtime_sym_external_return >>
          metis_tac[runtime_sym_nonreentrant_unlock, runtime_sym_alloc_buffer])
      >- metis_tac[runtime_sym_alloc_buffer]
      >- metis_tac[runtime_sym_store_memory_typed]
      >> metis_tac[runtime_sym_nonreentrant_unlock]) >>
  disch_then ACCEPT_TAC
QED

Theorem runtime_sym_single_return_raw:
  (!s v s'. runtime_sym_env tops ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_expr ce ty e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
  (!b v info s op s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf b v info s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !s u s'. runtime_sym_env tops ce /\ runtime_sym_loop lc /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_stmts ce lc ty [Return (SOME e)] s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >- (simp[comp_return_def] >> metis_tac[]) >>
  simp[declare_stmt_local_def, comp_bind_def, comp_return_def] >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmts _ _ _ [] _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_return_def] >> strip_tac >> gvs[] >>
  mp_tac runtime_sym_return_some_raw >>
  (impl_tac >- (conj_tac
    >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
    first_assum ACCEPT_TAC)) >>
  disch_then drule_all >> simp[]
QED
