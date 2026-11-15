Theory runtimeSymSrcReasonMessage
Ancestors
  runtimeSymSrcInterfaces stmtLowering compileEnv context stmtSimReasonExpr

(* The literal generator boundary is owned by C1.1.3; its exact contract
   is explicit below.  The fallback equation already exists in stmtSimReasonExpr. *)
Theorem runtime_sym_reason_literal:
  (!bs n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_bytelike_literal bs n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) ==>
  !n text ce s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_reason_message ce (Literal (BaseT (StringT n)) (StringL text)) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >>
  simp[compile_reason_message_def, comp_bind_def] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `!bs n s b s'. _` (drule_at (Pat `compile_bytelike_literal _ _ _ = _`)) >>
  simp[runtime_sym_value_def, base_ptr_def]
QED

Theorem runtime_sym_reason_message:
  (!bs n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_bytelike_literal bs n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e ==>
  !s v s'. runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_reason_message ce e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> Cases_on `?n text. e = Literal (BaseT (StringT n)) (StringL text)`
  >- (gvs[] >> drule runtime_sym_reason_literal >> metis_tac[]) >>
  `compile_reason_message ce e = compile_expr ce (expr_type e) e` by
    (irule compile_reason_message_expr >> gvs[]) >>
  qpat_x_assum `!bs n s b s'. _` kall_tac >>
  qpat_x_assum `~(?n text. _)` kall_tac >>
  qpat_x_assum `compile_reason_message ce e = _` SUBST1_TAC >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >> metis_tac[]
QED
