Theory runtimeSymSrcAssignUpdates
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  context venomInst supportedStmts supportedStmtTraverse supportedExprs

(* Boundary ledger: target-pointer and lower_value belong to C1.1.3's
   guarded expression interfaces; binop to its expression primitives.
   These are literal selected-call contracts, not compile_stmt assumptions. *)
Theorem runtime_sym_stmt_augassign:
  (!s op loc pt s'. runtime_sym_env ce /\
    (supported_target tops bindings bt \/ supported_aug_target tops bindings bt) /\
    ~supported_target_exists is_self_code bt /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s op s'. runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce target_ty e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!x y bl el s op s'. ~is_label_operand x /\ ~is_label_operand y /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_binop bop x y target_ty bl el s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (AugAssign target_ty bt bop e)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "target")
    (CONJUNCTS_THEN2 (mk_asm "rhs") (mk_asm "binop"))) >>
  pure_rewrite_tac[runtime_sym_stmt_contract_def, supported_stmt_def,
    supported_stmt_expr_exists_def] >> rpt strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  PairCases_on `tgt_result` >>
  asm "target" (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  Cases_on `tgt_result1` >> gvs[]
  >>~- ([`emit_void INVALID [] _ = _`],
    drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[] >> strip_tac >>
  asm "rhs" drule_all >> strip_tac >>
  asm "binop" drule_all >> strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]
QED

(* Append ledger: compile_target_base is the assignment-local namespace
   boundary (discharged by the assignment join); lower_value is C1.1.3's
   guarded callback boundary. Allocation/store are C1.1.3.2 context facts;
   compile_dynarray_append is the C1.1.3 expression dynarray primitive.
   Opcode side conditions are retained literally for that primitive. *)
Theorem runtime_sym_stmt_append:
  (runtime_sym_env ce /\ supported_append_target tops target ==>
    ~is_label_operand (compile_target_base ce target)) /\
  (!t s op s'. runtime_sym_env ce /\ supported_expr tops val_e /\
    ~supported_expr_exists is_self_code val_e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t val_e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!base v ws es et st cap prim load store s u s'.
    ~is_label_operand base /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Append target val_e)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "base")
    (CONJUNCTS_THEN2 (mk_asm "value")
      (CONJUNCTS_THEN2 (mk_asm "alloc")
        (CONJUNCTS_THEN2 (mk_asm "store") (mk_asm "append"))))) >>
  pure_rewrite_tac[runtime_sym_stmt_contract_def, supported_stmt_def,
    supported_stmt_expr_exists_def] >> rpt strip_tac >> gvs[] >>
  `~is_label_operand (compile_target_base ce target)` by
    (asm "base" irule >> simp[]) >>
  `supported_expr tops val_e` by
    simp[supported_expr_def] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  asm "value" drule_all >> strip_tac >>
  Cases_on `is_word_type
    (case target_root_type ce target of SOME (ArrayT t _) => t | _ => ty)` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (asm "append" (drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      Cases_on `infer_array_location ce (target_to_expr target)` >>
      simp[load_opc_for_def, store_opc_for_def]) >>
  asm "alloc" drule_all >> strip_tac >>
  asm "store" drule_all >> strip_tac >>
  asm "append" (drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  Cases_on `infer_array_location ce (target_to_expr target)` >>
  simp[load_opc_for_def, store_opc_for_def]
QED
