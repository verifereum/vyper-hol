(* Complete account suffixes; the base frame is the operand's final frame. *)
Theory bodyPtrEnvBuiltinsAccountRuns
Ancestors
  bodyPtrEnvBuiltinsAccountSuffix bodyPtrEnvBuiltinsAccountReads
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsScalarCompose
  bodyPtrEnvBuiltinsEdges bodyPtrDefs ptrDiscipline fragGasPathPtr compileEnv exprLoweringProps
  exprSimAccounts emitHelperProps emitHelper fragExec stmtFragPtr
  venomState venomInst venomExecSemantics valueEncoding vyperValue
  vyperContext vyperTypeSystem words list exprLowering vyperTypeInvariants
  vfmState

Theorem account_iscontract_counted_run:
  emit_op EXTCODESIZE [arg] sa = (mid,sm) /\
  emit_op GT [mid; Lit 0w] sm = (op,sb) /\ fn_has_code sa sb fn /\
  LENGTH bs = 20 /\
  LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code < dimword (:256) /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn arg = {} /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel fn cenv es.scopes s /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME
      (bool_to_word ((lookup_account (word_of_bytes_be bs) es.accounts).code <> [])) /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `emit_op EXTCODESIZE _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  `MEM (Codesize,EXTCODESIZE)
     [(Balance,BALANCE); (Codesize,EXTCODESIZE); (Codehash,EXTCODEHASH)]` by simp[] >>
  `evaluate_type (get_tenv cx) (account_item_type Codesize) =
     SOME (BaseTV (UintT 256))` by simp[account_item_type_def, evaluate_type_def] >>
  drule_all account_read_counted_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[account_codesize_encoding] >>
  `step_inst_base (mk_inst sm.cs_next_id GT [mid; Lit 0w]
     [STRING #"%" (toString sm.cs_next_var)]) t =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
      (bool_to_word ((lookup_account (word_of_bytes_be bs) es.accounts).code <> [])) t)` by
    (irule account_iscontract_gt_step >> simp[]) >>
  drule_all emit_account_gt_append >> simp[]
QED

Theorem account_suffix_counted_run:
  item <> Code /\ (item = Address ==> op_prov G arg = NONE) /\
  (case item of
     Balance => emit_op BALANCE [arg]
   | Codesize => emit_op EXTCODESIZE [arg]
   | Codehash => emit_op EXTCODEHASH [arg]
   | IsContract => comp_bind (emit_op EXTCODESIZE [arg])
                    (\c. emit_op GT [c; Lit 0w])
   | Address => comp_return arg
   | Code => comp_return arg) sa = (op,sb) /\
  fn_has_code sa sb fn /\ LENGTH bs = 20 /\ accounts_well_typed es.accounts /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv /\
  op_taint tn arg = {} /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel fn cenv es.scopes s /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME (typed_val_to_w256 tv
      (evaluate_account_op item bs
        (lookup_account (word_of_bytes_be bs) es.accounts))) /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  Cases_on `item` >> gvs[]
  >~ [`comp_return`]
  >- (gvs[comp_return_def, account_item_type_def, evaluate_type_def,
           evaluate_account_op_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[Once gas_path_ptr_cases])
  >~ [`comp_bind`]
  >- (gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
      `LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code <
         dimword (:256)` by
        (gvs[accounts_well_typed_def, account_well_typed_def, dimword_def] >>
         first_x_assum (qspec_then `word_of_bytes_be bs` strip_assume_tac) >> decide_tac) >>
      drule_all account_iscontract_counted_run >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
      drule account_iscontract_encoding >> simp[]) >>
  irule account_read_counted_run >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
