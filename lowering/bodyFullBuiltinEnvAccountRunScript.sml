(* Fixed-endpoint account suffixes. *)
Theory bodyFullBuiltinEnvAccountRun
Ancestors
  exprSimAccounts bodyFullGhostFrame fragGasSeqPtr gasOutcomeFullCompose
  exprUnopSimDefs exprSimDefs exprSimHypsDefs bodyPtrDefs
  ptrSafeRun ptrDiscipline venomInst venomState
  vyperStorageTrace list finite_map compileEnv exprSimUnopProps
  vyperInterpreter vyperContext vyperTypeSystem fragGasOriginPtr
  loweringStateRelDefs accountsRelProps vyperStorageFootprint exprLoweringProps
  decoderGhostFramePtr codegenRel fragExec emitHelperProps allocaHistory

Theorem account_suffix_full_run:
 !item bs ee cx v x sa op sb func st0 cenv s ctx DF lo d G tn explicit PG.
 item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed ee.accounts /\
 unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
   (BytesV bs) ee = INL v /\
 (case item of Balance => emit_op BALANCE [x]
  | Codesize => emit_op EXTCODESIZE [x]
  | Codehash => emit_op EXTCODEHASH [x]
  | IsContract => comp_bind (emit_op EXTCODESIZE [x]) (\c. emit_op GT [c; Lit 0w])
  | Address => comp_return x | Code => comp_return x) sa = (op,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 storage_trace_domain cx st0 ee.storage_trace /\ local_ptrs_reserved cenv sa /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
 op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H ee.storage_trace ==>
 stmt_state_rel H ctx func cenv cx ee s /\
 storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s)
 ==>
 ?t G' tn'.
 ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
 t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
 alloca_history func t /\ t.vs_memory = s.vs_memory /\
 t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
 tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
 FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
 (!tv. evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
 eval_operand op t = SOME (typed_val_to_w256 tv v)) /\
 (!H. valid_horizon cx st0 H ee.storage_trace ==>
 gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
 stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `item = Address`
 >- (gvs[comp_return_def, unop_result_def, evaluate_builtin_def,
          evaluate_account_op_def, account_item_type_def] >>
     qexistsl_tac [`s`, `G`, `tn`] >>
     simp[vyperValueTheory.evaluate_type_def] >>
     rpt strip_tac >> simp[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
 `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
 `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
   metis_tac[] >>
 `!addr. (lookup_account addr s.vs_accounts).balance =
         (lookup_account addr ee.accounts).balance /\
         (lookup_account addr s.vs_accounts).code =
         (lookup_account addr ee.accounts).code /\
         (lookup_account addr s.vs_accounts).nonce =
         (lookup_account addr ee.accounts).nonce` by
   (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
    metis_tac[accounts_agree_lookup]) >>
 Cases_on `item` >> gvs[]
 >- suspend "balance"
 >- suspend "codehash"
 >- suspend "codesize"
 >> suspend "iscontract"
QED

Resume account_suffix_full_run[balance]:
 `!out. step_inst_base (mk_inst sa.cs_next_id BALANCE [x] [out]) s =
   OK (update_var out (n2w (lookup_account (word_of_bytes_be bs) ee.accounts).balance) s)` by
   (gen_tac >> simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
     venomExecSemanticsTheory.exec_read1_def, mk_inst_def,
     address_word_w2w] >> metis_tac[]) >>
 qmatch_asmsub_abbrev_tac `n2w bal : bytes32` >>
 qabbrev_tac `w = n2w bal : bytes32` >>
 qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
 qabbrev_tac `inst = mk_inst sa.cs_next_id BALANCE [x] [dst]` >>
 qabbrev_tac `u = update_var dst w s` >>
 qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
   `step_prov PG G inst u`, `step_taint inst s u tn`] >>
 `op = Var dst /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
   gvs[Abbr `dst`, emitHelperTheory.emit_op_def, comp_bind_def,
     fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
 `!p. not_fresh_at sa p ==> p <> dst` by
   (simp[Abbr `dst`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
 `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
 `!p. not_fresh_at sa p ==>
   lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
   FLOOKUP (step_prov PG G inst u) p = FLOOKUP G p /\
   op_taint (step_taint inst s u tn) (Var p) = op_taint tn (Var p)` by
   (rpt strip_tac >>
    `p <> dst` by metis_tac[] >>
    simp[Abbr `u`, Abbr `inst`, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
 `(step_taint inst s u tn).t_mem = tn.t_mem /\
  (step_taint inst s u tn).t_stor = tn.t_stor /\
  (step_taint inst s u tn).t_trans = tn.t_trans /\
  (step_taint inst s u tn).t_imm = tn.t_imm` by
   (simp[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
     new_site_bytes_def, range_bytes_def, written_taint_def,
     source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
     imm_taint_def, Abbr `u`, update_var_def, mk_inst_def,
     pred_setTheory.EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
 `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME inst` by
   (drule emitted_insts_emit_op >> strip_tac >>
    drule_all fn_has_code_same_block >> strip_tac >>
    first_x_assum (qspec_then `0` mp_tac) >>
    simp[Abbr `inst`, Abbr `dst`] >> metis_tac[]) >>
 `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
 `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
 `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
   (drule_all alloca_history_base_step >> simp[Abbr `inst`, mk_inst_def,
     is_terminator_def]) >>
 simp[] >>
 FAIL_TAC "balance result"
QED
Resume account_suffix_full_run[codehash]:
 FAIL_TAC "codehash"
QED
Resume account_suffix_full_run[codesize]:
 FAIL_TAC "codesize"
QED
Resume account_suffix_full_run[iscontract]:
 FAIL_TAC "iscontract"
QED
Finalise account_suffix_full_run
