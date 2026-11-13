(* Fixed-endpoint account suffixes. *)
Theory bodyFullBuiltinEnvAccountRun
Ancestors
  bodyFullBuiltinEnvAccountStep exprSimAccounts bodyFullGhostFrame fragGasSeqPtr gasOutcomeFullCompose
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
 op_taint tn x = {} /\ op_prov G x = NONE /\ ~ctx_has_dalloca ctx /\
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
 op_taint tn' op = {} /\ op_prov G' op = NONE /\
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
 mp_tac (account_emit_full_run |> Q.INST [`item` |-> `Balance`,
   `opc` |-> `BALANCE`, `xs` |-> `[x]`,
   `w` |-> `n2w (lookup_account (word_of_bytes_be bs) ee.accounts).balance`]) >>
 simp[] >> strip_tac >>
 qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
 gvs[unop_result_def, evaluate_builtin_def, evaluate_account_op_def,
   account_item_type_def, vyperValueTheory.evaluate_type_def,
   valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def, integer_wordTheory.i2w_def]
QED
Resume account_suffix_full_run[codehash]:
 qabbrev_tac `a = lookup_account (word_of_bytes_be bs) ee.accounts` >>
 qabbrev_tac `w = if vfmState$account_empty a then 0w else word_of_bytes T (0w:bytes32) (Keccak_256_w64 a.code)` >>
 `!out. step_inst_base (mk_inst sa.cs_next_id EXTCODEHASH [x] [out]) s =
   OK (update_var out w s)` by
   (gen_tac >> simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
     venomExecSemanticsTheory.exec_read1_def, mk_inst_def, address_word_w2w] >>
    gvs[Abbr `a`, Abbr `w`, vfmStateTheory.account_empty_def]) >>
 mp_tac (account_emit_full_run |> Q.INST [`item` |-> `Codehash`,
   `opc` |-> `EXTCODEHASH`, `xs` |-> `[x]`]) >>
 simp[] >> strip_tac >>
 qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
 gvs[unop_result_def, evaluate_builtin_def, evaluate_account_op_def,
   account_item_type_def, vyperValueTheory.evaluate_type_def,
   valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
   Abbr `a`, Abbr `w`] >>
 IF_CASES_TAC >> simp[listTheory.PAD_RIGHT, vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64,
   byteTheory.word_of_bytes_be_def,
   valueEncodingProofsTheory.word_of_bytes_replicate_zero]
QED
Resume account_suffix_full_run[codesize]:
 `!out. step_inst_base (mk_inst sa.cs_next_id EXTCODESIZE [x] [out]) s =
   OK (update_var out (n2w (LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code)) s)` by
   (gen_tac >> simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
     venomExecSemanticsTheory.exec_read1_def, mk_inst_def,
     address_word_w2w] >> metis_tac[]) >>
 mp_tac (account_emit_full_run |> Q.INST [`item` |-> `Codesize`,
   `opc` |-> `EXTCODESIZE`, `xs` |-> `[x]`,
   `w` |-> `n2w (LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code)`]) >>
 simp[] >> strip_tac >>
 qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
 gvs[unop_result_def, evaluate_builtin_def, evaluate_account_op_def,
   account_item_type_def, vyperValueTheory.evaluate_type_def,
   valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,
   integer_wordTheory.i2w_def]
QED
Resume account_suffix_full_run[iscontract]:
 qpat_x_assum `comp_bind _ _ sa = _` mp_tac >>
 simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
 rename1 `emit_op EXTCODESIZE [x] sa = (c,sm)` >>
 `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
   metis_tac[emit_op_extends_next_var] >>
 `cs_extends sm sb` by metis_tac[emit_op_extends_next_var] >>
 `fn_has_code sa sm func /\ fn_has_code sm sb func` by
   metis_tac[fn_has_code_split] >>
 qabbrev_tac `w = n2w (LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code) : bytes32` >>
 `!out. step_inst_base (mk_inst sa.cs_next_id EXTCODESIZE [x] [out]) s =
   OK (update_var out w s)` by
   (gen_tac >> simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
     venomExecSemanticsTheory.exec_read1_def, mk_inst_def,
     address_word_w2w, Abbr `w`] >> metis_tac[]) >>
 mp_tac (account_emit_full_run |> Q.INST [`item` |-> `IsContract`,
   `opc` |-> `EXTCODESIZE`, `xs` |-> `[x]`, `op` |-> `c`, `sb` |-> `sm`]) >>
 simp[] >> strip_tac >>
 `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
   (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
 `!out. step_inst_base (mk_inst sm.cs_next_id GT [c; Lit 0w] [out]) t =
   OK (update_var out (bool_to_word (w2n w > 0)) t)` by
   (simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
     venomExecSemanticsTheory.exec_pure2_def, mk_inst_def, eval_operand_def,
     wordsTheory.WORD_GREATER, wordsTheory.word_lo_def]) >>
 mp_tac (account_emit_full_run |> Q.INST [`item` |-> `IsContract`,
   `opc` |-> `GT`, `xs` |-> `[c; Lit 0w]`, `sa` |-> `sm`,
   `s` |-> `t`, `G` |-> `G'`, `tn` |-> `tn'`, `w` |-> `bool_to_word (w2n w > 0)`]) >>
 simp[Once op_taint_def] >> strip_tac >>
 qexistsl_tac [`t'`, `G''`, `tn''`] >> simp[] >>
 conj_tac >- (gvs[unop_result_def, evaluate_builtin_def, evaluate_account_op_def,
   account_item_type_def, vyperValueTheory.evaluate_type_def,
   valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def] >>
   `LENGTH (lookup_account (word_of_bytes_be bs) ee.accounts).code < dimword (:256)` by
     (fs[vyperTypeInvariantsTheory.accounts_well_typed_def, vyperTypeInvariantsTheory.account_well_typed_def,
       wordsTheory.dimword_def] >>
      qpat_x_assum `!addr. _ < _ /\ _` (qspec_then `word_of_bytes_be bs` strip_assume_tac) >> decide_tac) >>
   simp[Abbr `w`, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
     venomExecSemanticsTheory.bool_to_word_def] >>
   Cases_on `(lookup_account (word_of_bytes_be bs) ee.accounts).code` >> simp[]) >>
 rpt strip_tac >>
 qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _` drule >>
 strip_tac >> drule gas_origin_ptr_path_append >>
 simp[] >> disch_then irule >> metis_tac[]

QED
Finalise account_suffix_full_run
