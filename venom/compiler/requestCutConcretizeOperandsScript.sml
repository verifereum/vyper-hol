Theory requestCutConcretizeOperands
Ancestors
  concretizePtrOpaqueRetpc concretizePtrReturnTransport
  concretizePtrOwnershipErasure concretizePtrValueTransport concretizePtrPrefixLedger
  concretizePtrTaintContent concretizePtrRequestHistory
  lowerDloadPtrCall ptrDiscipline memLocDefs pointerConfinedDefs venomState
  finite_map list pred_set extCallOracle

Theorem request_cut_concretize_operands:
  ptr_mixed_vars births positions TG tn fn gn s t /\
  s.vs_labels = t.vs_labels /\
  ptr_ledger_erases dyn births TG G /\ FDOM G SUBSET pv /\
  ptr_use_ok P pv i /\ taint_ok fn tn i s /\
  EVERY (ptr_nonopaque_operand fn) i.inst_operands /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  (!op. MEM op i.inst_operands ==>
    IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t) /\
    ptr_lookup_transport births positions (op_prov TG op) {}
      (eval_operand op s) (eval_operand op t)) /\
  (!op. MEM op i.inst_operands /\
    (FILTER ($= op) i.inst_operands = [op] ==>
      !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
        ops.iao_ofst <> op) ==> eval_operand op s = eval_operand op t)
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (gen_tac >> strip_tac >> CCONTR_TAC >>
     qpat_assum `taint_ok _ _ _ _` (mp_tac o CONJUNCT1 o REWRITE_RULE [taint_ok_def]) >>
     disch_then (qspec_then `op` mp_tac) >>
     qpat_assum `MEM i.inst_opcode _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
     simp[]) >>
  drule_all ptr_mixed_vars_eval_presence >> strip_tac >>
  `!op. MEM op i.inst_operands ==>
    ptr_lookup_transport births positions (op_prov TG op) {}
      (eval_operand op s) (eval_operand op t)` by
    (rpt strip_tac >>
     `ptr_nonopaque_operand fn op /\ op_taint tn op = {}` by fs[EVERY_MEM] >>
     drule_all ptr_mixed_vars_eval >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G x = NONE` >>
     Cases_on `FLOOKUP G x` >> simp[] >>
     `x IN pv` by fs[SUBSET_DEF,FLOOKUP_DEF] >>
     qpat_assum `ptr_use_ok _ _ _` (mp_tac o CONJUNCT2 o REWRITE_RULE [ptr_use_ok_def]) >>
     disch_then (qspec_then `x` mp_tac) >>
     qpat_assum `MEM i.inst_opcode _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
     fs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `op_prov TG op = NONE` by
    (drule ptr_owner_op_projection >> disch_then (qspec_then `op` mp_tac) >>
     Cases_on `op_prov TG op` >> simp[ptr_owner_erases_def, FLOOKUP_DEF]) >>
  qpat_assum `!op. MEM op i.inst_operands ==> ptr_lookup_transport _ _ _ _ _ _`
    (qspec_then `op` mp_tac) >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

Theorem request_cut_concretize_store:
  ptr_history_content tn s t ==> dload_shared_store tn tn s t
Proof
  strip_tac >> drule ptr_history_content_call_ctx >> strip_tac >>
  fs[ptr_history_content_def, ptr_taint_content_def, dload_shared_store_def,
     contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def] >>
  gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address` >>
  fs[storage_agree_except_def, word_agree_except_def]
QED
