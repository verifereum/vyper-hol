Theory readonlyInvokeCopyFwdExecutionMemoryScalars
Ancestors
  allocaFrontierBound
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdValues o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadPtrDiscipline o1LowerDloadGhost o1LowerDloadRelocationKernel
  frameRelocationGuardedValues
  internalReturnCopyFwdSim ptrDiscipline pointerConfinedDefs memLocDefs frameViewFacts
  venomExecProps venomState finite_map list pred_set

Theorem ricf_execution_nonaddress_no_provenance:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE;RET;RETFMP;DRET] /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     fs[MEM] >> gvs[ptr_use_ok_def] >> metis_tac[]) >>
  simp[]
QED

Theorem ricf_execution_nonaddress_value:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE;RET;RETFMP;DRET] /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint rt op) x y
Proof
  strip_tac >>
  `op_prov G op = NONE` by
    metis_tac[ricf_execution_nonaddress_no_provenance] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `!name. op = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[is_pointer_preserving_op_def]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_opaque_frame_operand >> strip_tac >>
  qexists_tac `y` >>
  gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def]
QED

Theorem ricf_execution_nonaddress_operand:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\ op_taint rt op = {} /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE;RET;RETFMP;DRET] /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >> drule_all ricf_execution_nonaddress_value >> strip_tac >>
  gvs[] >> metis_tac[word_agree_except_empty]
QED
