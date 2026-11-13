Theory decoderIndexInitPtr
Ancestors decoderIndexInitCorePtr decoderBudgetAllocaCorePtr
  abiDecoderIndexInit abiDecoderAllocation allocationPtr typedCopyPtr fragExecPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun compileEnv context emitHelper emitHelperProps
  loweringHalt localPtrsProps exprLoweringProps venomExecSemantics venomMemProps venomState venomInst finite_map
  words list rich_list arithmetic pred_set instIdxIndep

Theorem budget_alloca_endpoint_exact_ptr[local]:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\ sa.cs_next_id IN abi_decoder_ids first last /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem DIFF {a | p <= a /\ a < p + 32} =
      tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all budget_alloca_endpoint_exact_ptr_core >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED

Theorem budget_alloca_endpoint_ptr[local]:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\ sa.cs_next_id IN abi_decoder_ids first last /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all budget_alloca_endpoint_exact_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED

Theorem abi_decode_index_init_endpoint_exact_ptr:
  abi_decode_index_init sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\
  sa.cs_next_id IN abi_decoder_ids first last /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_index_init_endpoint_exact_ptr_core >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED

Theorem abi_decode_index_init_endpoint_ptr:
  abi_decode_index_init sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\
  sa.cs_next_id IN abi_decoder_ids first last /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_index_init_endpoint_exact_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED
