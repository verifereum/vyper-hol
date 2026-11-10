(* Actual physical slot credit; the auxiliary arena is private. *)
Theory actualDecoderAllocationPtr
Ancestors actualAllocCredit decoderBudgetAllocaCorePtr abiDecoderAllocation
  pred_set arithmetic finite_map words emitHelperProps venomExecSemantics
  venomState venomInst fragExec exprLoweringProps

Theorem actual_slot_singleton_budget:
  (FLOOKUP s.vs_allocas id = NONE /\
     s.vs_alloca_next + 32 < dimword (:256)) \/
  (?p. FLOOKUP s.vs_allocas id = SOME (p,32) /\
     p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)) ==>
  ?b cap. abi_decoder_budget id (id+1) b cap s
Proof
  strip_tac
  >- (qexistsl_tac [`s.vs_alloca_next`, `32`] >>
      irule abi_decoder_budget_empty >>
      `abi_decoder_ids id (id+1) = {id}` by
        (rw[abi_decoder_ids_def, EXTENSION] >> decide_tac) >> simp[]) >>
  qexistsl_tac [`p`, `s.vs_alloca_next-p`] >>
  `abi_decoder_ids id (id+1) = {id}` by
    (rw[abi_decoder_ids_def, EXTENSION] >> decide_tac) >>
  `abi_decoder_missing id (id+1) s = {}` by
    (simp[abi_decoder_missing_def, EXTENSION, finite_mapTheory.FLOOKUP_DEF] >>
     gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  simp[abi_decoder_budget_def] >> rpt strip_tac >> gvs[]
QED

Theorem actual_alloca_endpoint_exact_ptr_core:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
      s.vs_alloca_next + 32 < dimword (:256)) \/
   (?p. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,32) /\
      p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) ==>
  ?H u q p. ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    p + 32 < dimword (:256) /\
    (case FLOOKUP s.vs_allocas sa.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem DIFF {a | p <= a /\ a < p + 32} =
      tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `?b cap. abi_decoder_budget sa.cs_next_id (sa.cs_next_id+1) b cap s` by
    (irule actual_slot_singleton_budget >> metis_tac[]) >>
  `sa.cs_next_id IN abi_decoder_ids sa.cs_next_id (sa.cs_next_id+1)` by
    simp[abi_decoder_ids_def] >>
  drule_all budget_alloca_endpoint_exact_ptr_core >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def] >>
  simp[step_inst_base_def, mk_inst_def] >>
  simp[exec_alloca_def, eval_operand_def, bind_outputs_def,
    update_var_def, lookup_var_def] >>
  strip_tac >> gvs[lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `(n2w _ : bytes32) = n2w _` mp_tac >>
  simp[n2w_11]
QED

Theorem actual_word_alloca_physical_credit:
  alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ alloca_size inst = 32 /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?p. entry = (p,32) /\ p + 32 <= s.vs_alloca_next) ==>
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\
      s.vs_alloca_next + 32 < dimword (:256)) \/
   (?p. FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32) /\
      p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[] >> irule actual_word_alloca_no_wrap >>
      gvs[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[] >>
  irule allocaFrontierBoundTheory.alloca_frontier_inv_bound >>
  metis_tac[]
QED
