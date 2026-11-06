Theory exprPtrUnwrapAllocationFrame
Ancestors
  exprPtrUnwrapAllocation allocationPtr exprSimAlloc ghostPcTransportPtr
  bufferAllocationExecution ptrDiscipline ptrSafeRun venomState venomInst
  exprLoweringProps finite_map words exprPtrUnwrapAllocSeparation loweringPosts

(* u is the unadvanced ALLOCA endpoint; k is the counted endpoint's cursor. *)
Theorem unwrap_alloc_output_coverage:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u ==>
  ptr_covers
    (step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u)
    (step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
    out (u with vs_inst_idx := k) nb
Proof
  strip_tac >> simp[] >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  gvs[] >> irule alloca_step_ptr_covers >> metis_tac[]
QED

Theorem unwrap_alloc_old_coverage:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
  p <> out /\ ptr_covers G tn p s sz ==>
  ptr_covers
    (step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u)
    (step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
    p (u with vs_inst_idx := k) sz
Proof
  strip_tac >> simp[] >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  gvs[] >> irule alloca_step_old_ptr_covers >> metis_tac[]
QED

Theorem unwrap_alloc_taint_frame:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w nb)] [out]) (fn_insts func) /\
  nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK u ==>
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s u tn).t_imm = tn.t_imm /\
  (!i. (i < buffer_allocation_base s id \/ buffer_allocation_base s id + nb <= i) ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s u tn).t_mem <=>
     i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[buffer_allocation_base_def] >> rpt strip_tac >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >> simp[]
QED

Theorem unwrap_alloc_runtime_frame:
  u = update_var out (n2w (buffer_allocation_base s id))
        (buffer_allocation_fields s id nb) ==>
  (u with vs_inst_idx := k).vs_memory = s.vs_memory /\
  (u with vs_inst_idx := k).vs_accounts = s.vs_accounts /\
  (u with vs_inst_idx := k).vs_transient = s.vs_transient /\
  (u with vs_inst_idx := k).vs_call_ctx = s.vs_call_ctx /\
  (u with vs_inst_idx := k).vs_immutables = s.vs_immutables
Proof
  strip_tac >> simp[buffer_allocation_fields_def, update_var_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
QED

Theorem unwrap_alloc_operand_frame:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
  (!p. op = Var p ==> p <> out) ==>
  eval_operand op (u with vs_inst_idx := k) = eval_operand op s
Proof
  strip_tac >> simp[] >> irule alloca_step_operand_preserved >> metis_tac[]
QED

Theorem unwrap_alloc_old_entry_taint:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post ctx func cenv cx e es sa sm s0 es' result vv s /\
  nb < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\
  FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
  off <= i /\ i < off + len ==>
  (i IN (step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn).t_mem
   <=> i IN tn.t_mem)
Proof
  strip_tac >> drule_all unwrap_alloc_old_entry_separation >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >> gvs[] >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  first_x_assum irule >> decide_tac
QED
