Theory bodyPtrTypeBuiltinsEmptyAlloc
Ancestors
  allocationPtr fragGasSeqPtr fragExecPtr fragExec loweringHalt exprSimAlloc
  context emitHelper compileEnv exprLoweringProps exprSimProps robustCopyTransportPtr
  venomExecSemantics
  venomInst venomState rich_list finite_map ptrDiscipline bodyPtrDefs venomMemDefs

(* The certificate uses the successful run supplied by the semantic proof;
   it does not choose a second machine endpoint. *)
Theorem empty_alloc_checked_run:
  !D ctx func PG G tn sa sb buf sz s t.
    compile_alloc_buffer sz sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    ~ctx_has_dalloca ctx ==>
    ?p. buf.buf_operand = Var p /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s
        (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) t)
        (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s t tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def] >>
  gvs[AllCaseEqs()] >>
  simp[inst_seq_ptr_def, ptr_inst_ok_alloca]
QED

Theorem empty_alloc_checked_coverage:
  !D ctx func cenv cx es PG G tn sa sb buf sz s t.
    compile_alloc_buffer sz sa = (buf,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    sz < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
    ?p G' tn'. buf.buf_operand = Var p /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      ptr_covers G' tn' p t sz /\
      (!q k. q <> p /\ ptr_covers G tn q s k ==>
         ptr_covers G' tn' q t k) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn' t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_alloc_checked_run >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >> gvs[] >>
  qexistsl_tac [`step_prov PG G
    (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)] [STRING #"%" (toString sa.cs_next_var)]) t`,
    `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)] [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  rpt conj_tac
  >- (irule alloca_step_ptr_covers >> metis_tac[])
  >- (rpt strip_tac >> irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  strip_tac >> irule alloca_step_stor_taint_ok >> metis_tac[]
QED

(* Old registers are framed even when this allocation site is reused. *)
Theorem empty_alloc_old_ghost:
  !ctx func cenv cx es s id n out t PG G tn q.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    q <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) q =
      FLOOKUP G q /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
      (Var q) = op_taint tn (Var q)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem empty_alloc_memory_ghost:
  !ctx func cenv cx es s id n out t tn b.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    FLOOKUP t.vs_allocas id = SOME (b,n) ==>
    t.vs_memory = s.vs_memory /\
    (!i. ~(b <= i /\ i < b+n) ==>
       (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
        <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[update_var_def]
QED

Theorem empty_alloc_ghost_kept:
  !ctx func cenv cx es s sa n out t PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ ~not_fresh_at sa out /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
      (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[ghost_kept_def] >>
  conj_tac
  >- (gen_tac >> strip_tac >> irule empty_alloc_old_ghost >> simp[] >> metis_tac[]) >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
          qpat_x_assum `!aid base sz. FLOOKUP _ _ = SOME _ ==> _ <= _` drule >> decide_tac) >>
      rpt strip_tac >>
      fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def, local_region_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[]
QED

Theorem empty_alloc_local_robust:
  !ctx func cenv cx es s id n out t tn tv v w.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ val_wf tv v /\
    w2n w + val_footprint tv v <= s.vs_alloca_next /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
      t.vs_memory m ==> val_in_memory tv v (w2n w) m
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def] >> rpt strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `tn.t_mem`,
        `tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`,
        `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`] >>
      simp[] >> rpt strip_tac >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[update_var_def]
QED

Theorem empty_alloc_ghost_inv:
  !ctx func cenv cx es s id n out t PG G tn d.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
    ghost_inv d cenv cx es G tn s ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) t
Proof
  rpt gen_tac >> strip_tac >>
  `!p. p <> out ==> lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     drule alloca_step_operand_preserved >>
     disch_then (qspec_then `Var p` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_def] >> strip_tac >> rpt conj_tac
  >- suspend "locals"
  >- suspend "returnbuf"
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >>
      drule_all empty_alloc_old_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  irule alloca_step_stor_taint_ok >> metis_tac[]
QED

Resume empty_alloc_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by metis_tac[] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac
  >- (irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\
   w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >> strip_tac >> gvs[] >>
     `val_footprint entry.type entry.value <= type_memory_size entry.type` by
       metis_tac[val_footprint_le] >> decide_tac) >>
  irule empty_alloc_local_robust >> metis_tac[]
QED

Resume empty_alloc_ghost_inv[returnbuf]:
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def] >>
  irule alloca_step_old_ptr_covers >> metis_tac[]
QED

Finalise empty_alloc_ghost_inv

Theorem empty_alloc_buffer_certificate:
  !D ctx func cenv cx es s sa sb buf n t PG G tn d.
    compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    ghost_inv d cenv cx es G tn s ==>
    ?p G' tn'. buf.buf_operand = Var p /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      ptr_covers G' tn' p t n /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es sa G tn s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    suspend "member" >>
  drule_all empty_alloc_checked_run >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >> gvs[] >>
  qexistsl_tac [`step_prov PG G
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
        [STRING #"%" (toString sa.cs_next_var)]) t`,
    `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
        [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  rpt conj_tac
  >- (irule alloca_step_ptr_covers >> metis_tac[])
  >- (irule empty_alloc_ghost_inv >> simp[] >>
      fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule empty_alloc_ghost_kept >> metis_tac[]
QED

Resume empty_alloc_buffer_certificate[member]:
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all emit_inst_fn_member >>
  gvs[]
QED

Finalise empty_alloc_buffer_certificate
