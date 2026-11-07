(* Semantic ownership at the normalization allocation, including reused sites. *)
Theory storageNormalizationOwnershipPtr
Ancestors
  storageNormalizationAllocPtr exprSimAlloc exprSimCopy reasonAllocationFramePtr
  reasonBufferPtr robustCopyTransportPtr allocationPtr loweringHalt exprSimProps context compileEnv exprLoweringProps venomExecSemantics
  venomInst venomState finite_map words

Theorem normalization_alloc_buffer_ownership:
  !func cenv cx es sa sm buf sz s ctx PG G tn.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword(:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w p.
      buf.buf_operand = Var p /\
      step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand (Var p) t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword(:256) /\ t.vs_memory = s.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
        regions_disjoint (w2n w) sz b len) /\
      ptr_covers
        (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) t)
        (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s t tn)
        p t sz /\
      (!old n. old <> p /\ ptr_covers G tn old s n ==>
        ptr_covers
          (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) t)
          (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s t tn)
          old t n)
Proof
  rpt gen_tac >> strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK t` by
    gvs[run_inst_seq_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
        AllCaseEqs()] >>
  qexistsl_tac [`t`, `w`, `p`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule alloca_step_ptr_covers >> metis_tac[]) >>
  rpt strip_tac >> irule alloca_step_old_ptr_covers >> metis_tac[]
QED

Theorem normalization_alloca_storage_observations:
  !s id n out s1.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    s1.vs_accounts = s.vs_accounts /\
    s1.vs_transient = s.vs_transient /\
    s1.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Theorem normalization_alloca_storage_holds:
  !s id n out s1 cx tr ty tv w es.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    storage_holds cx tr ty tv w es s ==>
    storage_holds cx tr ty tv w es s1
Proof
  rpt strip_tac >> drule normalization_alloca_storage_observations >>
  strip_tac >> gvs[loweringPostsTheory.storage_holds_def,
    contract_storage_def, contract_transient_def]
QED

Theorem normalization_alloca_key_taints:
  !id n out s s1 tn.
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_imm = tn.t_imm
Proof
  simp[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def, mk_inst_def]
QED

Theorem normalization_alloca_located_storage:
  !ctx func cenv cx es s id n out s1 PG G tn ty tv p t'.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword(:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    (!x. p.ptr_operand = Var x ==> x <> out) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    eval_operand p.ptr_operand s1 = eval_operand p.ptr_operand s /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand p.ptr_operand s1 = eval_operand p.ptr_operand s` by
    (irule alloca_step_operand_preserved >> metis_tac[]) >>
  drule normalization_alloca_storage_observations >> strip_tac >>
  qspecl_then [`id`, `n`, `out`, `s`, `s1`, `tn`] strip_assume_tac
    normalization_alloca_key_taints >>
  `op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      p.ptr_operand = op_taint tn p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> gvs[ptrDisciplineTheory.op_taint_def] >>
     drule_all reason_alloca_old_metadata >> simp[ptrDisciplineTheory.op_taint_def]) >>
  gvs[bodyPtrDefsTheory.ptr_vv_ok_def]
QED

(* Copy clients keep the semantic frame and protected registered buffers
   separate from the destination's representation/taint argument. *)
Theorem normalization_copy_ownership_frame:
  !ctx func cenv cx es st s t inst b sz.
    stmt_state_rel ctx func cenv cx es s /\
    local_ptrs_reserved cenv st /\ copy_static t = copy_static s /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region cenv es.scopes s name lb len ==>
      regions_disjoint b sz lb len) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_allocas = s.vs_allocas /\
    (!tr ty tv w. storage_holds cx tr ty tv w es s ==>
      storage_holds cx tr ty tv w es t) /\
    (!aid off len. aid <> inst.inst_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`b`, `inst`, `s`, `st`, `sz`] >>
     fs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >>
      gvs[loweringPostsTheory.storage_holds_def, contract_storage_def,
        contract_transient_def]) >>
  rpt strip_tac >> first_x_assum irule >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  gvs[venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
  disch_then (qspecl_then [`off`, `len`, `b`, `sz`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem normalization_alloca_checked_endpoint:
  !D ctx func PG G tn s id n out s1 bb cenv cx es.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    stmt_state_rel ctx func cenv cx es s /\
    stmt_state_rel ctx func cenv cx es s1 /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword(:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    gas_path_ptr D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stmt_state_rel ctx func cenv cx es (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac
  >- (drule_all reason_buffer_alloca_path >> simp[]) >>
  simp[stmt_state_rel_inst_idx]
QED

Theorem normalization_copy_protected_robust:
  !ctx func cenv cx es s t inst b sz aid off len tn tn' tv v p.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    aid <> inst.inst_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) /\
    off <= p /\ p + val_footprint tv v <= off+len /\ val_wf tv v /\
    (!i. ~(b <= i /\ i < b+sz) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. ~(b <= i /\ i < b+sz) ==> (i IN tn' <=> i IN tn)) /\
    (!m. mem_agree_outside tn s.vs_memory m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tn' t.vs_memory m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  `b+sz <= off \/ off+len <= b` by
    (`alloca_inv s` by gvs[stmt_state_rel_def] >>
     gvs[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
     disch_then (qspecl_then [`off`, `len`, `b`, `sz`] mp_tac) >>
     simp[] >> decide_tac) >>
  rpt strip_tac >>
  (irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
   conj_tac >- simp[] >>
   qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn`, `tn'`, `{i | b <= i /\ i < b+sz}`] >>
   simp[] >> rpt strip_tac >> decide_tac)
QED
