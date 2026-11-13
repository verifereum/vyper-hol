(* Single-slot TopLevelName materialization: memory and pointer checks on
   the same operational load/store run. *)
Theory bodyFullToplevelSlotSingle
Ancestors
  bodyFullUnwrapRun exprPtrUnwrapSingleSegment bodyStorageCopyMemory
  exprPtrUnwrapEnsureSingle bodyFullUnwrapSlotPost exprPtrUnwrapStoragePost
  exprLoweringProps bodyPtrDefs venomState venomInst words list rich_list
  bodyMemEcArithPrefix exprPtrUnwrapAllocation bufferAllocationExecution fragGasSeqPtr
  fragGasOriginPtrDead fragGasOriginPtr exprPtrUnwrapLoopEntry
  exprPtrUnwrapAllocSemantic exprPtrUnwrapEnsureShape
  venomExecSemantics ptrDiscipline loweringStateRelDefs exprSimStorageCopy
  slotCopyExecution frameActivationSeparation copyExecution finite_map
  exprPtrUnwrapRuntimeFrame venomMemProps valueEncodingProps arithmetic
  exprPtrUnwrapAllocSeparation exprSimAlloc allocationPtr loweringPosts exprSimProps
  exprPtrUnwrapEndpointFrames ctorDeployMemoryRunMemEntryWord

Theorem toplevel_slot_single_suffix_origin_ptr:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\
  emitted_insts sa sb =
    [mk_inst id (if p.ptr_location=LocStorage then SLOAD else TLOAD)
       [p.ptr_operand] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand p.ptr_operand s = SOME key /\ op_taint tn p.ptr_operand = {} /\
  root <> out /\ ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  w2n addr + 32 < dimword (:256) /\ w2n addr + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    t = mstore (w2n addr)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key)
      (update_var out
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key) s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x k. x <> out /\ ptr_covers G tn x s k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  mp_tac (Q.INST [`fn` |-> `func`, `src` |-> `p.ptr_operand`,
    `load` |-> `if p.ptr_location=LocStorage then SLOAD else TLOAD`]
    copy_single_slot_segment) >>
  (impl_tac >- (simp[] >> Cases_on `p.ptr_location=LocStorage` >> simp[])) >>
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (asm_rewrite_tac[] >> irule body_storage_singleton_mem_ok >>
     simp[eval_operand_def] >> qexists `w2n addr` >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (asm_rewrite_tac[] >> Cases_on `p.ptr_location=LocStorage` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >> asm_rewrite_tac[] >>
  Cases_on `p.ptr_location=LocStorage` >> gvs[]
QED

Theorem toplevel_slot_alloc_origin_ptr:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  compile_alloc_buffer nb sa = (buf,sb) /\ fn_has_code sa sb func /\
  nb < dimword (:256) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out u.
    buf.buf_operand = Var out /\ buf.buf_size = nb /\
    u = update_var out (n2w (buffer_allocation_base s sa.cs_next_id))
      (buffer_allocation_fields s sa.cs_next_id nb) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),
       step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u,
       step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
Proof
  strip_tac >> drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `u.vs_requests = s.vs_requests` by
    (simp[Abbr `u`, buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule unwrap_alloc_ptr_check >>
     simp[] >> qexists `u` >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s
     (step_prov PG G inst u) (step_taint inst s u tn)` by
    simp[inst_seq_ptr_def] >>
  `run_inst_seq [inst] s = OK u` by simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[ec_alloc_buffer_mem_ok] >>
  drule unwrap_alloc_current_block >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),
      step_prov PG G inst u, step_taint inst s u tn)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`out`, `u`] >> gvs[Abbr `u`, Abbr `inst`]
QED

(* The raw endpoints and ghost updates are selected once, not once per H. *)
Theorem toplevel_slot_single_common_run:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_alloc_buffer nb sa = (buf,mid) /\ buf.buf_operand = Var root /\
  fn_has_code sa mid func /\ nb < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = update_var root (n2w (buffer_allocation_base s sa.cs_next_id))
        (buffer_allocation_fields s sa.cs_next_id nb) /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  same_blocks mid sb /\ isPREFIX mid.cs_current_insts sb.cs_current_insts /\
  fn_has_code mid sb func /\
  emitted_insts mid sb =
    [mk_inst id (if p.ptr_location=LocStorage then SLOAD else TLOAD) [p.ptr_operand] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand p.ptr_operand a = SOME key /\ op_taint tn0 p.ptr_operand = {} /\
  root <> out /\ ptr_covers G0 tn0 root a 32 /\ lookup_var root a = SOME addr /\
  w2n addr + 32 < dimword (:256) /\ w2n addr + 32 <= a.vs_alloca_next /\
  allocas_from lo a /\ ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?Gf tnf t.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    t = mstore (w2n addr)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key)
      (update_var out
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key) a) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) key} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    (!x k. x <> out /\ ptr_covers G0 tn0 x a k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {}|>` >>
  mp_tac (Q.INST [`D` |-> `D0`, `sb` |-> `mid`] toplevel_slot_alloc_origin_ptr) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0)` by
    (gvs[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by simp[] >>
  drule_all toplevel_slot_single_suffix_origin_ptr >>
  disch_then (qspecl_then [`explicit`, `PG`, `D0`] strip_assume_tac) >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  qexistsl [`Gf`, `tnf`, `t`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  gvs[Abbr `D0`]
QED

Theorem toplevel_slot_single_endpoint:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_ensure_in_memory p.ptr_operand p.ptr_location nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  nb < dimword (:256) /\ 32 <= nb /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  eval_operand p.ptr_operand s = SOME key /\ op_taint tn p.ptr_operand = {} ==>
  ?root d mid buf u a G0 tn0 z Gf tnf.
    compile_alloc_buffer nb sa = (buf,mid) /\
    fn_has_code sa mid func /\ fn_has_code mid sb func /\
    buf.buf_operand = Var root /\ op = Var root /\
    d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    z = (mstore (w2n d)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key)
      (update_var (STRING #"%" (toString mid.cs_next_var))
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) a key) a)
      with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_covers Gf tnf root z nb /\ eval_operand op z = SOME d /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
      {w2n d+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule_all ensure_slot_memory_single_code >> strip_tac >>
  `32*1 <= nb` by simp[] >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`, `G`, `ARB`] strip_assume_tac) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s
     (n2w nb : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo u` by metis_tac[frameActivationSeparationTheory.allocas_from_exec_alloca] >>
  `allocas_from lo a` by
    (qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def]) >>
  `alloca_inv u` by fs[stmt_state_rel_def, state_rel_def] >>
  `w2n d + 32 <= a.vs_alloca_next` by
    (`w2n d + nb <= u.vs_alloca_next` by
       metis_tac[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `w2n d + nb <= _` mp_tac >> simp[] ) >>
  drule_all ensure_slot_memory_split >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `buf' = buf /\ sm'' = sm'` by fs[] >>
  qpat_x_assum `buf' = buf` SUBST_ALL_TAC >>
  qpat_x_assum `sm'' = sm'` SUBST_ALL_TAC >>
  drule storage_copy_word_layout >> strip_tac >>
  `root <> STRING #"%" (toString sm'.cs_next_var)` by
    (qpat_x_assum `slot_copy_external _ (Var root)` mp_tac >>
     simp[slot_copy_external_def, slot_copy_var_def] >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_covers G0 tn0 root a 32` by fs[] >>
  `a = u with vs_inst_idx := LENGTH sm'.cs_current_insts` by
    (qpat_x_assum `a.vs_inst_idx = _` mp_tac >>
     qpat_assum `a = _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  mp_tac (Q.INST [`mid` |-> `sm'`, `addr` |-> `d`,
    `id` |-> `sm'.cs_next_id`, `out` |-> `STRING #"%" (toString sm'.cs_next_var)`]
    toplevel_slot_single_common_run) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    qpat_x_assum `w2n d + 32 * 1 < _` mp_tac >> simp[dimword_def])) >> strip_tac >>
  `ptr_covers Gf tnf root t nb` by metis_tac[] >>
  `ptr_covers Gf tnf root (t with vs_inst_idx := LENGTH sb.cs_current_insts) nb` by
    (qpat_x_assum `ptr_covers Gf tnf root t nb` mp_tac >>
     simp[ptr_covers_def, lookup_var_def]) >>
  `eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME d` by
    (qpat_x_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[eval_operand_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl [`root`, `d`, `sm'`, `buf`, `u`, `a`, `G0`, `tn0`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`, `Gf`, `tnf`] >>
  asm_rewrite_tac[]
QED


Theorem toplevel_slot_single_copy_projections[local]:
  compile_expr cenv ty (TopLevelName ann nsid) si = (vv,sm) /\
  z = (mstore (w2n d) w (update_var (STRING #"%" (toString mid.cs_next_var)) w a)
    with vs_inst_idx := idx) /\
  tf.t_mem = (ti.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
    {w2n d+k | k IN key_taint keys key} ==>
  slot_copy_runtime_frame mid d 1 a z /\ mem_word_at (w2n d) z.vs_memory = w /\
  z.vs_requests = a.vs_requests /\
  (!b. b < 32 /\ w2n d+b IN tf.t_mem ==> b IN key_taint keys key) /\
  (!j. j < w2n d \/ w2n d+32 <= j ==> (j IN tf.t_mem <=> j IN ti.t_mem))
Proof
  strip_tac >>
  `copy_static z = copy_static a` by
    simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  drule copy_static_fields >> strip_tac >>
  conj_tac
  >- (simp[slot_copy_runtime_frame_def] >> conj_tac
      >- (rpt strip_tac >> Cases_on `op` >>
          simp[eval_operand_def, lookup_var_def, mstore_def,
            write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE] >>
          qpat_x_assum `slot_copy_external _ _` mp_tac >>
          simp[slot_copy_external_def, slot_copy_var_def] >>
          disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >>
          `a'+1 <= w2n d \/ w2n d+32 <= a'` by decide_tac >>
          simp[mstore_mem_bytes_at_disjoint, update_var_def]) >>
      conj_tac >- simp[LENGTH_mstore_eq, update_var_def] >>
      rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint, update_var_def]) >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >>
      gvs[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF,
        pred_setTheory.GSPECIFICATION, ADD_COMM]) >>
  rpt strip_tac >>
  `~(w2n d <= j /\ j < w2n d+32)` by decide_tac >>
  `~(?k. j = w2n d+k /\ k IN key_taint keys key)` by
    (strip_tac >> fs[key_taint_def] >> decide_tac) >>
  simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
  metis_tac[ADD_COMM]
QED

Theorem toplevel_slot_single_allocation_bounds[local]:
  compile_expr cenv ty (TopLevelName ann nsid) si = (vv,sm) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  stmt_state_rel H ctx func cenv cx ee s /\ nb < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  d = n2w (buffer_allocation_base s sb.cs_next_id) /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts ==>
  buf.buf_size = nb /\ lo <= w2n d /\ allocas_from lo a /\
  s.vs_alloca_next <= a.vs_alloca_next /\ w2n d+nb <= a.vs_alloca_next /\
  buffer_allocation_base s sb.cs_next_id < dimword (:256) /\
  a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
  a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
  a.vs_requests = s.vs_requests /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP a.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  drule_all unwrap_alloc_site_bound >> strip_tac >>
  `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
  `w2n d = buffer_allocation_base s sb.cs_next_id` by simp[w2n_n2w] >>
  `lo <= buffer_allocation_base s sb.cs_next_id` by
    (Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  `exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s
     (n2w nb : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  `allocas_from lo u` by metis_tac[allocas_from_exec_alloca] >>
  drule_all unwrap_alloc_fields_old >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `allocas_from lo a` by
    (qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry` by
    (qpat_x_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _` mp_tac >>
     simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
  >- simp[buffer_allocation_fields_def, update_var_def, buffer_allocation_base_def] >>
  rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  fs[buffer_allocation_fields_def, update_var_def, buffer_allocation_base_def,
    venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  metis_tac[ADD_COMM]
QED

Theorem toplevel_slot_single_allocation_separation[local]:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  fn_inst_ids_distinct func /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id ==>
    off+sz <= w2n d \/ w2n d+nb <= off) /\
  (!name b len. local_region cenv es.scopes s0 name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n d \/ w2n d+nb <= off)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes u name b len` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl [`s`, `sb`, `ee.scopes`] >> simp[] >> metis_tac[]) >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
    local_region cenv ee.scopes s name b len` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s0`, `sa`, `es.scopes`] >> simp[] >> fs[vv_post_def]) >>
  fs[regions_disjoint_def] >> rpt conj_tac >> metis_tac[vv_post_def, LESS_LESS_EQ_TRANS]
QED

Theorem toplevel_slot_single_history[local]:
  compile_expr cenv ty (TopLevelName ann nsid) si = (vv,sm) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\ fn_inst_ids_distinct func /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  same_blocks mid sc /\ isPREFIX mid.cs_current_insts sc.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts mid sc) /\
  z.vs_allocas = a.vs_allocas /\ z.vs_current_bb = mid.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  alloca_history func z
Proof
  strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule unwrap_alloc_current_block >> strip_tac >>
  `alloca_history func a` by
    (qpat_assum `a = _` (fn th => pure_rewrite_tac[th]) >>
     irule emitted_alloca_history >>
     simp[] >>
     qexistsl [`[mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]]`, `s`, `sb`] >>
     `out = root` by metis_tac[operand_11] >>
     fs[run_inst_seq_def] >> simp[mk_inst_def, is_terminator_def]) >>
  `?bb. lookup_block mid.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts mid sc) (DROP (LENGTH mid.cs_current_insts) bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code mid sc func` mp_tac >>
     simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
     qexists `bb` >>
     gvs[same_blocks_def, IS_PREFIX_APPEND, emitted_insts_def,
       DROP_APPEND, DROP_LENGTH_NIL]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
     >- (simp[update_var_def] >> strip_tac >> gvs[]) >>
     PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[]) >>
  irule ctor_sequence_history_advance >>
  qexistsl [`bb`, `emitted_insts mid sc`, `a`] >>
  simp[] >>
  gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
    DROP_APPEND, DROP_LENGTH_NIL]
QED

Theorem toplevel_slot_single_history_endpoint[local]:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  p.ptr_location = slot_loc tr /\
  compile_ensure_in_memory p.ptr_operand p.ptr_location nb 1 ctor imm sb = (op,sc) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\ fn_inst_ids_distinct func /\
  d = n2w (buffer_allocation_base s sb.cs_next_id) /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  z = mstore (w2n d) (slot_copy_word (if p.ptr_location = LocStorage then SLOAD else TLOAD) a key)
    (update_var (STRING #"%" (toString mid.cs_next_var))
      (slot_copy_word (if p.ptr_location = LocStorage then SLOAD else TLOAD) a key) a)
      with vs_inst_idx := LENGTH sc.cs_current_insts /\
  z.vs_allocas = a.vs_allocas ==>
  alloca_history func z /\ z.vs_current_bb = sc.cs_current_bb /\
  z.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  drule_at (Pos last) ensure_slot_memory_split >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `buf1` (qx_choose_then `mid1` strip_assume_tac) o SRULE []) >>
  `buf1 = buf /\ mid1 = mid` by fs[] >>
  qpat_x_assum `buf1 = buf` SUBST_ALL_TAC >>
  qpat_x_assum `mid1 = mid` SUBST_ALL_TAC >>
  drule storage_copy_word_layout >> strip_tac >>
  `z.vs_current_bb = mid.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (drule unwrap_alloc_current_block >> strip_tac >>
     simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >> pairarg_tac >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts mid sc)` by
    (Cases_on `p.ptr_location = LocStorage` >> simp[mk_inst_def]) >>
  drule_all toplevel_slot_single_history >>
  strip_tac >> qpat_x_assum `z = _` kall_tac >>
  qpat_x_assum `u = _` kall_tac >> qpat_x_assum `a = _` kall_tac >>
  fs[same_blocks_def]
QED

Theorem toplevel_slot_single_certificate:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue vt p,sm) /\
  p.ptr_location = slot_loc tr /\
  compile_ensure_in_memory p.ptr_operand p.ptr_location nb 1 ctor imm sb = (op,sc) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue vt p) s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  nb < dimword (:256) /\ 32 <= nb /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  eval_operand p.ptr_operand s = SOME key /\ op_taint tn p.ptr_operand = {} ==>
  ?buf mid root d u a G0 tn0 z Gf tnf.
  compile_alloc_buffer nb sb = (buf,mid) /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\
  buf.buf_operand = Var root /\ buf.buf_size = nb /\ op = Var root /\
  d = n2w (buffer_allocation_base s sb.cs_next_id) /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  G0 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  slot_copy_runtime_frame mid d 1 a z /\
  mem_word_at (w2n d) z.vs_memory = slot_copy_word (if tr then TLOAD else SLOAD) s key /\
  eval_operand op z = SOME d /\ ptr_covers Gf tnf root z nb /\
  (!b. b < 32 /\ w2n d+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) key) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_requests = s.vs_requests /\
  (!x. not_fresh_at sb x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
  alloca_history func z /\ allocas_from lo z /\
  s.vs_alloca_next <= z.vs_alloca_next /\ lo <= w2n d /\
  w2n d+nb <= z.vs_alloca_next /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id /\
    (!name b len. local_region cenv ee.scopes s name b len ==> off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) /\
  (!name b len. local_region cenv es.scopes s0 name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b len. local_region cenv es.scopes s0 name b len ==> off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf))
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  mp_tac (Q.INST [`si` |-> `sa`, `sa` |-> `sb`, `sb` |-> `sc`, `es` |-> `ee`]
    toplevel_slot_single_endpoint) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[slot_loc_def])) >>
  strip_tac >>
  drule_all toplevel_slot_single_allocation_bounds >> strip_tac >>
  drule_all toplevel_slot_single_allocation_separation >> strip_tac >>
  drule_all toplevel_slot_single_copy_projections >> strip_tac >>
  drule_all (Q.INST [`n` |-> `1`] unwrap_copy_exterior_frames |> SRULE []) >> strip_tac >>
  `sb.cs_next_var <= mid.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!x. slot_copy_external mid (Var x) ==>
    FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> STRING #"%" (toString mid.cs_next_var)` by
       (fs[slot_copy_external_def, slot_copy_var_def] >>
        first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     metis_tac[]) >>
  `!x. not_fresh_at sb x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     mp_tac (Q.INST [`sa` |-> `sb`, `sm` |-> `sb`, `HG` |-> `Gf`,
       `tf` |-> `tnf`, `n` |-> `1`, `k` |-> `LENGTH mid.cs_current_insts`]
       unwrap_copy_old_variable_frames) >>
     (impl_tac >- simp[]) >>
     metis_tac[]) >>
  `z.vs_allocas = a.vs_allocas /\ z.vs_alloca_next = a.vs_alloca_next /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\ z.vs_requests = s.vs_requests` by
    (qpat_x_assum `slot_copy_runtime_frame _ _ _ _ _` mp_tac >>
     simp[slot_copy_runtime_frame_def]) >>
  `allocas_from lo z` by metis_tac[allocas_from_def] >>
  `w2n d = buffer_allocation_base s sb.cs_next_id` by simp[] >>
  `mem_word_at (w2n d) z.vs_memory = slot_copy_word (if tr then TLOAD else SLOAD) s key` by
    (`!load. slot_copy_word load a key = slot_copy_word load s key` by
       (gen_tac >> irule slot_copy_word_sources >> asm_rewrite_tac[]) >>
     `p.ptr_location = LocStorage <=> ~tr` by
       (Cases_on `tr` >> fs[slot_loc_def]) >>
     qpat_x_assum `z = _` kall_tac >>
     Cases_on `tr` >> fs[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_slot_single_history_endpoint >> strip_tac >>
  qexistsl [`buf`, `mid`, `root`, `d`, `u`, `a`, `G0`, `tn0`, `z`, `Gf`, `tnf`] >>
  qpat_x_assum `z = _` kall_tac >>
  qpat_x_assum `tnf.t_mem = _` kall_tac >>
  `p.ptr_location = LocStorage <=> ~tr` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  Cases_on `tr` >> gvs[] >> metis_tac[]
QED
