(* A memory-source snapshot uses the actual raw ALLOCA followed by MCOPY. *)
Theory bodyLocalSnapshotPhysicalMods
Ancestors
  arithmetic finite_map pred_set words assignTuplePtrCopyLen
  bodyFullAllocaFresh bodyFullMemoryCopy bodyPtrMakeArrayCopyStateFrame
  bodyFullHashKeccakFixed bufferAllocationExecution abiBuiltinAllocation
  bodyPtrDefs compileEnv context emitHelperProps exprLoweringProps
  exprSimAlloc exprSimProps exprSimStorageCopy fragExec fragGasOriginPtrLoop
  freshWrites localPtrsProps loweringHalt loweringStateRelDefs ptrDiscipline
  robustCopyTransportPtr stmtSimDefs typedCopyOriginPtrBase typedMemoryCopy
  venomState venomMemDefs

Theorem local_snapshot_physical_mods:
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand (Var xs) n sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n < dimword (:256) /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  type_memory_size tv = n /\ val_wf tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s n /\ w2n sw+n < dimword (:256) /\
  (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u root b Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    lookup_var root u = SOME (n2w b) /\ ptr_covers Gu tu root u n /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    lo <= b /\ b+n < dimword (:256) /\ b+n <= u.vs_alloca_next /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory tv v b mem) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
      FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!name a len. local_region cenv es.scopes u name a len <=>
      local_region cenv es.scopes s name a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b n a len) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    typed_copy_frame b n s.vs_memory u.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_immutables = s.vs_immutables /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`sb` |-> `sm`,`H` |-> `H0`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
      alloc_buffer_origin_ptr_path_with_raw_endpoint))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`a`,`Ga`,`ta`,`raw`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,Ga,ta)` by
    first_assum ACCEPT_TAC >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  `s.vs_memory = a.vs_memory /\ ~a.vs_halted /\
   a.vs_data_section = s.vs_data_section /\ a.vs_call_ctx = s.vs_call_ctx /\
   a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
   a.vs_immutables = s.vs_immutables` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
                        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_halted,z.vs_data_section,
          z.vs_call_ctx,z.vs_accounts,z.vs_transient,z.vs_immutables)``) >> simp[]) >>
  `!aid off sz. FLOOKUP a.vs_allocas aid = SOME (off,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off` by
    suspend "alloc_table" >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func)` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     drule_all buffer_alloc_code >> fs[]) >>
  `!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by
    suspend "alloc_taint" >>
  `!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by suspend "source" >>
  suspend "copy"
QED

Resume local_snapshot_physical_mods[alloc_table]:
  drule compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `raw = update_var root (n2w (buffer_allocation_base s sa.cs_next_id))
          (buffer_allocation_fields s sa.cs_next_id (w2n (n2w n : bytes32)))` by
    (qpat_x_assum `run_inst_seq _ _ = OK (update_var _ _ _)` mp_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `FLOOKUP a.vs_allocas aid = SOME (off,sz)` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  simp[update_var_def,buffer_allocation_fields_def,FLOOKUP_UPDATE] >>
  Cases_on `aid = sa.cs_next_id` >> simp[]
QED

Resume local_snapshot_physical_mods[alloc_taint]:
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) s = OK raw` by
    (qpat_x_assum `run_inst_seq _ _ = OK raw` mp_tac >>
     fs[run_inst_seq_def,AllCaseEqs()]) >>
  `FLOOKUP raw.vs_allocas sa.cs_next_id = SOME (w2n w,n)` by
    (qpat_assum `FLOOKUP a.vs_allocas sa.cs_next_id = SOME _` mp_tac >>
     qpat_assum `a = raw with vs_inst_idx := _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  drule_all bodyPtrMakeArrayAllocBufferTheory.literal_alloca_exterior_taint >>
  simp[arithmeticTheory.NOT_LESS, arithmeticTheory.NOT_LESS_EQUAL]
QED

Resume local_snapshot_physical_mods[source]:
  `val_footprint tv v <= n` by metis_tac[val_footprint_le] >>
  mp_tac (Q.SPECL [`tn.t_mem`,`ta.t_mem`,`s.vs_memory`,`a.vs_memory`,
    `{i | s.vs_alloca_next <= i /\ i < w2n (w:bytes32)+n}`,`tv`,`v`,`w2n (sw:bytes32)`]
    robust_val_in_memory_exterior_frame) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> fs[] >> decide_tac)) >> simp[]
QED

Resume local_snapshot_physical_mods[copy]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm xs /\ lookup_var xs a = SOME sw` by metis_tac[] >>
  `ptr_covers Ga ta xs a n` by metis_tac[ptr_covers_lookup_frame] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by
    (`stmt_state_rel H0 ctx func cenv cx es a` by simp[] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `n = 0 \/ w2n sw+n <= a.vs_alloca_next` by decide_tac >>
  `compile_copy_memory (Var root) (Var xs) n sm = ((),sb)` by
    (qpat_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var root` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  mp_tac (Q.INST [`xd` |-> `root`,`sa` |-> `sm`,`s` |-> `a`,
    `dw` |-> `w:bytes32`,`tn` |-> `ta`,`G` |-> `Ga`]
    (SPEC_ALL body_full_memory_copy_path)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac) >>
  suspend "snapshot_post"
QED

Resume local_snapshot_physical_mods[snapshot_post]:
  markerLib.RESUME_TAC >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Ga`,`a`,`ta`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >> drule typed_copy_state_frame_allocas_below_fmp >>
     disch_then (irule o iffRL) >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `copy_static u = copy_static a` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``copy_static`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[copy_static_def]) >>
  `u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
   u.vs_data_section = a.vs_data_section /\ u.vs_call_ctx = a.vs_call_ctx /\
   u.vs_accounts = a.vs_accounts /\ u.vs_transient = a.vs_transient /\
   u.vs_immutables = a.vs_immutables` by
    (qpat_assum `copy_static u = copy_static a`
       (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next,z.vs_data_section,
           z.vs_call_ctx,z.vs_accounts,z.vs_transient,z.vs_immutables)``) >>
     SIMP_TAC (srw_ss()) [copy_static_def]) >>
  `!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u` by
    suspend "copy_state" >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_copy_memory,pairTheory.SND] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sb x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\
    lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `lookup_var root u = SOME w` by metis_tac[] >>
  `ptr_covers Gu tu root u n` by metis_tac[ptr_covers_lookup_frame] >>
  `!name off len. local_region cenv es.scopes u name off len <=>
    local_region cenv es.scopes s name off len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `!name off len. local_region cenv es.scopes u name off len ==>
    regions_disjoint (w2n w) n off len` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
     fs[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  qexistsl_tac [`u`,`root`,`w2n (w:bytes32)`,`Gu`,`tu`] >>
  pure_rewrite_tac[n2w_w2n] >> suspend "assemble"
QED

Resume local_snapshot_physical_mods[copy_state]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`sa.cs_next_id`,`w2n (w:bytes32)`,`n`,`root`,`sa`,`sm`,`a`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (first_assum irule >> first_assum ACCEPT_TAC)]
QED

Resume local_snapshot_physical_mods[assemble]:
  markerLib.RESUME_TAC >>
  `not_fresh_at sb root` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  `lo <= a.vs_alloca_next` by decide_tac >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo a` mp_tac >>
     qpat_assum `u.vs_allocas = a.vs_allocas` (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     SIMP_TAC (srw_ss()) []) >>
  `typed_copy_frame (w2n (w:bytes32)) n s.vs_memory u.vs_memory` by
    (qhdtm_assum `typed_copy_state_frame` (strip_assume_tac o REWRITE_RULE
        [typed_copy_state_frame_def]) >>
     qpat_assum `s.vs_memory = a.vs_memory` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!i. ~(w2n (w:bytes32) <= i /\ i < w2n w+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> (i IN tu.t_mem <=> i IN ta.t_mem)` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. _ ==> (i IN ta.t_mem <=> i IN tn.t_mem)` (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_assum `u.vs_allocas = a.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u.vs_alloca_next = a.vs_alloca_next` (fn th => pure_rewrite_tac[th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (simp[] >> NO_TAC)]
QED

Finalise local_snapshot_physical_mods
