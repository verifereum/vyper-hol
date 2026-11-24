(* Physical constructor-code unwrap at the endpoint of a linked raw RHS. *)
Theory bodyCopyCtorRhsRunMods
Ancestors
  bodyFullUnwrapCodeCtorRun bodyFullShadowBodyInv
  fragGasOriginPtrDead fragExecPtr ghostPcTransportPtr exprSimAbiEncodeMemoryLength exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocEntry
  exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocation
  exprPtrUnwrapCodeCopyShape exprLoweringProps exprSimCopy exprSimStorageCopy
  stateRelProj loweringStateRelDefs bodyPtrDefs robustCopyTransportPtr
  bufferAllocationExecution immutableCopyExecution valueEncodingProps
  exprSimProps exprLowering context compileEnv venomState venomInst
  finite_map words arithmetic ptrDiscipline fragExec
  exprPtrUnwrapRetained loweringHalt exprSimAlloc freshWrites
  venomExecSemantics valueEncodingDefs

Theorem copy_ctor_rhs_snapshot[local]:
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  compile_imm_copy_to_memory T imm arg buf.buf_operand n 0 mid = ((),sc) /\
  copy_runtime_frame mid a sc z /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ lookup_var root a = SOME dst /\
  (!x. arg = Var x ==> not_fresh_at sb x) /\ eval_operand arg s = SOME src /\
  (n <> 0 ==> !region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    copy_old_operand sb region) ==>
  z.vs_memory = (immutable_transfers F T src dst n 0 a).vs_memory
Proof
  strip_tac >> Cases_on `n = 0`
  >- gvs[compile_imm_copy_zero, copy_runtime_frame_def, emitted_insts_refl,
         run_inst_seq_def, immutable_transfers_def] >>
  `!op. (!p. op = Var p ==> p <> root) ==> eval_operand op a = eval_operand op s` by
    (gen_tac >> strip_tac >> qpat_assum `a = _` SUBST1_TAC >>
     irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  `ci_mono sb mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
     copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s = SOME 0w /\ copy_old_operand sb region` by simp[] >>
     `!x. region = Var x ==> x <> root` by
       (fs[copy_old_operand_def] >> metis_tac[unwrap_alloc_old_operand_distinct]) >>
     metis_tac[copy_old_operand_mono, ci_mono_def]) >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `!x. arg = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
  `eval_operand arg a = SOME src` by metis_tac[] >>
  `eval_operand buf.buf_operand a = SOME dst /\ copy_old_operand mid buf.buf_operand` by
    gvs[eval_operand_def, copy_old_operand_def, operand_11, lookup_var_def] >>
  drule_all copy_ctor_run >> strip_tac >> fs[copy_runtime_frame_def] >> metis_tac[]
QED

(* No lookup or active/owning-module equality is needed: all bytes read by
   the suffix are in the protected range already certified by the raw post. *)
Theorem copy_ctor_rhs_endpoint_mods:
  unwrap_value ce (LocatedValue ty p) sb = (op,sc) /\
  ce.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type ty /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < dimword(:256) /\
  val_wf rt v /\
  eval_operand p.ptr_operand s = SOME src /\
  op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
  w2n src + type_memory_size rt <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v (w2n src) mem) /\
  stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at_mods D lo d ce cx ee G tn s /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sb /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?z Gf tnf root dst u.
    op = Var root /\ eval_operand op z = SOME dst /\
    ptr_covers Gf tnf root z (type_memory_size rt) /\
    FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    FLOOKUP Gf root = SOME (w2n dst,type_memory_size rt) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    sb.cs_next_id < sc.cs_next_id /\
    (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    w2n dst + type_memory_size rt <= z.vs_alloca_next /\ lo <= w2n dst /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n dst) mem) /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP z.vs_allocas id = SOME entry) /\
    (!id b len. id < sb.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
      b+len <= w2n dst \/ w2n dst+type_memory_size rt <= b) /\
    (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. i < w2n dst \/ w2n dst+type_memory_size rt <= i ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    z.vs_requests = s.vs_requests /\
    z.vs_fmp = s.vs_fmp /\ z.vs_initial_fmp = s.vs_initial_fmp /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    root = STRING #"%" (toString sb.cs_next_var) /\
    exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
      s (n2w (type_memory_size rt) : bytes32) = OK u /\
    FLOOKUP u.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    copy_static z = copy_static u /\ sb.cs_next_var < sc.cs_next_var /\
    w2n dst + type_memory_size rt < dimword(:256)
Proof
  strip_tac >>
  `type_memory_size rt = 32 * type_slot_size rt` by simp[type_memory_size_slots] >>
  `(type_memory_size rt + 31) DIV 32 = type_slot_size rt` by
    simp[type_memory_size_slots, ADD_DIV_ADD_DIV] >>
  `?buf mid. compile_alloc_buffer (type_memory_size rt) sb = (buf,mid) /\
     compile_imm_copy_to_memory T ce.ce_imm_alloca p.ptr_operand buf.buf_operand
       (type_slot_size rt) 0 mid = ((),sc) /\ op = buf.buf_operand` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `ci_mono sb mid /\ ci_mono mid sc` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  `fn_has_code sb mid func /\ fn_has_code mid sc func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `type_slot_size rt <> 0 ==> !region. ce.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
     op_taint tn region = {} /\ op_prov G region = NONE` by
    (disch_tac >> gen_tac >> disch_tac >> `lo <> 0` by decide_tac >>
     drule_then assume_tac stmt_state_rel_immutable_base_zero >>
     conj_tac >- fs[immutable_base_zero_def] >>
     Cases_on `region` >>
     fs[copy_old_operand_def, op_taint_def, op_prov_def, ghost_inv_at_mods_def] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `w2n src + 32 * type_slot_size rt <= lo` by decide_tac >>
  drule_all ctor_code_copy_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  rename1 `copy_runtime_frame mid a sc raw` >>
  rename1 `lookup_var root a = SOME dst` >>
  rename1 `ptr_covers Gf tnf root raw _` >>
  suspend "physical"
QED

Resume copy_ctor_rhs_endpoint_mods[physical]:
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `w2n dst = buffer_allocation_base s sb.cs_next_id` by simp[] >>
  `u = update_var root dst (buffer_allocation_fields s sb.cs_next_id (type_memory_size rt))` by simp[] >>
  `a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
   a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
   a.vs_immutables = s.vs_immutables` by
    (drule unwrap_alloc_runtime_frame >> simp[]) >>
  `copy_static raw = copy_static a /\
   (!x. not_fresh_at mid x ==> lookup_var x raw = lookup_var x a)` by
    fs[copy_runtime_frame_def] >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `lookup_var root raw = SOME dst` by simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `sb.cs_next_id < sc.cs_next_id` by fs[ci_mono_def] >>
  `raw.vs_allocas = u.vs_allocas /\ raw.vs_accounts = s.vs_accounts /\
   raw.vs_transient = s.vs_transient /\ raw.vs_call_ctx = s.vs_call_ctx /\
   raw.vs_immutables = s.vs_immutables /\ raw.vs_data_section = s.vs_data_section /\
   raw.vs_labels = s.vs_labels /\ raw.vs_requests = s.vs_requests /\
   raw.vs_fmp = s.vs_fmp /\ raw.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_x_assum `copy_static raw = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_allocas,st.vs_accounts,st.vs_transient,
         st.vs_call_ctx,st.vs_immutables,st.vs_data_section,st.vs_labels,
         st.vs_requests,st.vs_fmp,st.vs_initial_fmp)`) >>
     simp[copy_static_def, update_var_def, buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp raw` by
    (strip_tac >> drule_all unwrap_alloc_below_fmp >> simp[] >>
     qpat_x_assum `copy_static raw = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_fmp,st.vs_initial_fmp)`) >>
     simp[copy_static_def, allocas_below_fmp_def, update_var_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `lo <= w2n dst` by
    (qpat_assum `allocas_from lo raw` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sb.cs_next_id`, `w2n dst`, `type_memory_size rt`] match_mp_tac) >>
     qpat_assum `raw.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
    b+len <= w2n dst \/ w2n dst+type_memory_size rt <= b` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[DISJ_COMM]) >>
  suspend "taint_and_bytes"
QED

Resume copy_ctor_rhs_endpoint_mods[taint_and_bytes]:
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
       (fn_insts func)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> drule_all buffer_alloc_code >> gvs[]) >>
  `tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
   (!i. i < w2n dst \/ w2n dst+type_memory_size rt <= i ==>
     (i IN tm.t_mem <=> i IN tn.t_mem))` by
    (drule_all unwrap_alloc_taint_frame >> disch_then (qspec_then `tn` mp_tac) >>
     simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!i. i < w2n dst \/ w2n dst+type_memory_size rt <= i ==>
     (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!j. j IN tnf.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
     `~(w2n dst <= i /\ i < w2n dst + 32 * type_slot_size rt)` by decide_tac >> simp[]) >>
  `!i. i < type_memory_size rt ==>
     (w2n dst+i IN tnf.t_mem <=> w2n src+i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!j. j IN tnf.t_mem <=> _` (qspec_then `w2n dst+i` SUBST1_TAC) >>
     `w2n dst <= w2n dst+i /\ w2n dst+i < w2n dst+32*type_slot_size rt /\
      w2n dst+i-w2n dst = i /\ w2n src+i < w2n dst` by decide_tac >> simp[]) >>
  `(mem_bytes_at (w2n dst) (type_memory_size rt) raw.vs_memory =
    mem_bytes_at (w2n src) (type_memory_size rt) s.vs_memory) /\
   LENGTH s.vs_memory <= LENGTH raw.vs_memory` by
    suspend "snapshot" >>
  `val_footprint rt v <= type_memory_size rt` by (irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  `!mem. mem_agree_outside tnf.t_mem raw.vs_memory mem ==>
     val_in_memory rt v (w2n dst) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`s.vs_memory`, `raw.vs_memory`, `type_memory_size rt`, `w2n src`,
       `tn.t_mem`, `tnf.t_mem`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP Gf root = SOME (w2n dst,type_memory_size rt)` by
    (`Gm = G |+ (root,(w2n dst,type_memory_size rt))` by
       (qpat_x_assum `Gm = step_prov _ _ _ _` SUBST1_TAC >>
        irule step_prov_alloca >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at mid x ==> FLOOKUP Gf x = _ /\ _`
       (qspec_then `root` mp_tac) >> simp[FLOOKUP_UPDATE]) >>
  `op = Var root` by
    (qpat_assum `op = buf.buf_operand` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `FLOOKUP raw.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt)` by
    (qpat_assum `raw.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP raw.vs_allocas id = SOME entry` by
    (qpat_assum `raw.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
     mem_bytes_at off len raw.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_x_assum `!at len. _ ==> mem_bytes_at at len raw.vs_memory = _` mp_tac >>
     pure_asm_rewrite_tac[] >> disch_tac >> first_assum ACCEPT_TAC) >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    simp[] >>
  `root = STRING #"%" (toString sb.cs_next_var) /\ sb.cs_next_var < sc.cs_next_var` by
    fs[ci_mono_def] >>
  `exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
      s (n2w (type_memory_size rt) : bytes32) = OK u` by
    (qpat_assum `step_inst_base _ _ = _` mp_tac >>
     simp[NoAsms, step_inst_base_opcode_eqs, mk_inst_def]) >>
  `copy_static (raw with vs_inst_idx := LENGTH sc.cs_current_insts) = copy_static u` by
    (qpat_assum `a = u with vs_inst_idx := _`
       (fn th => qpat_assum `copy_static raw = copy_static a`
         (mp_tac o PURE_REWRITE_RULE[th])) >> simp[NoAsms, copy_static_def]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sc.cs_current_insts`,`Gf`,`tnf`,`root`,`dst`,`u`] >>
  pure_rewrite_tac[venom_state_accfupds, combinTheory.K_THM,
    ghostPcTransportPtrTheory.ptr_covers_inst_idx, ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `op = Var root` SUBST1_TAC >>
      rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC)
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC)
  >- REFL_TAC
  >- (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp raw` mp_tac >>
      pure_rewrite_tac[allocas_below_fmp_def, venom_state_accfupds] >>
      disch_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `allocas_from lo raw` mp_tac >>
      pure_rewrite_tac[allocas_from_def, venom_state_accfupds] >>
      disch_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x. not_fresh_at sb x ==> lookup_var x raw = _ /\ _` mp_tac >>
  pure_rewrite_tac[lookup_var_def, venom_state_accfupds] >>
  disch_tac >> first_assum ACCEPT_TAC
QED

Resume copy_ctor_rhs_endpoint_mods[snapshot]:
  `type_slot_size rt <> 0 ==> !region. ce.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sb region` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all copy_ctor_rhs_snapshot >> strip_tac >>
  Cases_on `type_slot_size rt = 0`
  >- fs[immutable_transfers_def, mem_bytes_at_def] >>
  `w2n src + type_memory_size rt < dimword(:256)` by decide_tac >>
  `regions_disjoint (w2n src) (type_memory_size rt) (w2n dst) (type_memory_size rt)` by
    (rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  drule_all copy_ctor_memory_snapshot >> disch_then (qspec_then `a` assume_tac) >>
  conj_tac
  >- (qspecl_then [`w2n dst`, `mem_bytes_at (w2n src) (type_memory_size rt) s.vs_memory`, `a`]
        mp_tac write_memory_mem_bytes_at_same >> simp[LENGTH_mem_bytes_at]) >>
  qpat_assum `raw.vs_memory = _` SUBST1_TAC >>
  qpat_assum `(immutable_transfers F T src dst _ 0 a).vs_memory = _` SUBST1_TAC >>
  qpat_assum `a.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  irule abi_encode_write_memory_length
QED

Finalise copy_ctor_rhs_endpoint_mods

(* Retain the original nonempty-run interface for existing consumers. *)
Theorem copy_ctor_rhs_run_mods:
  unwrap_value ce (LocatedValue ty p) sb = (op,sc) /\
  ce.ce_is_ctor /\ p.ptr_location = LocCode /\ ~is_word_type ty /\
  type_memory_bytes ce ty = type_memory_size rt /\
  0 < type_memory_size rt /\ type_memory_size rt < dimword(:256) /\
  val_wf rt v /\
  eval_operand p.ptr_operand s = SOME src /\
  op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
  w2n src + type_memory_size rt <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v (w2n src) mem) /\
  stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at_mods D lo d ce cx ee G tn s /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sb /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?z Gf tnf root dst.
    op = Var root /\ eval_operand op z = SOME dst /\
    ptr_covers Gf tnf root z (type_memory_size rt) /\
    FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
    FLOOKUP Gf root = SOME (w2n dst,type_memory_size rt) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    sb.cs_next_id < sc.cs_next_id /\
    (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    w2n dst + type_memory_size rt <= z.vs_alloca_next /\ lo <= w2n dst /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n dst) mem) /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP z.vs_allocas id = SOME entry) /\
    (!id b len. id < sb.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
      regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes s name b len ==>
      b+len <= w2n dst \/ w2n dst+type_memory_size rt <= b) /\
    (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!i. i < w2n dst \/ w2n dst+type_memory_size rt <= i ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    z.vs_requests = s.vs_requests /\
    z.vs_fmp = s.vs_fmp /\ z.vs_initial_fmp = s.vs_initial_fmp /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory
Proof
  strip_tac >> drule_all copy_ctor_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choosel_then [`z`, `Gf`, `tnf`, `root`, `dst`, `u`] strip_assume_tac)) >>
  qexistsl_tac [`z`, `Gf`, `tnf`, `root`, `dst`] >> asm_rewrite_tac[]
QED
