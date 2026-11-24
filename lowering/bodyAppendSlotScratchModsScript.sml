(* The scratch allocation and copy occur before the reached array guard. *)
Theory bodyAppendSlotScratchMods
Ancestors
  arithmetic finite_map pred_set words pair assignPlaceLayout
  assignTuplePtrCopyLen exprSimStorageCopy bodyFullMemoryStore
  bodyFullMemorySameTypeStore bodyDeclMemoryCore immutableDeployAssignRanges
  memoryLocalRhsProps valueCopyBytes reasonCopySourcePtr
  bodyFullAllocaFresh bodyPtrMakeArrayCopyStateFrame bodyMemBopRestWordPath
  bodyFullHashKeccakFixed loweringHalt fragGasOriginPtr fragGasOrigin
  bodyPtrMakeArrayAllocBuffer bodyLocalSnapshotResourcesMods
  bufferAllocationExecution abiBuiltinAllocation bodyFullPostsMods
  bodyMemoryDefs bodyPtrDefs compileEnv context emitHelperProps
  exprLoweringProps exprSimAlloc exprSimProps fragExec fragGasOriginPtrLoop
  freshWrites localPtrsProps loweringPosts loweringStateRelDefs ptrDiscipline
  robustCopyTransportPtr stmtSimDefs typedMemoryCopy typedCopyOriginPtrBase venomState venomMemDefs

(* Normalize the actual emitted store. Bytestring widening reads the stored
   payload size, not the larger declared capacity. *)
Theorem append_scratch_copy_path[local]:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (~is_bytestring_type sty ==> w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_bytestring_type sty` >- suspend "bytes" >>
  `val_store_size stv v = type_memory_size stv` by
    metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring] >>
  mp_tac (SPEC_ALL body_full_memory_store_path) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[]
QED

Resume append_scratch_copy_path[bytes]:
  `is_bytestring_type dty` by metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `~is_word_type sty` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `compile_store_memory cenv (Var xs) (Var xd) sty sty sa = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  `arg_type_fits sty dty` by fs[vyperTypeSystemTheory.type_widens_to_def] >>
  `type_memory_bytes cenv sty <= type_memory_bytes cenv dty` by
    simp[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_memory_bytes] >>
  `type_memory_size stv <= type_memory_size dtv` by fs[] >>
  `0 < type_memory_size stv` by
    (qspecl_then [`tenv`,`sty`,`stv`] mp_tac valueCopyBytesTheory.bytestring_type_value >>
     simp[] >> strip_tac >> simp[valueEncodingTheory.type_memory_size_def]) >>
  `type_memory_size stv + 64 < dimword (:256)` by decide_tac >>
  `ptr_covers G tn xd s (type_memory_size stv)` by
    metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
  `w2n dw + type_memory_size stv < dimword (:256) /\
   w2n dw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  drule_all body_full_memory_same_type_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n dw`,`type_memory_size stv`] >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  (simp[] >- (rpt strip_tac >> metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer])) >>
  rpt strip_tac >> `~(w2n dw <= i /\ i < w2n dw+type_memory_size stv)` by decide_tac >> simp[]
QED

Finalise append_scratch_copy_path[local]

Theorem append_scratch_physical[local]:
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
  compile_store_memory cenv (Var xs) buf.buf_operand dty sty sm = ((),sb) /\
  ~is_word_type sty /\ ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  type_memory_size dtv + 64 < dimword (:256) /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
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
    lookup_var root u = SOME (n2w b) /\ ptr_covers Gu tu root u (type_memory_size dtv) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,type_memory_size dtv) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))] [root]) (fn_insts func) /\
    lo <= b /\ b + type_memory_size dtv < dimword (:256) /\
    b + type_memory_size dtv <= u.vs_alloca_next /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory dtv v b mem) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ alloca_history func u /\
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
    (!name a len. local_region cenv es.scopes s name a len ==>
      loweringStateRelDefs$regions_disjoint b (type_memory_size dtv) a len) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      loweringStateRelDefs$regions_disjoint b (type_memory_size dtv) a len) /\
    typed_copy_frame b (type_memory_size dtv) s.vs_memory u.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_immutables = s.vs_immutables /\ u.vs_labels = s.vs_labels /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!i. ~(b <= i /\ i < b+type_memory_size dtv) ==> (i IN tu.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = type_memory_size dtv` >>
  `n < dimword (:256)` by decide_tac >>
  qpat_x_assum `compile_alloc_buffer (type_memory_bytes _ _) _ = _`
    (mp_tac) >>
  qpat_assum `type_memory_bytes cenv dty = n`
    (fn th => pure_rewrite_tac[th]) >> disch_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `sm`,`H` |-> `H0`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
      alloc_buffer_origin_ptr_path_with_raw_endpoint))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`a`,`Ga`,`ta`,`raw`] strip_assume_tac) >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  `s.vs_memory = a.vs_memory /\ ~a.vs_halted /\
   a.vs_data_section = s.vs_data_section /\ a.vs_call_ctx = s.vs_call_ctx /\
   a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
   a.vs_immutables = s.vs_immutables /\ a.vs_labels = s.vs_labels` by
    (qpat_assum `a with <|vs_vars := _; vs_allocas := _;
                        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_halted,z.vs_data_section,
          z.vs_call_ctx,z.vs_accounts,z.vs_transient,z.vs_immutables,z.vs_labels)``) >> simp[]) >>
  `!aid off sz. FLOOKUP a.vs_allocas aid = SOME (off,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off` by
    suspend "alloc_table" >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> drule_all buffer_alloc_code >> fs[]) >>
  `!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by
    suspend "alloc_taint" >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm xs /\ lookup_var xs a = SOME sw` by simp[] >>
  `!name off len. local_region cenv es.scopes a name off len <=>
    local_region cenv es.scopes s name off len` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `!name off len. local_region cenv es.scopes s name off len ==>
    loweringStateRelDefs$regions_disjoint (w2n w) n off len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes a name off len` by simp[] >>
     qpat_assum `!name off len. local_region _ _ a _ _ _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem` by suspend "source" >>
  `~is_bytestring_type sty ==> w2n sw + type_memory_size stv <= w2n w \/
    w2n w+n <= w2n sw` by suspend "separation" >>
  suspend "copy"
QED

Resume append_scratch_physical[alloc_table]:
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

Resume append_scratch_physical[alloc_taint]:
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) s = OK raw` by
    (qpat_x_assum `run_inst_seq _ _ = OK raw` mp_tac >>
     fs[run_inst_seq_def,AllCaseEqs()]) >>
  `FLOOKUP raw.vs_allocas sa.cs_next_id = SOME (w2n w,n)` by
    (qpat_assum `FLOOKUP a.vs_allocas sa.cs_next_id = SOME _` mp_tac >>
     qpat_assum `a = raw with vs_inst_idx := _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  drule_all literal_alloca_exterior_taint >> simp[NOT_LESS, NOT_LESS_EQUAL]
QED

Resume append_scratch_physical[source]:
  mp_tac (Q.SPECL [`tn.t_mem`,`ta.t_mem`,`s.vs_memory`,`a.vs_memory`,
    `{i | w2n (w:bytes32) <= i /\ i < w2n w+n}`,`stv`,`v`,`w2n (sw:bytes32)`]
    robust_val_in_memory_exterior_frame) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >>
     qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (mp_tac o Q.SPEC `stv` o REWRITE_RULE [expr_val_at_def]) >>
     simp[eval_operand_def] >> strip_tac
     >- (qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
           (drule_all_then mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
     >- (qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _`
           (drule_then mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     fs[])) >> simp[]
QED

Resume append_scratch_physical[separation]:
  strip_tac >>
  `eval_operand (Var xs) s = SOME sw` by simp[eval_operand_def] >>
  drule_all immutable_assign_nonbytes_source_owned >> strip_tac
  >- (`n = 0` by
        (spose_not_then assume_tac >> `0 < type_memory_size dtv` by simp[Abbr `n`] >>
         drule_all widening_source_memory_size_pos >> simp[]) >> simp[])
  >- (qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
        (drule_all_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _` (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume append_scratch_physical[copy]:
  markerLib.RESUME_TAC >>
  `ptr_covers Ga ta xs a (type_memory_size stv)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp a` by
    (`stmt_state_rel H0 ctx func cenv cx es a` by simp[] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `lo <= a.vs_alloca_next /\ w2n sw + val_store_size stv v <= a.vs_alloca_next`
    by decide_tac >>
  `compile_store_memory cenv (Var xs) (Var root) dty sty sm = ((),sb)` by
    (qpat_assum `compile_store_memory _ _ buf.buf_operand _ _ _ = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var root` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  qpat_assum `compile_store_memory cenv (Var xs) (Var root) _ _ _ = _`
    (mp_then Any mp_tac append_scratch_copy_path) >>
  disch_then (drule_at (Pat `ptr_covers Ga ta xs a _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `value_has_type stv v`)) >>
  disch_then (drule_at (Pat `fn_has_code sm sb _`)) >>
  disch_then (drule_at (Pat `allocas_from _ a`)) >>
  disch_then (mp_tac o Q.INST [`explicit` |-> `explicit`, `ctx` |-> `ctx`,
    `PG` |-> `PG`, `dw` |-> `w:bytes32`] o SPEC_ALL) >>
  qpat_assum `Abbrev (n = _)`
    (fn th => pure_rewrite_tac[SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac) >>
  suspend "frame"
QED

Resume append_scratch_physical[frame]:
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
   u.vs_immutables = a.vs_immutables /\ u.vs_labels = a.vs_labels` by
    (qpat_assum `copy_static u = copy_static a`
       (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next,z.vs_data_section,
           z.vs_call_ctx,z.vs_accounts,z.vs_transient,z.vs_immutables,z.vs_labels)``) >>
     SIMP_TAC (srw_ss()) [copy_static_def]) >>
  `!H : (bool # 256 word # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es s ==>
    stmt_state_rel H ctx func cenv cx es u` by suspend "copy_state" >>
  `alloca_history func u` by suspend "history" >>
  suspend "assemble"
QED

Resume append_scratch_physical[copy_state]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`sa.cs_next_id`,`w2n (w:bytes32)`,`n`,`root`,`sa`,`sm`,`a`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (first_assum irule >> first_assum ACCEPT_TAC)]
QED

Resume append_scratch_physical[history]:
  markerLib.RESUME_TAC >>
  `alloca_inv s` by (drule rest_word_state_alloca_inv >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
    (qspec_then `cx_dead H0 cx` (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
  drule gas_origin_path_erase >> strip_tac >>
  drule_all rest_word_marked_allocation_posts >> simp[]
QED

Resume append_scratch_physical[assemble]:
  markerLib.RESUME_TAC >>
  `ci_mono sm sb` by
    (qpat_assum `compile_store_memory cenv (Var xs) (Var root) _ _ _ = _`
       (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp[ci_mono_compile_store_memory]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def]) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `lookup_var root u = SOME w /\ ptr_covers Gu tu root u n` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _ /\ _`
       (qspec_then `root` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     (conj_tac >- (asm_rewrite_tac[])) >>
     irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`a`,`ta`] >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at sa x ==>
    not_fresh_at sb x /\ lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `not_fresh_at sm x` by simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var _ _ = _ /\ _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >>
     simp[]) >>
  `!name off len. local_region cenv es.scopes u name off len <=>
    local_region cenv es.scopes s name off len` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> (i IN tu.t_mem <=> i IN ta.t_mem)` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. _ ==> (i IN ta.t_mem <=> i IN tn.t_mem)` (qspec_then `i` mp_tac) >> simp[]) >>
  `typed_copy_frame (w2n w) n s.vs_memory u.vs_memory` by
    (qpat_assum `s.vs_memory = a.vs_memory` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`u`,`root`,`w2n (w:bytes32)`,`Gu`,`tu`] >> pure_rewrite_tac[n2w_w2n] >>
  qpat_assum `u.vs_allocas = a.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u.vs_alloca_next = a.vs_alloca_next` (fn th => pure_rewrite_tac[th]) >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo a` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `u.vs_allocas = a.vs_allocas`
       (fn th => SIMP_TAC bool_ss [allocas_from_def,th])) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Finalise append_scratch_physical[local]

(* The buffer, saved operands and linked resources are at the same endpoint,
   with the physical path chosen before the horizon. *)
Theorem append_slot_scratch_ready_mods:
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
  compile_store_memory cenv (Var xs) buf.buf_operand dty sty sm = ((),sb) /\
  ~is_word_type sty /\ ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  type_memory_size dtv + 64 < dimword (:256) /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  expr_val_at cenv cx sty start sa es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) ==>
  ?u root b Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    lookup_var root u = SOME (n2w b) /\ ptr_covers Gu tu root u (type_memory_size dtv) /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\ op_taint tu buf.buf_operand = {} /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,type_memory_size dtv) /\
    sa.cs_next_id < sb.cs_next_id /\
    lo <= b /\ b + type_memory_size dtv < dimword (:256) /\
    b + type_memory_size dtv <= u.vs_alloca_next /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory dtv v b mem) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ alloca_history func u /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      not_fresh_at sb x /\ lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s /\ op_taint tu op = op_taint tn op) /\
    (!name off len. local_region cenv es.scopes u name off len ==>
      loweringStateRelDefs$regions_disjoint b (type_memory_size dtv) off len) /\
    typed_copy_frame b (type_memory_size dtv) s.vs_memory u.vs_memory /\
    (!i. ~(b <= i /\ i < b+type_memory_size dtv) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tu.t_mem <=> i IN tn.t_mem)) /\
    (!aid off len i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) /\
      off <= i /\ i < off+len ==> (i IN tu.t_mem <=> i IN tn.t_mem)) /\
    u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_immutables = s.vs_immutables /\ u.vs_labels = s.vs_labels /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (immutable_frame_mods func cenv cx es s ==> immutable_frame_mods func cenv cx es u) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx es G tn s ==>
      ghost_inv_at_mods D lo d cenv cx es Gu tu u) /\
    (!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sb u) /\
    alloca_frame cenv es sa s cenv es u /\ ghost_kept_at lo cenv es sa G tn s Gu tu
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`H0` |-> `H0`] (SPEC_ALL append_scratch_physical)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`root`,`b`,`Gu`,`tu`] strip_assume_tac) >>
  qabbrev_tac `n = type_memory_size dtv` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]` >>
  `MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (b,n)` by simp[Abbr `inst`,venomInstTheory.mk_inst_def] >>
  mp_tac (Q.INST [`H0` |-> `H0`, `ce` |-> `cenv`, `mid` |-> `es`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] local_snapshot_resources_mods))) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >>
  suspend "resources"
QED

Resume append_slot_scratch_ready_mods[resources]:
  markerLib.RESUME_TAC >>
  `ci_mono sm sb` by
    (qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o REWRITE_RULE [pairTheory.SND] o
        AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp[ci_mono_compile_store_memory]) >>
  `sm.cs_next_id = sa.cs_next_id + 1 /\ sm.cs_next_var = sa.cs_next_var + 1` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!d. return_buf_frame d cenv sa s ==> return_buf_frame d cenv sb u` by
    (rpt strip_tac >> irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s /\ op_taint tu op = op_taint tn op` by
    (Cases >> simp[eval_operand_def] >> rw[] >> simp[op_taint_def]) >>
  `eval_operand buf.buf_operand u = SOME (n2w b) /\ op_taint tu buf.buf_operand = {}` by
    (simp[eval_operand_def] >> fs[ptr_covers_def]) >>
  `!name off len. local_region cenv es.scopes u name off len ==>
    loweringStateRelDefs$regions_disjoint b n off len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s name off len` by
       (qpat_assum `!name off len. local_region _ _ u _ _ _ <=> _`
          (qspecl_then [`name`,`off`,`len`] (irule o iffLR)) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!name off len. local_region _ _ s _ _ _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  suspend "exterior"
QED

Resume append_slot_scratch_ready_mods[exterior]:
  markerLib.RESUME_TAC >>
  `!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >>
     qpat_assum `typed_copy_frame b n _ _`
       (qspecl_then [`i`,`1`] mp_tac o CONJUNCT1 o REWRITE_RULE [typed_copy_frame_def]) >>
     `i+1 <= b \/ b+n <= i` by decide_tac >> simp[]) >>
  `!aid off len i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) /\
    off <= i /\ i < off+len ==> (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!aid off len. aid < sa.cs_next_id /\ _ ==> _` (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disch_tac >>
     `~(b <= i /\ i < b+n)` by decide_tac >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s Gu tu` by suspend "kept" >>
  qexistsl_tac [`u`,`root`,`b`,`Gu`,`tu`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Resume append_slot_scratch_ready_mods[kept]:
  markerLib.RESUME_TAC >> pure_rewrite_tac[ghost_kept_at_def] >> rpt strip_tac >> simp[]
  >- (qpat_assum `!aid off len i. FLOOKUP _ aid = SOME (off,len) /\ _ ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  qpat_assum `!name off len. local_region _ _ s _ _ _ ==> _` (drule_then assume_tac) >>
  `~(b <= i /\ i < b+n)` by (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!i. ~(b <= i /\ i < b+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem)`
    (qspec_then `i` (drule_then (irule o iffLR))) >> first_assum ACCEPT_TAC
QED

Finalise append_slot_scratch_ready_mods
