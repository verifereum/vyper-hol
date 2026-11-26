(* Install a flat aggregate copy at the selected local subobject. *)
Theory bodyAssignLocalLayoutInstallAtPathMods
Ancestors
  bodyAssignLocalPreStoreMods bodyAssignLocalStoreCutsMods bodyLocalCopyWritesMods
  bodyAssignLocalInstallMods
  bodyFullMemoryCopy bodyFullPathHistory bodyLocalSnapshotPhysicalMods
  bodyLocalSnapshotResourcesMods memoryLayoutSource memoryLayoutRel
  memoryLayoutDefs memoryValueEncoding valueCopy valueEncodingProps
  vyperPlaceFrames stmtLowering exprLowering context bodyFullShared
  stmtSimDeclMem fragGasOriginPtr loweringPosts bodyPtrDefs
  freshWrites typedMemoryCopy venomInst valueEncodingDefs
  venomState exprLoweringProps compileEnv bodyFullAllocaFresh
  bufferAllocationExecution abiBuiltinAllocation exprSimAlloc exprOpenPrimitives
  bodyPtrMakeArrayAllocBuffer exprSimPtrLiteralBuffer stateRelProj
  bodyMemoryDefs wordArgsPtr stmtSimDefs ptrDiscipline loweringHalt finite_map
  emitHelperProps
Libs
  monadsyntax

Theorem assign_local_layout_install_at_path_mods:
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw)
    ee cur s G tn /\
  local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw) (op,sw)
    sa ee cur s G tn /\
  compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
    (vv_location vv) dty (lowered_value_type cenv e) (type_memory_bytes cenv dty)
    cur = ((),sb) /\
  sty = lowered_value_type cenv e /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  (dty = sty \/ tuple_memory_layout_eq dty sty) /\
  fn_has_code cur sb func /\ fn_inst_ids_distinct func /\
  ((vv_location vv <> SOME LocMemory /\ type_memory_size ptv = 0) ==>
    ~block_is_terminated cur) /\
  ee.gas_obs = [] /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?t Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf) /\
    (\ef. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
      ~block_is_terminated sb /\ cenv_top_ext cenv cenv ef.scopes /\
      stmt_state_rel H ctx func cenv cx ef t /\
      immutable_frame_mods func cenv cx ef t /\
      storage_well_formed_on cx ef (FST H) /\
      return_buf_frame d cenv sb t /\ alloca_history func t /\
      return_buf_sep d cenv ef t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
               FLOOKUP t.vs_allocas aid = SOME a) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv ef t /\
      (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
         (!name b' sz. local_region cenv es.scopes s0 name b' sz ==>
                        a + n <= b' \/ b' + sz <= a) /\
         a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)) (ff with gas_obs := [])
Proof
  BETA_TAC >> pure_once_rewrite_tac[GSYM local_assign_normal_at_cut_mods] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `?H. valid_horizon cx st0 H ff.storage_trace`)
  >- (qexistsl_tac [`s`,`G`,`tn`] >> gen_tac >> disch_tac >>
      qpat_x_assum `~(?H. valid_horizon _ _ H _)` (mp_tac o SIMP_RULE bool_ss []) >>
      disch_then (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `ff.storage_trace = ee.storage_trace /\ (ff with gas_obs := []) = ff` by
    (drule_then (qx_choose_then `sc` SUBST1_TAC) write_memory_place_frame >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_assum `local_assign_here_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  qpat_x_assum `local_assign_store_source_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [local_assign_store_source_mods_def]) >>
  qpat_x_assum `sty = lowered_value_type cenv e` (SUBST_ALL_TAC o SYM) >>
  simp[LET_THM] >> strip_tac >>
  qpat_x_assum `ff.storage_trace = ee.storage_trace` SUBST_ALL_TAC >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `memory_layout_rel ptv stv` by suspend "layout" >>
  `type_memory_size stv = type_memory_size ptv` by fs[memory_layout_rel_def] >>
  `!cs src. compile_store_memory cenv src (FST dst) dty sty cs =
       compile_copy_memory (FST dst) src (type_memory_size ptv) cs` by
    (qpat_assum `dty = sty \/ tuple_memory_layout_eq dty sty` strip_assume_tac >>
     simp[compile_store_memory_def]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (w2n sw) m` by
    suspend "read_layout" >>
  Cases_on `vv_location vv = SOME LocMemory`
  >- suspend "staged" >>
  suspend "direct"
QED

Resume assign_local_layout_install_at_path_mods[layout]:
  markerLib.RESUME_TAC >>
  `memory_layout_key dty = memory_layout_key sty` by
    (qpat_assum `dty = sty \/ tuple_memory_layout_eq dty sty` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac
     >- simp[] >>
     qpat_x_assum `tuple_memory_layout_eq _ _` mp_tac >>
     Cases_on `dty` >> Cases_on `sty` >>
     simp[tuple_memory_layout_eq_def,memory_layout_key_tuple]) >>
  drule_all_then ACCEPT_TAC memory_layout_key_evaluated
QED

Resume assign_local_layout_install_at_path_mods[read_layout]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  irule memory_value_rel_val_in_memory >> conj_tac >- first_assum ACCEPT_TAC >>
  irule memory_layout_rel_value >> qexists_tac `stv` >> simp[] >>
  irule val_in_memory_memory_value_rel >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[staged]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `n = type_memory_size ptv` >>
  `n < dimword (:256)` by decide_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `!cs src. compile_store_memory _ _ _ _ _ _ = _`
    (fn th => simp[compile_assign_value_def,th,comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer n cur = (buf,sm)` >>
  rename1 `compile_copy_memory buf.buf_operand op n sm = (r,sc)` >>
  Cases_on `r` >>
  `ci_mono cur sm /\ ci_mono sm sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,pairTheory.SND] >>
  `fn_has_code cur sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,cs_extends_trans]) >>
  `0 < n ==> ?xs. op = Var xs /\ not_fresh_at cur xs /\
     lookup_var xs s = SOME sw /\ ptr_covers G tn xs s n /\
     w2n sw+n < dimword (:256) /\ w2n sw+n <= s.vs_alloca_next` by
    (strip_tac >> qpat_assum `0 < type_memory_size stv ==> _` mp_tac >>
     simp[eval_operand_def] >> metis_tac[eval_operand_def,arithmeticTheory.ADD_COMM]) >>
  `?u root a Gu tu.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tu)) /\
    (!H : (bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee u) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    lookup_var root u = SOME (n2w a) /\ ptr_covers Gu tu root u n /\
    FLOOKUP u.vs_allocas cur.cs_next_id = SOME (a,n) /\
    MEM (mk_inst cur.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    lo <= a /\ a+n < dimword (:256) /\ a+n <= u.vs_alloca_next /\
    (!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory ptv v a m) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid a len. FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
       FLOOKUP s.vs_allocas aid = SOME (a,len) \/ s.vs_alloca_next <= a) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at cur x ==> not_fresh_at sc x /\ lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!name a len. local_region cenv ee.scopes u name a len <=> local_region cenv ee.scopes s name a len) /\
    (!name b len. local_region cenv ee.scopes s name b len ==> regions_disjoint a n b len) /\
    (!aid b len. aid < cur.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint a n b len) /\
    typed_copy_frame a n s.vs_memory u.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_immutables = s.vs_immutables /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!i. ~(a <= i /\ i < a+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem))` by suspend "snapshot" >>
  suspend "snapshot_resources"
QED

Resume assign_local_layout_install_at_path_mods[snapshot]:
  markerLib.RESUME_TAC >>
  Cases_on `n = 0` >- suspend "snapshot_zero" >>
  `0 < n` by decide_tac >>
  qpat_x_assum `0 < n ==> ?xs. op = _ /\ _`
    (drule_then (qx_choose_then `xs` strip_assume_tac)) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) local_snapshot_physical_mods >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_copy_memory buf.buf_operand (Var xs) _ _ = ((),sc)`)) >>
  disch_then (drule_at (Pat `!m. mem_agree_outside _ _ m ==> val_in_memory ptv v _ m`)) >>
  disch_then (mp_tac o Q.INST [`lo` |-> `lo`, `PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
     (qpat_assum `Abbrev (n = _)` (ACCEPT_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]))])) >>
  disch_then (qx_choosel_then [`u`,`root`,`a`,`Gu`,`tu`] strip_assume_tac) >>
  qexistsl_tac [`u`,`root`,`a`,`Gu`,`tu`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_assum `!name a' len. local_region _ _ u name a' len ==> regions_disjoint _ _ a' len`
    (qspecl_then [`name`,`b'`,`len`] mp_tac) >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[snapshot_zero]:
  markerLib.RESUME_TAC >>
  `sm = sc /\ sc = sb` by fs[compile_copy_memory_def,comp_return_def] >>
  qpat_x_assum `sm = sc` SUBST_ALL_TAC >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (mp_tac o Q.INST [`lo` |-> `lo`,`PG` |-> `PG`,`G` |-> `G`,`tn` |-> `tn`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`,`raw`] strip_assume_tac) >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  `s.vs_memory = u.vs_memory /\ ~u.vs_halted /\
   u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
                        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_halted,z.vs_data_section,
          z.vs_call_ctx,z.vs_accounts,z.vs_transient,z.vs_immutables)``) >> simp[]) >>
  `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (off,sz) \/ s.vs_alloca_next <= off` by
    suspend "zero_alloc_table" >>
  `MEM (mk_inst cur.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func)` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     drule_all buffer_alloc_code >> fs[]) >>
  `!i. i IN tu.t_mem <=> i IN tn.t_mem` by suspend "zero_alloc_taint" >>
  suspend "zero_snapshot_post"
QED

Resume assign_local_layout_install_at_path_mods[zero_alloc_table]:
  markerLib.RESUME_TAC >>
  drule compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `raw = update_var root (n2w (buffer_allocation_base s cur.cs_next_id))
          (buffer_allocation_fields s cur.cs_next_id (w2n (n2w n : bytes32)))` by
    (qpat_x_assum `run_inst_seq _ _ = OK (update_var _ _ _)` mp_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `FLOOKUP u.vs_allocas aid = SOME (_,sz)` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas cur.cs_next_id` >>
  simp[update_var_def,buffer_allocation_fields_def,FLOOKUP_UPDATE] >>
  Cases_on `aid = cur.cs_next_id` >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[zero_alloc_taint]:
  markerLib.RESUME_TAC >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `root = STRING #"%" (toString cur.cs_next_var)` by fs[] >>
  `step_inst_base (mk_inst cur.cs_next_id ALLOCA [Lit (n2w n)] [root]) s = OK raw` by
    (`!i. run_inst_seq [i] s = step_inst_base i s` by
       (gen_tac >> Cases_on `step_inst_base i s` >> simp[run_inst_seq_def]) >>
     qpat_assum `run_inst_seq _ _ = OK raw` mp_tac >>
     qpat_assum `emitted_insts cur sc = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `!i. run_inst_seq [i] s = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `root = _` (fn th => pure_once_rewrite_tac[th]) >>
     simp[]) >>
  `FLOOKUP raw.vs_allocas cur.cs_next_id = SOME (w2n w,n)` by
    (qpat_assum `FLOOKUP u.vs_allocas cur.cs_next_id = SOME _` mp_tac >>
     qpat_assum `u = raw with vs_inst_idx := _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  drule_all literal_alloca_exterior_taint >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[zero_snapshot_post]:
  markerLib.RESUME_TAC >>
  `!name a len. local_region cenv ee.scopes u name a len <=> local_region cenv ee.scopes s name a len` by
    (irule literal_ptr_local_region_frame >> qexists_tac `cur` >> simp[] >>
     rpt strip_tac >> last_x_assum drule >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`stmt_state_rel H0 ctx func cenv cx ee u` by
       (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _`
          (qspec_then `H0` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ _ u`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `!x. not_fresh_at cur x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `cur` >> fs[ci_mono_def]) >>
  `tu.t_mem = tn.t_mem` by simp[pred_setTheory.EXTENSION] >>
  `!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory ptv v (w2n w) m` by
    (rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w2n sw`,`0`,`m`] >>
     qpat_assum `val_wf ptv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
     simp[mem_bytes_at_def] >> disch_tac >>
     qpat_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v _ m`
       (qspec_then `m` irule) >>
     qpat_assum `s.vs_memory = u.vs_memory` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `tu.t_mem = tn.t_mem` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at cur x ==> not_fresh_at sc x /\ lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at sc x`
           (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at cur x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
  `typed_copy_frame (w2n w) n s.vs_memory u.vs_memory` by simp[typed_copy_frame_def] >>
  `!name b' len. local_region cenv ee.scopes s name b' len ==>
     regions_disjoint (w2n w) n b' len` by
    (rpt strip_tac >>
     qpat_assum `!name z len. local_region _ _ u name z len ==> regions_disjoint _ _ z len`
       (qspecl_then [`name`,`b'`,`len`] mp_tac) >> simp[]) >>
  qexistsl_tac [`u`,`root`,`w2n w`,`Gu`,`tu`] >>
  pure_rewrite_tac[wordsTheory.n2w_w2n] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Resume assign_local_layout_install_at_path_mods[snapshot_resources]:
  markerLib.RESUME_TAC >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x` by
    fs[ret_pc_ok_def] >>
  `!x. not_fresh_at cur x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by simp[] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) local_snapshot_resources_mods >>
  disch_then (drule_at (Pat `typed_copy_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `local_ptrs_reserved cenv cur`)) >>
  disch_then (drule_at (Pat `allocas_from lo u`)) >>
  disch_then (mp_tac o Q.INST [`inst` |-> `mk_inst cur.cs_next_id ALLOCA [Lit (n2w n)] [root]`,
    `G` |-> `G`,`Gu` |-> `Gu`,`tn` |-> `tn`,`tu` |-> `tu`] o SPEC_ALL) >>
  (impl_tac >- (simp[mk_inst_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `!name a len i. local_region cenv ee.scopes s name a len /\
     a <= i /\ i < a + len /\ i IN tu.t_mem ==> i IN tn.t_mem` by suspend "snapshot_local_taint" >>
  `ghost_kept_at lo cenv ee cur G tn s Gu tu` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  suspend "snapshot_return"
QED

Resume assign_local_layout_install_at_path_mods[snapshot_local_taint]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qpat_assum `!name b len. local_region _ _ s name b len ==> regions_disjoint _ _ b len`
    (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disch_tac >>
  qpat_assum `!i. ~(a <= i /\ i < a+n) ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[snapshot_return]:
  markerLib.RESUME_TAC >>
  `cur.cs_next_id <= sc.cs_next_id /\ cur.cs_next_var <= sc.cs_next_var /\
   sc.cs_next_var <= sb.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cur` >> simp[]) >>
  `!x w. not_fresh_at cur x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w` by simp[] >>
  `return_buf_frame d cenv sc u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  `return_buf_sep d cenv ee u` by suspend "snapshot_return_sep" >>
  `local_region cenv ee.scopes u id (w2n b) cap` by simp[] >>
  `not_fresh_at cur p` by
    (qpat_assum `local_ptrs_reserved cenv cur`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     qpat_assum `!x y p z z'. FLOOKUP cenv.ce_vars x = SOME (PtrVar (Var p) z) ==> _`
       (drule_at (Pat `FLOOKUP cenv.ce_vars id = _`)) >> simp[]) >>
  `lookup_var p u = SOME b` by
    (qpat_assum `!x. not_fresh_at cur x ==> lookup_var x u = _ /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at sc x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  suspend "staged_copy"
QED

Resume assign_local_layout_install_at_path_mods[snapshot_return_sep]:
  markerLib.RESUME_TAC >>
  irule return_buf_sep_transport >>
  reverse conj_tac >- (qexistsl_tac [`cenv`,`ee`,`s`] >> simp[]) >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  qpat_assum `return_buf_frame (SOME _) _ cur s`
    (strip_assume_tac o SIMP_RULE std_ss [return_buf_frame_def]) >>
  qpat_assum `return_buf_sep (SOME _) _ _ s`
    (assume_tac o CONJUNCT1 o SIMP_RULE std_ss [bodySimFullTheory.return_buf_sep_def]) >>
  simp[allocas_from_def] >> rpt strip_tac >>
  qpat_assum `!aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) ==> _`
    (drule_then strip_assume_tac)
  >- (qpat_assum `allocas_from _ s` (drule_then mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
  decide_tac
QED

Resume assign_local_layout_install_at_path_mods[staged_copy]:
  markerLib.RESUME_TAC >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,Gu,tu) [] (OK t,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory ptv v (w2n dw) m) /\
    typed_copy_state_frame sc (w2n dw) n u t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~block_is_terminated sb /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    (!x. not_fresh_at sc x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x))` by suspend "staged_copy_run" >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
  `alloca_inv s` by
    (drule_then (ACCEPT_TAC o CONJUNCT2) stmt_state_rel_local_ptrs_alloca) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `DF H0` assume_tac) >> drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  suspend "staged_install"
QED

Resume assign_local_layout_install_at_path_mods[staged_copy_run]:
  markerLib.RESUME_TAC >>
  Cases_on `n = 0` >- suspend "staged_copy_zero" >>
  `0 < n` by decide_tac >>
  qpat_x_assum `0 < n ==> ?x. FST dst = _ /\ _`
    (drule_then (qx_choose_then `xd` strip_assume_tac)) >>
  `lookup_var xd s = SOME dw` by fs[eval_operand_def] >>
  `lookup_var xd u = SOME dw /\ not_fresh_at sc xd` by
    (qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at sc x /\ _`
       (qspec_then `xd` mp_tac) >> simp[]) >>
  `ptr_covers Gu tu xd u n` by metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `w2n dw+n <= u.vs_alloca_next /\ w2n dw+n < dimword (:256)` by decide_tac >>
  `w2n (n2w a : bytes32) = a` by (`a < dimword (:256)` by decide_tac >> simp[]) >>
  qpat_x_assum `FST dst = Var xd` SUBST_ALL_TAC >>
  qpat_x_assum `buf.buf_operand = Var root` SUBST_ALL_TAC >>
  `emit_void MCOPY [Var xd;Var root;Lit (n2w n)] sc = ((),sb)` by
    (qspec_then `n` strip_assume_tac arithmeticTheory.num_CASES >>
     qpat_assum `compile_copy_memory (Var xd) (Var root) _ _ = _` mp_tac >>
     qpat_assum `n = SUC _` (fn th => pure_rewrite_tac[th,compile_copy_memory_def]) >>
     rewrite_tac[]) >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  drule_at (Pat `compile_copy_memory (Var xd) (Var root) _ _ = _`) body_full_memory_copy_frame_path >>
  disch_then (drule_at (Pat `lookup_var root u = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var xd u = SOME _`)) >>
  disch_then (mp_tac o Q.INST [`tv` |-> `ptv`, `v` |-> `v`,`lo` |-> `lo`,
    `G` |-> `Gu`,`tn` |-> `tu`,`PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_assum `Abbrev (n = _)` (ACCEPT_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]))])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >> qpat_assum `!x. not_fresh_at sc x ==> lookup_var x t = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[staged_copy_zero]:
  markerLib.RESUME_TAC >>
  `sb = sc /\ sm = sc` by fs[compile_copy_memory_def,comp_return_def] >>
  `~block_is_terminated sb` by (drule compile_alloc_buffer_open >> simp[]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[typed_copy_state_frame_refl,gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >> irule valueCopyTheory.val_in_memory_relocate >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`a`,`0`,`m`] >> simp[mem_bytes_at_def] >>
  qpat_assum `val_wf ptv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
  qpat_assum `Abbrev (n = _)` (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  simp[]
QED

Resume assign_local_layout_install_at_path_mods[staged_install]:
  markerLib.RESUME_TAC >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> qx_gen_tac `H` >> disch_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
   ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u` by
    (rpt conj_tac
     >- (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==> _` irule >> simp[])
     >- (qpat_assum `immutable_frame_mods _ _ _ _ s ==> _` irule >> simp[]) >>
     qpat_assum `!D d. ghost_inv_at_mods D _ d _ _ _ _ _ s ==> _` irule >> simp[]) >>
  qpat_x_assum `w2n dw = w2n b + off` SUBST_ALL_TAC >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac assign_local_install_post_mods) >>
  disch_then (fn th =>
    qpat_assum `write_place cx (MemoryPlace id path) v ee = (INL (),ff)`
      (mp_then (Pat `write_place _ _ _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `typed_copy_state_frame sc _ _ u t`)) >>
  disch_then (fn th =>
    qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ Gu tu u`
      (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ghost_kept_at _ _ ee cur G tn s Gu tu`
      (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (mp_tac o Q.INST [`lctx` |-> `lctx`,`sb` |-> `sb`,
    `Gf` |-> `Gf`,`tf` |-> `tf`] o SPEC_ALL) >>
  suspend "staged_install_post"
QED

Resume assign_local_layout_install_at_path_mods[staged_install_post]:
  markerLib.RESUME_TAC >>
  (impl_tac >-
    (conj_tac >- (strip_tac >> irule local_copy_immutable_frame_mods >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> asm_rewrite_tac[]) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac,
       (qpat_assum `Abbrev (n = _)` (fn th => pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >> simp[])])) >>
  disch_then (qx_choose_then `ce` strip_assume_tac) >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  `alloca_frame cenv es sa s0 cenv ff t` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`s`,`cur`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at cur x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `ghost_kept_at _ _ es _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  rewrite_tac[local_assign_normal_mods_def] >> simp[] >>
  suspend "staged_protected_taint"
QED

Resume assign_local_layout_install_at_path_mods[staged_protected_taint]:
  markerLib.RESUME_TAC >>
  map_every qx_gen_tac [`aid`,`orig_base`,`len`,`i`] >> strip_tac >>
  `i IN tn.t_mem` by
    (qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> i IN tn.t_mem`
       (qspecl_then [`aid`,`orig_base`,`len`,`i`] mp_tac) >>
     (impl_tac >-
       (simp[] >> qpat_assum `alloca_frame _ _ _ _ _ ee s`
          (mp_tac o Q.SPECL [`aid`,`orig_base`,`len`] o REWRITE_RULE [alloca_frame_def]) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (assume_tac o CONJUNCT2) >> rpt strip_tac >>
        first_x_assum (drule_then assume_tac) >> decide_tac)) >> simp[]) >>
  qpat_assum `ghost_kept_at _ _ es _ _ _ _ _ _`
     (mp_tac o Q.SPECL [`aid`,`orig_base`,`len`,`i`] o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[direct]:
  markerLib.RESUME_TAC >>
  `compile_copy_memory (FST dst) op (type_memory_size ptv) cur = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `!cs src. compile_store_memory _ _ _ _ _ _ = _`
       (fn th => simp[compile_assign_value_def,th])) >>
  `w2n dw + type_memory_size ptv <= s.vs_alloca_next` by decide_tac >>
  `w2n dw + type_memory_size ptv < dimword (:256)` by decide_tac >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory ptv v (w2n dw) m) /\
    typed_copy_state_frame cur (w2n dw) (type_memory_size ptv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~block_is_terminated sb /\
    cur.cs_next_var <= sb.cs_next_var /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size ptv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at cur x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` by suspend "direct_run" >>
  suspend "direct_install"
QED

Resume assign_local_layout_install_at_path_mods[direct_run]:
  markerLib.RESUME_TAC >>
  Cases_on `type_memory_size ptv = 0`
  >- suspend "direct_zero" >>
  `0 < type_memory_size ptv` by decide_tac >>
  qpat_x_assum `0 < type_memory_size ptv ==> ?x. FST dst = _ /\ _`
    (drule_then (qx_choose_then `xd` strip_assume_tac)) >>
  `0 < type_memory_size stv` by decide_tac >>
  qpat_x_assum `0 < type_memory_size stv ==> (?x. op = _ /\ _) /\ _`
    (drule_then strip_assume_tac) >>
  rename1 `op = Var xs` >>
  `lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw` by fs[eval_operand_def] >>
  `ptr_covers G tn xs s (type_memory_size ptv) /\
   w2n sw + type_memory_size ptv < dimword (:256) /\
   w2n sw + type_memory_size ptv <= s.vs_alloca_next` by
    (qpat_assum `type_memory_size stv = type_memory_size ptv`
       (fn th => pure_once_rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_x_assum `FST dst = Var xd` SUBST_ALL_TAC >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `emit_void MCOPY [Var xd;Var xs;Lit (n2w (type_memory_size ptv))] cur = ((),sb)` by
    (qpat_assum `compile_copy_memory (Var xd) (Var xs) _ _ = _` mp_tac >>
     Cases_on `type_memory_size ptv` >> fs[compile_copy_memory_def]) >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  `cur.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`Var xd`,`Var xs`,`type_memory_size ptv`,`cur`]
       ci_mono_compile_copy_memory) >> simp[ci_mono_def]) >>
  suspend "direct_positive"
QED

Resume assign_local_layout_install_at_path_mods[direct_zero]:
  markerLib.RESUME_TAC >>
  `sb = cur` by fs[compile_copy_memory_def,comp_return_def] >>
  `~block_is_terminated sb` by simp[] >>
  qexistsl_tac [`s`,`G`,`tn`] >>
  simp[typed_copy_state_frame_refl,gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >>
  irule valueCopyTheory.val_in_memory_relocate >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w2n sw`,`0`,`m`] >> simp[mem_bytes_at_def] >>
  qpat_assum `val_wf ptv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[direct_positive]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) body_full_memory_copy_frame_path >>
  disch_then (drule_at (Pat `!m. mem_agree_outside _ _ m ==> val_in_memory ptv v (w2n sw) m`)) >>
  disch_then (mp_tac o Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `PG` |-> `PG`, `lo` |-> `lo`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume assign_local_layout_install_at_path_mods[direct_install]:
  markerLib.RESUME_TAC >>
  `alloca_inv s` by
    (drule_then (ACCEPT_TAC o CONJUNCT2) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H0` assume_tac) >> drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `w2n dw = w2n b + off` SUBST_ALL_TAC >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> qx_gen_tac `H` >> disch_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) assign_local_install_post_mods >>
  disch_then (fn th =>
    qpat_assum `write_place cx (MemoryPlace id path) v ee = (INL (),ff)`
      (mp_then (Pat `write_place _ _ _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (mp_tac o Q.INST [`lctx` |-> `lctx`,`sb` |-> `sb`,
    `Gf` |-> `Gf`,`tf` |-> `tf`] o SPEC_ALL) >>
  suspend "direct_install_post"
QED

Resume assign_local_layout_install_at_path_mods[direct_install_post]:
  markerLib.RESUME_TAC >>
  (impl_tac >-
    (conj_tac >- (strip_tac >> irule local_copy_immutable_frame_mods >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      asm_rewrite_tac[]) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
  disch_then (qx_choose_then `ce` strip_assume_tac) >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  rewrite_tac[local_assign_normal_mods_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise assign_local_layout_install_at_path_mods
