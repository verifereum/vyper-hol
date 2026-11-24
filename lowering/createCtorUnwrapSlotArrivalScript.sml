(* The slot unwrap's own allocation and copy, in their emitted ID band. *)
Theory createCtorUnwrapSlotArrival
Ancestors
  createCtorUnwrapSlotPost createCtorSlotLoopOriginBand createCtorStraightBand
  bodyFullUnwrapSlotOrigin exprPtrUnwrapLoopEntry exprPtrUnwrapEnsureShape
  exprPtrUnwrapSingleSegment abiBufferAllocationCode stmtReasonLitFragMemory
  exprPtrUnwrapStorage loweringPosts localPtrsProps vyperStorageFootprint
  fragGasOriginPtr ptrSafetyTransport bufferAllocationExecution venomMemProofs
  allocaHistory bodyBinopFragMemory copyExecution relation rich_list arithmetic
  venomExecSemantics venomInst venomState exprSimStorageCopy fragExec compileEnv
  exprLoweringProps exprLowering finite_map words emitHelper list ptrDiscipline
  loweringStateRelDefs venomMemDefs context bodyPtrDefs exprSimProps
  exprSimPtrTopLevelStorageCopy exprPtrUnwrapAllocSemantic abiPathAllocInv
  freshWrites valueEncodingProps exprSimFieldLayout gasOriginPtrLabels allocationPtr
  exprSimAlloc vyperStorageTrace bodyFullHashKeccakFixed loweringHalt exprPtrUnwrapAllocEntry

Theorem ctor_slot_band_join[local]:
  lo <= mid /\ mid <= hi /\
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      lo <= i.inst_id /\ i.inst_id < mid /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s a /\
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid <= i.inst_id /\ i.inst_id < hi /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      lo <= i.inst_id /\ i.inst_id < hi /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z
Proof
  strip_tac >> irule RTC_TRANS >> qexists_tac `a` >> conj_tac
  >- (irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem ctor_slot_alloc_band[local]:
  compile_alloc_buffer nb sa = (buf,mid) /\ fn_has_code sa mid func /\
  buf.buf_operand = Var root /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sa.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  qpat_assum `buf.buf_operand = Var root` mp_tac >> simp[] >> strip_tac >>
  `LENGTH (emitted_insts sa mid) = 1` by simp[] >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sa.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa mid))` by
    (irule ctor_straight_band_run >>
     reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> gvs[]) >>
     fs[run_inst_seq_def,mk_inst_def,is_terminator_def]) >>
  gvs[ADD1,ADD_COMM]
QED

Theorem ctor_single_slot_band:
  (load = SLOAD \/ load = TLOAD) /\
  (do v <- emit_op load [src]; emit_void MSTORE [Var root; v] od) mid = ((),sc) /\
  fn_has_code mid sc func /\
  eval_operand src a = SOME key /\ op_taint tn src = {} /\
  not_fresh_at mid root /\ ptr_covers G tn root a 32 /\
  lookup_var root a = SOME dst /\ allocas_from lo a /\ w2n dst + 32 <= a.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\ alloca_history func a /\
  ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?Gf tnf z.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G,tn) [] (OK z,Gf,tnf) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
    mid.cs_next_id <= sc.cs_next_id /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ ~z.vs_halted /\ z.vs_alloca_next = a.vs_alloca_next /\
    z = (mstore (w2n dst) (slot_copy_word load a key)
      (update_var (STRING #"%" (toString mid.cs_next_var)) (slot_copy_word load a key) a)
      with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    tnf.t_mem = (tn.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
      {w2n dst+b | b IN key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule storage_copy_word_layout >> strip_tac >>
  `sc.cs_next_id = mid.cs_next_id + 2` by
    (qpat_x_assum `(do v <- _; _ od) _ = _` mp_tac >>
     simp[emit_op_def,emit_void_def,emit_def,fresh_var_def,fresh_id_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[]) >>
  `root <> STRING #"%" (toString mid.cs_next_var)` by simp[] >>
  drule_all unwrap_single_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (a,G,tn) [] (OK z,Gf,tnf)` >>
  suspend "single_band"
QED

Resume ctor_single_slot_band[single_band]:
  `sc.cs_current_bb = mid.cs_current_bb /\
   sc.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid sc` by
    gvs[same_blocks_def,emitted_insts_def,IS_PREFIX_APPEND,DROP_LENGTH_APPEND] >>
  drule_all fn_has_code_code >> strip_tac >>
  `LENGTH sc.cs_current_insts = a.vs_inst_idx + LENGTH (emitted_insts mid sc)` by simp[] >>
  `?t. run_inst_seq (emitted_insts mid sc) a = OK t /\
       z = t with vs_inst_idx := LENGTH sc.cs_current_insts` by
    (drule_all copy_single_slot_segment >>
     disch_then (qspecl_then [`mid.cs_next_id`,`func`,`PG`,`D`] strip_assume_tac) >>
     rename1 `run_inst_seq [_; _] a = OK t` >> qexists_tac `t` >> simp[]) >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z` by
    (qpat_assum `z = t with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `LENGTH sc.cs_current_insts = _` SUBST1_TAC >>
     irule ctor_straight_band_run >>
     reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> gvs[]) >>
     Cases_on `load = SLOAD` >> fs[mk_inst_def,is_terminator_def]) >>
  suspend "single_history"
QED

Resume ctor_single_slot_band[single_history]:
  `z.vs_allocas = a.vs_allocas /\ z.vs_current_bb = a.vs_current_bb /\
   ~z.vs_halted /\ z.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `z = (mstore _ _ _) with vs_inst_idx := _` SUBST1_TAC >>
     simp[NoAsms,mstore_def,write_memory_with_expansion_def,update_var_def] >> simp[]) >>
  `alloca_history func z` by
    (qpat_assum `isPREFIX (emitted_insts mid sc) _`
       (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts mid sc)` by
       (Cases_on `load = SLOAD` >> fs[mk_inst_def]) >>
     `lookup_block a.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     `DROP a.vs_inst_idx bb.bb_instructions = emitted_insts mid sc ++ l` by simp[] >>
     drule_all alloca_history_no_alloca_slice >>
     qpat_assum `LENGTH sc.cs_current_insts = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`z`] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[]]
QED

Finalise ctor_single_slot_band[local]

(* Physical witness shared by the constructor and the scoped stage client.
   The RTC and pointer path have the very same endpoint and exit ghosts. *)
Theorem ctor_ensure_slot_band_execution:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s /\ fn_inst_ids_distinct func /\
  (n <> 1 ==> !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
                    phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    RTC (\r z. ?i. ctor_segment_fetch func r = SOME i /\
      sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME z) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (n <> 1 ==> ?cv ds.
      toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
      (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted) /\
    (n = 1 ==>
      t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
        (update_var (STRING #"%" (toString sm.cs_next_var))
          (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
            with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
        {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
      tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
      (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ensure_slot_memory_split >>
  disch_then (qx_choosel_then [`buf`,`sm`] strip_assume_tac) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by suspend "registered" >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`,`G`,`D`]
    (qx_choosel_then [`root`,`d`,`a`,`G0`,`tn0`,`u`] strip_assume_tac)) >>
  drule_all unwrap_alloc_origin_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,`D`]
    (qx_choosel_then [`out`,`u1`] strip_assume_tac)) >>
  `out = root` by fs[] >> qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u1 = u` by fs[] >> qpat_x_assum `u1 = u` SUBST_ALL_TAC >>
  `allocas_from lo a` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
       (mp_then Any (qspec_then `lo` mp_tac) (Q.GEN `lower` member_origin_allocas_from)) >> simp[]) >>
  `alloca_history func a` by (drule_all unwrap_alloc_origin_history >> simp[]) >>
  `not_fresh_at sm root /\ sa.cs_next_id <= sm.cs_next_id` by
    (conj_tac
     >- (drule storage_copy_alloc_layout >> strip_tac >> metis_tac[]) >>
     drule compile_alloc_buffer_code >> simp[]) >>
  `op = Var root` by fs[] >> suspend "allocation_bounds"
QED

Resume ctor_ensure_slot_band_execution[registered]:
  drule compile_alloc_buffer_extends >> strip_tac >>
  `cs_extends sm sb` by
    (Cases_on `n = 1`
     >- (qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >>
         disch_then (strip_assume_tac o MATCH_MP storage_copy_word_layout) >>
         fs[same_blocks_def,cs_extends_same_block]) >>
     qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
     drule_all compile_slot_to_memory_boundary >> simp[]) >>
  drule_all fn_has_code_split >> simp[]
QED

Resume ctor_ensure_slot_band_execution[allocation_bounds]:
  `w2n d + 32*n <= a.vs_alloca_next` by suspend "buffer_frontier" >>
  `s.vs_alloca_next <= a.vs_alloca_next` by
    (qpat_assum `a = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms,buffer_allocation_fields_def,update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    (drule compile_alloc_buffer_code >> strip_tac >>
     metis_tac[not_fresh_at_mono,DECIDE ``x <= x+1``]) >>
  `RTC (\r z. ?i. ctor_segment_fetch func r = SOME i /\
       sa.cs_next_id <= i.inst_id /\ i.inst_id < sm.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME z) s a` by
    (qpat_assum `a = _` SUBST1_TAC >> irule ctor_slot_alloc_band >>
     simp[] >> qexistsl_tac [`buf`,`nb`,`root`] >> simp[]) >>
  Cases_on `n = 1` >- suspend "singleton" >> suspend "loop"
QED

Resume ctor_ensure_slot_band_execution[buffer_frontier]:
  `alloca_next_valid s` by fs[stmt_state_rel_def,alloca_inv_def] >>
  qpat_assum `a = _` SUBST1_TAC >>
  qpat_assum `u = _` SUBST1_TAC >> qpat_assum `d = _` SUBST1_TAC >>
  simp[update_var_def,buffer_allocation_fields_def,buffer_allocation_base_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (simp[] >> irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next + 32*n` >> simp[MOD_LESS_EQ]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> strip_tac >>
  qpat_x_assum `alloca_next_valid s` (mp_tac o REWRITE_RULE[alloca_next_valid_def]) >>
  disch_then drule >> simp[MOD_LESS_EQ] >> decide_tac
QED

Resume ctor_ensure_slot_band_execution[singleton]:
  qpat_assum `n = 1` (fn nth =>
    qpat_assum `buf.buf_operand = Var root` (fn bth =>
      qpat_x_assum `if n = 1 then _ else _` (assume_tac o REWRITE_RULE[nth,bth]))) >>
  `32 <= nb /\ w2n d + 32 <= a.vs_alloca_next` by fs[] >>
  Q.SUBGOAL_THEN
    `(if loc = LocStorage then SLOAD else TLOAD) = SLOAD \/
     (if loc = LocStorage then SLOAD else TLOAD) = TLOAD` assume_tac
  >- (Cases_on `loc = LocStorage` >> simp[]) >>
  `ptr_covers G0 tn0 root a 32` by fs[] >>
  drule_all ctor_single_slot_band >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`]
    (qx_choosel_then [`Gf`,`tnf`,`t`] strip_assume_tac)) >>
  suspend "finish_single"
QED

Resume ctor_ensure_slot_band_execution[loop]:
  qpat_assum `n <> 1` (fn nth =>
    qpat_assum `buf.buf_operand = Var root` (fn bth =>
      qpat_x_assum `if n = 1 then _ else _` (strip_assume_tac o REWRITE_RULE[nth,bth]))) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  `compile_word_copy_loop src (Var root) n loc LocMemory F sm = (lab,sb)` by
    fs[compile_slot_to_memory_def] >>
  `?exitbb. lookup_block sb.cs_current_bb func.fn_blocks = SOME exitbb /\
     phi_prefix_length exitbb.bb_instructions = 0` by fs[fn_has_code_def] >>
  `lookup_var root a = SOME (n2w (w2n d))` by simp[] >>
  drule_all ctor_slot_loop_origin_band >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`]
    (qx_choosel_then [`t`,`Gf`,`tnf`,`cv`,`ds`] strip_assume_tac)) >>
  `copy_static t = copy_static a` by
    fs[toplevel_copy_inv_def,storage_copy_inv_def,copy_prefix_def,storage_copy_frame_def] >>
  drule copy_static_fields >> strip_tac >>
  `alloca_history func t` by
    (irule alloca_history_jump >> conj_tac >- simp[] >>
     qexists_tac `a` >> simp[]) >>
  suspend "finish_loop"
QED

fun finish_slot_band () =
  `RTC (\r z. ?i. ctor_segment_fetch func r = SOME i /\
       sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME z) s t` by
    (irule ctor_slot_band_join >> qexistsl_tac [`a`,`sm.cs_next_id`] >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >> gvs[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `t.vs_alloca_next = a.vs_alloca_next` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0)` by
    metis_tac[] >>
  qexistsl_tac [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC);

Resume ctor_ensure_slot_band_execution[finish_single]:
  finish_slot_band () >> Cases_on `loc = LocStorage` >> simp[]
QED

Resume ctor_ensure_slot_band_execution[finish_loop]:
  `sm.cs_next_id <= sb.cs_next_id` by simp[] >>
  finish_slot_band () >>
  qpat_assum `n <> 1` (fn th => simp[NoAsms,th]) >>
  qexistsl_tac [`cv`,`ds`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ctor_ensure_slot_band_execution

Theorem ctor_unwrap_slot_arrival:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==> w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qabbrev_tac `tr = (p.ptr_location = LocTransient)` >>
  `p.ptr_location = slot_loc tr` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >> simp[slot_loc_def,Abbr `tr`]) >>
  qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any (drule_then strip_assume_tac) vv_post_storage_source) >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  qabbrev_tac `nb = type_memory_bytes cenv (post_value_type cenv e)` >>
  qabbrev_tac `n = type_slot_size rty` >>
  `nb = type_memory_size rty /\ nb = 32*n` by simp[Abbr `nb`, Abbr `n`,type_memory_size_slots] >>
  `nb < dimword(:256) /\ n < 2**256` by fs[dimword_def] >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
        cenv.ce_is_ctor cenv.ce_imm_alloca sb = (op,sc)` by
    (qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     gvs[unwrap_value_def,slot_count_of_memory_size,slot_loc_def,Abbr `n`,Abbr `nb`]) >>
  qunabbrev_tac `tr` >>
  `32*n <= nb` by simp[] >>
  `n <> 1 ==> !bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
                    phi_prefix_length bb.bb_instructions = 0` by simp[] >>
  drule_all ctor_ensure_slot_band_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    (qx_choosel_then [`root`,`dst`,`allocated`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`]
       strip_assume_tac)) >>
  `nb = type_memory_bytes cenv (post_value_type cenv e) /\
   n = type_slot_size rty` by simp[Abbr `nb`,Abbr `n`] >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[] >>
  drule_all ctor_unwrap_slot_endpoint_post >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`v`,`z`,`Gf`,`tnf`] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> irule LESS_EQ_TRANS >>
  qexists_tac `s.vs_alloca_next` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
