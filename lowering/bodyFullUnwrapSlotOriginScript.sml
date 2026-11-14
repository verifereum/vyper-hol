(* Joint execution boundaries for the allocating slot-copy suffix. *)
Theory bodyFullUnwrapSlotOrigin
Ancestors
  exprPtrUnwrapAllocEntry exprPtrUnwrapLoopEntry exprPtrUnwrapEnsureShape
  bodyFullUnwrapRun fragGasCopyLoop fragGasOriginPtr fragGasSeqPtr
  exprPtrUnwrapAllocation exprPtrUnwrapAllocationFrame
  compileEnv context venomState venomInst words finite_map
  exprLoweringProps fragExecMem ptrSafeRun arithmetic
  emitHelper loweringStateRelDefs exprPtrUnwrapFrames ptrDiscipline
  exprPtrUnwrapSingleSegment rich_list venomExecSemantics exprPtrUnwrapEnsureSingle
  exprSimStorageCopy slotCopyExecution copyExecution
  fragGasSeqAbort allocaHistory bodyBinopFragMemory
  exprSimPtrTopLevelStorageCopy abiBufferAllocationCode fragExec


Theorem unwrap_ensure_slot_origin_loop:
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u cv ds.
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
    toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
    (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_loop_code >> strip_tac >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule_all unwrap_alloc_origin_path >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`, `D`]
    (qx_choosel_then [`out`, `u1`] strip_assume_tac)) >>
  `out = root` by fs[] >>
  qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u1 = u` by fs[] >>
  qpat_x_assum `u1 = u` SUBST_ALL_TAC >>
  `not_fresh_at sm root /\ (!x. src = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `!x. src = Var x ==> _` mp_tac >>
     qpat_x_assum `buf.buf_operand = Var root` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
        comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `allocas_from lo a` by
    (simp[Once (GSYM exprPtrUnwrapFramesTheory.copy_allocas_inst_idx)] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `aid = sa.cs_next_id` >> gvs[allocas_from_def] >> metis_tac[]) >>
  `w2n d + 32*n <= a.vs_alloca_next` by
    ( `alloca_next_valid s` by fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
      qpat_x_assum `a = _` SUBST1_TAC >>
      qpat_x_assum `u = _` SUBST1_TAC >>
      qpat_x_assum `d = _` SUBST1_TAC >>
      simp[update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_def,
        bufferAllocationExecutionTheory.buffer_allocation_base_def] >>
      Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
      >- (simp[] >> irule LESS_EQ_TRANS >> qexists `s.vs_alloca_next + 32*n` >> simp[MOD_LESS_EQ]) >>
      rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
      drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> strip_tac >>
      fs[venomMemDefsTheory.alloca_next_valid_def] >>
      first_x_assum drule >> simp[] >> decide_tac) >>
  `compile_word_copy_loop src (Var root) n loc LocMemory F sm = (lab,sb)` by
    fs[compile_slot_to_memory_def] >>
  `lookup_var root a = SOME (n2w (w2n d))` by simp[] >>
  drule_all storage_copy_loop_origin_ptr >>
  disch_then (qspecl_then [`explicit`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`, `cv`, `ds`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >> simp[]
QED

Theorem unwrap_single_slot_origin_execution:
  (load = SLOAD \/ load = TLOAD) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\
  emitted_insts sa sb =
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand src s = SOME key /\ op_taint tn src = {} /\ root <> out /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  allocas_from lo s /\ w2n addr + 32 <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s)
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
        {w2n addr+k | k IN key_taint
          (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all exprPtrUnwrapSingleSegmentTheory.copy_single_slot_segment >>
  disch_then (qspecl_then [`id`, `func`, `PG`, `D`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []]` by
    gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `run_inst_seq_mem_ok
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []] s` by
    (qpat_x_assum `load = SLOAD \/ load = TLOAD` strip_assume_tac >>
     simp[run_inst_seq_mem_ok_def, mk_inst_def,
      unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def,
      codegenRelTheory.fixed_source_write_range_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[lookup_var_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode)
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []]` by
    (qpat_x_assum `load = SLOAD \/ load = TLOAD` strip_assume_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  qexistsl [`Gf`, `tnf`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  asm_rewrite_tac[] >> simp[mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem unwrap_ensure_slot_origin_single:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32 <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
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
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
      (update_var (STRING #"%" (toString sm.cs_next_var))
        (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
          with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
      {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_single_code >> strip_tac >>
  `32*1 <= nb /\ 1 < 2**256` by simp[] >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule_all unwrap_alloc_origin_path >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`, `D`]
    (qx_choosel_then [`out`, `u1`] strip_assume_tac)) >>
  `out = root` by fs[] >> qpat_x_assum `out = root` SUBST_ALL_TAC >>
  `u1 = u` by fs[] >> qpat_x_assum `u1 = u` SUBST_ALL_TAC >>
  `allocas_from lo a` by
    (simp[Once (GSYM exprPtrUnwrapFramesTheory.copy_allocas_inst_idx)] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `aid = sa.cs_next_id` >> gvs[allocas_from_def] >> metis_tac[]) >>
  `w2n d + 32 <= a.vs_alloca_next` by
    (`alloca_next_valid s` by fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     qpat_x_assum `a = _` SUBST1_TAC >> qpat_x_assum `u = _` SUBST1_TAC >>
     qpat_x_assum `d = _` SUBST1_TAC >>
     simp[update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_def,
       bufferAllocationExecutionTheory.buffer_allocation_base_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (simp[] >> irule LESS_EQ_TRANS >> qexists `s.vs_alloca_next + 32` >> simp[MOD_LESS_EQ]) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
     drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> strip_tac >>
     fs[venomMemDefsTheory.alloca_next_valid_def] >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  drule_all ensure_slot_memory_split >> disch_then (strip_assume_tac o SRULE []) >>
  drule storage_copy_word_layout >> strip_tac >>
  `same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts` by gvs[] >>
  `root <> STRING #"%" (toString sm.cs_next_var)` by
    (qpat_x_assum `slot_copy_external sm (Var root)` mp_tac >>
     simp[slot_copy_external_def, slot_copy_var_def] >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_covers G0 tn0 root a 32` by fs[] >>
  `~a.vs_halted` by simp[update_var_def,
    bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
  Q.SUBGOAL_THEN
    `(if loc=LocStorage then SLOAD else TLOAD) = SLOAD \/
     (if loc=LocStorage then SLOAD else TLOAD) = TLOAD` assume_tac
  >- (Cases_on `loc=LocStorage` >> simp[]) >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id (if loc=LocStorage then SLOAD else TLOAD) [src]
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst (sm.cs_next_id+1) MSTORE
       [Var root; Var (STRING #"%" (toString sm.cs_next_var))] []]` by fs[] >>
  drule_all unwrap_single_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  Cases_on `loc=LocStorage` >> gvs[]
QED


Theorem unwrap_ensure_slot_origin_execution:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ fn_inst_ids_distinct func /\
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
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
    gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
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
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n=1`
  >- (qpat_x_assum `n=1` SUBST_ALL_TAC >>
      `32 <= nb` by fs[] >> drule_all unwrap_ensure_slot_origin_single >>
      disch_then (qspecl_then [`explicit`, `PG`, `G`, `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
      `alloca_history func a` by (drule_all unwrap_alloc_origin_history >> simp[]) >>
      `gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
        (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
          (mp_then Any mp_tac gas_origin_ptr_path_append) >>
         gvs[]) >>
      `alloca_history func t` by suspend "single_history" >>
      `s.vs_alloca_next <= t.vs_alloca_next` by suspend "single_frontier" >>
      qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
      asm_rewrite_tac[] >> simp[]) >>
  drule_all unwrap_ensure_slot_origin_loop >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`, `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `alloca_history func a` by (drule_all unwrap_alloc_origin_history >> simp[]) >>
  `gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
          (mp_then Any mp_tac gas_origin_ptr_path_append) >>
         gvs[]) >>
  `alloca_history func t` by suspend "loop_history" >>
  `s.vs_alloca_next <= t.vs_alloca_next` by suspend "loop_frontier" >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  asm_rewrite_tac[] >> qexistsl [`cv`, `ds`] >> gvs[]
QED

Resume unwrap_ensure_slot_origin_execution[single_history]:
  drule_all ensure_slot_memory_single_code >> strip_tac >>
  drule_all ensure_slot_memory_split >> disch_then (strip_assume_tac o SRULE []) >>
  drule storage_copy_word_layout >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `a.vs_current_bb = sm.cs_current_bb /\ a.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     gvs[same_blocks_def, update_var_def,
       bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
     simp[]) >>
  `?bb rest. lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
     DROP a.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
    (qpat_x_assum `fn_has_code sm sb func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     fs[IS_PREFIX_APPEND, emitted_insts_def] >>
     rename1 `lookup_block sb.cs_current_bb func.fn_blocks = SOME codebb` >>
     qexists_tac `codebb` >> gvs[same_blocks_def, DROP_APPEND, DROP_LENGTH_NIL, listTheory.DROP_LENGTH_TOO_LONG]) >>
  `t.vs_allocas = a.vs_allocas /\ t.vs_current_bb = a.vs_current_bb` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, mstore_def, write_memory_with_expansion_def, update_var_def]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sm sb)` by
    (Cases_on `loc=LocStorage` >> gvs[mk_inst_def]) >>
  drule_all alloca_history_no_alloca_slice >>
  `a.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (`isPREFIX sm.cs_current_insts sb.cs_current_insts` by metis_tac[pairTheory.PAIR_EQ] >>
     qpat_x_assum `a.vs_inst_idx = LENGTH sm.cs_current_insts` mp_tac >>
     qpat_x_assum `isPREFIX sm.cs_current_insts sb.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND] >> gvs[]) >>
  simp[]
QED
Resume unwrap_ensure_slot_origin_execution[single_frontier]:
  `t.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, mstore_def, write_memory_with_expansion_def, update_var_def]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `a = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `u = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms, update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]
QED
Resume unwrap_ensure_slot_origin_execution[loop_history]:
  `copy_static t = copy_static a` by
    (qpat_x_assum `toplevel_copy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[toplevel_copy_inv_def, storage_copy_inv_def, copy_prefix_def]) >>
  drule copy_static_fields >> strip_tac >>
  drule_all ensure_slot_memory_split >> disch_then (strip_assume_tac o SRULE []) >>
  qpat_x_assum `if n = 1 then _ else _` mp_tac >> simp[] >> strip_tac >>
  drule_all copyExecutionTheory.compile_slot_to_memory_boundary >> strip_tac >>
  irule alloca_history_jump >> conj_tac >- simp[] >>
  qexists_tac `a` >> simp[]
QED
Resume unwrap_ensure_slot_origin_execution[loop_frontier]:
  `copy_static t = copy_static a` by
    (qpat_x_assum `toplevel_copy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[toplevel_copy_inv_def, storage_copy_inv_def, copy_prefix_def]) >>
  drule copy_static_fields >> strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `a = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `u = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms, update_var_def, bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]
QED
Finalise unwrap_ensure_slot_origin_execution
