(* Joint execution and framing for materialized DALLOCA buffers. *)
Theory bodyFullDynamicBuffer
Ancestors
  bodySim bodyFullIfExpReach fragGasSeqPtr exprLoweringProps loweringStateRelDefs
  loweringPosts bodyMemoryDefs compileEnv bodyPtrDefs venomState venomMemDefs
  venomInst venomExecSemantics ptrDiscipline ptrSafeRun unitTransformDefs memSafeRun
  memLocDefs codegenRel contextCodegenRel words list arithmetic finite_map pred_set
  stateRelProj[qualified] exprSimCopy[qualified] exprSimProps[qualified]
  bodyFullUnwrapSlotPost[qualified] bodyPtrBytestringBuiltinsWindowGhost[qualified]

(* DALLOCA reserves a region but does not write any of its bytes.  The
   memory-length part of fmp_room is recovered only once enough of the
   region has been materialised by writes (or was already in memory). *)
Theorem dalloca_origin_region_exact:
  MEM func ctx.ctx_functions /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\ eval_operand size_op s = SOME sz /\
  w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) < dimword (:256) /\
  op_taint tn size_op = {} /\ allocas_from lo s /\ allocas_below_fmp s ==>
  ?t Gh th.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gh,th)) /\
    lookup_var out t = SOME s.vs_fmp /\ op_taint th (Var out) = {} /\
    FLOOKUP Gh out = SOME (w2n s.vs_fmp,venomLayout$ceil32 (w2n sz)) /\
    ptr_covers Gh th out t (w2n sz) /\
    w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (w2n sz) /\
    t.vs_initial_fmp = s.vs_initial_fmp /\ allocas_below_fmp t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_returndata = s.vs_returndata /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_labels = s.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    th.t_mem = tn.t_mem UNION {j | w2n s.vs_fmp <= j /\ j < w2n t.vs_fmp} /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
          FLOOKUP Gh x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    (fmp_room ctx func s ==>
     (fmp_room ctx func t <=>
      w2n t.vs_fmp <= MAX (w2n s.vs_initial_fmp) (LENGTH s.vs_memory + 31))) /\
    t = (update_var out s.vs_fmp
          (s with vs_fmp := s.vs_fmp + n2w (venomLayout$ceil32 (w2n sz)))
          with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `active_inst func inst s` by
    (drule_all contextCodegenRelPropsTheory.lookup_instruction_active >> simp[]) >>
  `contextRawReachable$frag_reachable ctx func s func inst s` by
    simp[contextRawReachableTheory.frag_reachable_start] >>
  `dalloca_no_wrap inst s` by simp[dalloca_no_wrap_def] >>
  qabbrev_tac `alloc_base = w2n s.vs_fmp` >>
  qabbrev_tac `alloc_len = venomLayout$ceil32 (w2n sz)` >>
  `alloc_base + alloc_len < dimword (:256)` by
    fs[Abbr `alloc_base`, Abbr `alloc_len`] >>
  qabbrev_tac `u = update_var out s.vs_fmp (s with vs_fmp := s.vs_fmp + n2w alloc_len)` >>
  `step_inst 0 ctx inst s = OK u` by
    simp[lowerDloadPtrDallocaTheory.dalloca_step_success, Abbr `u`, Abbr `alloc_len`] >>
  `step_inst_base inst s = OK u` by gvs[step_inst_non_invoke] >>
  `w2n u.vs_fmp = alloc_base + alloc_len` by
    (`w2n s.vs_fmp + alloc_len < dimword (:256)` by fs[Abbr `alloc_base`] >>
     drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     simp[Abbr `u`, Abbr `alloc_base`, update_var_def]) >>
  `step_prov PG G inst u = G |+ (out,(alloc_base,alloc_len))` by
    simp[step_prov_def, out_prov_def, Abbr `u`, lookup_var_def, update_var_def,
         set_prov_def, finite_mapTheory.FLOOKUP_UPDATE, GSYM (markerTheory.Abbrev_def)] >>
  `step_taint inst s u tn =
     tn with <|t_mem := tn.t_mem UNION {j | alloc_base <= j /\ j < alloc_base + alloc_len};
               t_var := tn.t_var |+ (out,{})|>` by
    (simp[step_taint_def, out_taint_def, mem_taint_def, adopt_reset_def,
          store_taint_def, imm_taint_def, new_site_bytes_def, step_writes_def,
          range_bytes_def, source_memory_write_ranges_def, written_taint_def,
          taint_component_equality, set_var_taint_def, pred_setTheory.EXTENSION] >>
     simp[Abbr `u`, update_var_def, Abbr `alloc_base`, finite_mapTheory.FLOOKUP_DEF,
          SF CONJ_ss]) >>
  qexistsl [`u with vs_inst_idx := SUC s.vs_inst_idx`, `step_prov PG G inst u`,
            `step_taint inst s u tn`] >>
  conj_tac
  >- (rpt gen_tac >>
      `ptr_inst_ok D lo 0 ctx func G tn inst s` by
        simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `u`, update_var_def,
             source_memory_read_ranges_def, source_memory_write_ranges_def] >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
          step_prov PG G inst u,step_taint inst s u tn)` by
        (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
         simp[is_terminator_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
              source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
      drule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
      irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      simp[Abbr `u`, update_var_def]) >>
  `w2n sz <= alloc_len` by simp[Abbr `alloc_len`, venomLayoutTheory.ceil32_ge] >>
  `MEM inst (fn_insts func)` by
    (drule_all contextRawReachableTheory.frag_reachable_members >> simp[]) >>
  `ctx_has_dalloca ctx` by
    (simp[ctx_has_dalloca_def, EXISTS_MEM] >> qexists `func` >>
     simp[] >> qexists `inst` >> simp[]) >>
  fs[Abbr `u`, update_var_def, Abbr `alloc_base`, allocas_below_fmp_def] >>
  simp[ptr_covers_def, lookup_var_def, op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_room_def, pending_alloca_size_def, SF CONJ_ss] >>
  first_assum ACCEPT_TAC
QED
Theorem dynamic_buffer_materialized_frame:
  ctx_has_dalloca ctx /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
  B = w2n s.vs_fmp /\ w2n t.vs_fmp = B + venomLayout$ceil32 N /\
  B+N <= LENGTH t.vs_memory /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
  (!b k. b+k <= B ==> mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
  (!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem) ==>
  stmt_state_rel H ctx func cenv cx ee t /\ ghost_inv_at D lo d cenv cx ee Gmat tt t /\
  wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
  return_buf_frame d cenv sm t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
               vs_memory := t.vs_memory; vs_fmp := t.vs_fmp|>` by
    (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = _`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                                     vs_memory := t.vs_memory; vs_fmp := t.vs_fmp|>``) >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|>`
      (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  `s.vs_alloca_next <= B /\ fmp_room ctx func t` by
    (drule stateRelProjTheory.stmt_state_rel_fmp_room >>
     `venomLayout$ceil32 N <= N+31` by
       (rw[venomLayoutTheory.ceil32_def] >> decide_tac) >>
     simp[exprLoweringPropsTheory.fmp_room_def,pending_alloca_size_def] >>
     rpt strip_tac >> fs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!b k. b+k <= s.vs_alloca_next ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!name b k. local_region cenv ee.scopes s name b k ==> b+k <= s.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  `!name b k. local_region cenv es.scopes s0 name b k ==> b+k <= s0.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  `!aid b k. FLOOKUP s0.vs_allocas aid = SOME (b,k) ==> b+k <= s0.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (strip_assume_tac o REWRITE_RULE
         [exprLoweringPropsTheory.stmt_state_rel_def,alloca_inv_def,alloca_next_valid_def]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "writeback" >>
  conj_tac >- suspend "kept" >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qpat_assum `return_buf_frame d cenv sm s` (irule_at Any) >> simp[] >> metis_tac[]
QED

Resume dynamic_buffer_materialized_frame[state]:
  `local_ptrs_rel func cenv ee.scopes s /\
   immutable_alloca_sep func cenv cx ee s /\ immutable_base_zero cenv s /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,state_rel_def] >>
  `!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p s` by metis_tac[local_ptrs_reserved_def] >>
  `local_ptrs_rel func cenv ee.scopes t` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists `s` >> simp[] >>
     rpt strip_tac >> gvs[] >>
     TRY (qpat_assum `!name entry p sz. _ ==> lookup_var p t = lookup_var p s`
           (drule_all_then ACCEPT_TAC)) >>
     sym_tac >>
     qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _` irule >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> _` drule >>
     decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee t` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists `s` >> simp[] >>
     conj_tac
     >- (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|>`
           (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!b k. b+k <= s.vs_alloca_next ==> _` irule >>
     qpat_assum `immutable_alloca_sep func cenv cx ee s`
       (strip_assume_tac o REWRITE_RULE[exprLoweringPropsTheory.immutable_alloca_sep_def]) >>
     first_x_assum (drule_all_then strip_assume_tac) >> simp[]) >>
  `immutable_alloca_sep func cenv cx ee t` by
    (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >> simp[] >>
     rpt strip_tac >> qexists `id` >>
     irule (iffLR exprSimCopyTheory.copy_buffer_local_region_frame) >> metis_tac[]) >>
  `immutable_base_zero cenv t` by
    (irule exprLoweringPropsTheory.immutable_base_zero_frame >> qexists `s` >> simp[] >>
     reverse conj_tac
     >- (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|>`
          (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base]) >>
  `state_rel H func cenv cx ee t` by
    (irule exprLoweringPropsTheory.state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ee`,`s`] >> fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     qpat_assum `t:venom_state = _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def,alloca_inv_def,allocas_non_overlapping_def,
     alloca_next_valid_def,alloca_room_def,pending_alloca_size_def]
  >> (metis_tac[])
QED

Resume dynamic_buffer_materialized_frame[ghost]:
  `allocas_from lo t /\ lo <= t.vs_alloca_next /\ stor_taint_ok_at D tt t` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     fs[ghost_inv_at_def,allocas_from_def,stor_taint_ok_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ghost_inv_at D lo d cenv cx ee G tn s`
    (mp_then Any irule bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport) >>
  qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
  `lo <= B` by (fs[ghost_inv_at_def] >> decide_tac) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,state_rel_def] >>
  simp[] >> qexists `func` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> _`
    (drule_then assume_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!i. i < B /\ i IN tt.t_mem ==> _` irule >> simp[] >> decide_tac
QED

Resume dynamic_buffer_materialized_frame[writeback]:
  qpat_assum `wb_frame cenv es ee sa s0 s`
    (strip_assume_tac o REWRITE_RULE[loweringPostsTheory.wb_frame_def]) >>
  simp[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz s.vs_memory = _`
        (drule_all_then (SUBST1_TAC o SYM)) >>
      qpat_assum `!b k. b+k <= s.vs_alloca_next ==> _` irule >>
      qpat_assum `!aid b k. FLOOKUP s0.vs_allocas aid = SOME (b,k) ==> _` drule >>
      decide_tac) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >> qexists `s` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!b k. b+k <= s.vs_alloca_next ==> _` irule >>
  qpat_assum `!name b k. local_region cenv es.scopes s0 name b k ==> _` drule >>
  decide_tac
QED

Resume dynamic_buffer_materialized_frame[kept]:
  irule bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` (irule_at Any) >>
  `lo <= B` by (fs[ghost_inv_at_def] >> decide_tac) >>
  simp[] >> rpt conj_tac >> rpt strip_tac >>
  qpat_assum `!i. i < B /\ i IN tt.t_mem ==> _` irule >> simp[] >>
  TRY (qpat_assum `!name b k. local_region cenv es.scopes s0 name b k ==> _` drule) >>
  TRY (qpat_assum `!aid b k. FLOOKUP s0.vs_allocas aid = SOME (b,k) ==> _` drule) >>
  decide_tac
QED

Finalise dynamic_buffer_materialized_frame
