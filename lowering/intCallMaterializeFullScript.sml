(* Materialization binds the captured arguments in the real callee scope. *)
Theory intCallMaterializeFull
Ancestors
  intCallEntryFull bodyPtrDefs loweringStateRelDefs vyperState venomState
  finite_map allocationPtr wordLoadStorePtr ptrSafetyTransport
  fragExecPtr ptrSafeRun ptrDiscipline venomExecSemantics venomInst
  contextCodegenRel codegenRel unitTransformDefs memSafeRun
  fragGasSeqPtr ghostPcTransportPtr instIdxIndep loweringHalt
  bodyFullUnwrapRun fragExecMem exprLoweringProps
  bodyPtrMakeArrayCopyStep bodyPtrMakeArrayWordStore bodyFullAllocaFresh localPtrsProps
  intCallCallee instSeqComposePtr bodyPtrStructLitMonotoneRepresentation memoryValueEncoding

Theorem materialize_param_ghost_bind:
  ghost_inv_at D lo d cenv cx es G tn s /\ es.scopes = [env] /\
  FLOOKUP env name = SOME entry /\ ptr_covers G tn p s sz /\
  (!w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv_at D lo d
    (cenv with ce_vars updated_by (\m. m |+ (name,PtrVar (Var p) sz)))
    cx es G tn s
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  pure_rewrite_tac [ghost_inv_at_def] >> conj_tac
  >- (map_every qx_gen_tac [`nm`, `ent`, `q`, `span`] >> strip_tac >>
      Cases_on `nm = name`
      >- (gvs[lookup_scopes_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
      `FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var q) span)` by
        fs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!name entry p sz. lookup_scopes _ _ = SOME _ /\ _ ==> _`
        (qspecl_then [`nm`, `ent`, `q`, `span`] mp_tac) >> simp[]) >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME buf) _ _ _ _` >>
  PairCases_on `buf` >> gvs[return_buf_ptr_def]
QED

Theorem materialize_stack_seq_ptr:
  !s u t id region_size dst src PG G tn lo ctx func.
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\ dst <> src /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u /\
    step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] []) u = OK t /\
    op_taint tn (Var src) = {} /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
    !D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []] s
      (step_prov PG
        (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
        (mk_inst (id+1) MSTORE [Var dst; Var src] []) t)
      (step_taint (mk_inst (id+1) MSTORE [Var dst; Var src] []) u t
        (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `region_size < dimword (:256)` by decide_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[ptr_inst_ok_alloca]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `ptr_covers
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
     (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn)
     dst u region_size` by metis_tac[fresh_alloca_ptr_covers] >>
  `ptr_covers
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
     (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn)
     dst u 32` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo u` by
    (drule_all step_alloca_fresh >> strip_tac >> gvs[] >>
     gvs[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `id = aid` >> gvs[] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
     (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn)
     (mk_inst (id+1) MSTORE [Var dst; Var src] [])
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_lower_bound_transport >> conj_tac
     >- (fs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >>
     fs[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] [])
     (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (mp_tac (Q.SPECL [`mk_inst (id+1) MSTORE [Var dst; Var src] []`,
       `u`, `SUC s.vs_inst_idx`] step_inst_inst_idx_indep) >>
     impl_tac >- simp[mk_inst_def, is_terminator_def] >>
     simp[exec_result_map_def]) >>
  simp[inst_seq_ptr_def]
QED

Theorem materialize_stack_seq_ptr_cursors:
  !s u t id region_size dst src PG G tn lo ctx func.
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\ dst <> src /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u /\
    step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] []) u = OK t /\
    op_taint tn (Var src) = {} /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
    !D k. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []]
      (s with vs_inst_idx := k)
      (step_prov PG
        (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
        (mk_inst (id+1) MSTORE [Var dst; Var src] []) t)
      (step_taint (mk_inst (id+1) MSTORE [Var dst; Var src] []) u t
        (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst])
     (s with vs_inst_idx := k) = OK (u with vs_inst_idx := k)` by
    (mp_tac (Q.SPECL [`mk_inst id ALLOCA [Lit (n2w region_size)] [dst]`,
       `s`, `k`] step_inst_inst_idx_indep) >>
     simp[mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] [])
     (u with vs_inst_idx := k) = OK (t with vs_inst_idx := k)` by
    (mp_tac (Q.SPECL [`mk_inst (id+1) MSTORE [Var dst; Var src] []`,
       `u`, `k`] step_inst_inst_idx_indep) >>
     simp[mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  mp_tac (Q.SPECL [`s with vs_inst_idx := k`, `u with vs_inst_idx := k`,
    `t with vs_inst_idx := k`, `id`, `region_size`, `dst`, `src`, `PG`,
    `G`, `tn`, `lo`, `ctx`, `func`] materialize_stack_seq_ptr) >>
  fs[allocas_from_def, step_prov_inst_idx, step_taint_inst_idx] >> metis_tac[]
QED

Theorem materialize_stack_seq_mem:
  !s u t id region_size dst src.
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\ dst <> src /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u /\
    step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] []) u = OK t ==>
    run_inst_seq_mem_ok
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []] s
Proof
  rpt gen_tac >> strip_tac >>
  `region_size < dimword (:256) /\ s.vs_alloca_next < dimword (:256)`
       by decide_tac >>
     simp[run_inst_seq_mem_ok_def] >>
     simp[inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, fixed_source_write_range_def,
          mk_inst_def, eval_operand_def] >>
     mp_tac (Q.SPECL [`id`, `region_size`, `dst`, `s`] step_alloca_fresh) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `FLOOKUP s.vs_vars src` >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          wordsTheory.w2n_n2w] >> decide_tac
QED

Theorem materialize_stack_origin_ptr:
  !sa sb s u t id region_size dst src PG G tn lo ctx func explicit.
    fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []] /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\ dst <> src /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u /\
    step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var src] []) u = OK t /\
    op_taint tn (Var src) = {} /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),
       step_prov PG
         (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
         (mk_inst (id+1) MSTORE [Var dst; Var src] []) t,
       step_taint (mk_inst (id+1) MSTORE [Var dst; Var src] []) u t
         (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  drule_all materialize_stack_seq_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `func`, `D`] assume_tac) >>
  `run_inst_seq
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []] s = OK t` by
    simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok
      [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
       mk_inst (id+1) MSTORE [Var dst; Var src] []] s` by
    (mp_tac (Q.SPECL [`s`, `u`, `t`, `id`, `region_size`, `dst`, `src`]
       materialize_stack_seq_mem) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
     ~is_terminator i.inst_opcode)
     [mk_inst id ALLOCA [Lit (n2w region_size)] [dst];
      mk_inst (id+1) MSTORE [Var dst; Var src] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  metis_tac[emitted_origin_ptr_path]
QED

Theorem materialize_stack_word_bind:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ es.scopes = [env] /\
  FLOOKUP env name = SOME entry /\ ptr_covers G tn dst s sz /\
  lookup_var dst s = SOME a /\ lookup_var src s = SOME w /\
  op_taint tn (Var src) = {} /\ lo <= w2n a /\
  (!nm b span. local_region cenv es.scopes s nm b span ==>
     b + span <= w2n a \/ w2n a + 32 <= b) /\
  (!mem. mem_word_at (w2n a) mem = w ==>
     val_in_memory entry.type entry.value (w2n a) mem) ==>
  ghost_inv_at D lo d
    (cenv with ce_vars updated_by (\m. m |+ (name,PtrVar (Var dst) sz)))
    cx es
    (step_prov PG G (mk_inst id MSTORE [Var dst; Var src] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; Var src] []) s
      (mstore (w2n a) w s) tn)
    (mstore (w2n a) w s)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME w` by simp[eval_operand_def] >>
  mp_tac (Q.INST [`dst` |-> `dst`, `value` |-> `Var src`, `s` |-> `s`,
    `a` |-> `a`, `w` |-> `w`, `PG` |-> `PG`, `G` |-> `G`,
    `id` |-> `id`, `tn` |-> `tn`] mstore_raw_ghost_frame) >>
  simp[] >> strip_tac >>
  `ghost_inv_at D lo d cenv cx es G
     (step_taint (mk_inst id MSTORE [Var dst; Var src] []) s
       (mstore (w2n a) w s) tn) (mstore (w2n a) w s)` by
    (irule ghost_inv_at_mstore_clean >> simp[] >> metis_tac[]) >>
  `ptr_covers G
     (step_taint (mk_inst id MSTORE [Var dst; Var src] []) s
       (mstore (w2n a) w s) tn) dst (mstore (w2n a) w s) sz` by
    (gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  irule (Q.INST [`env` |-> `env`, `entry` |-> `entry`]
    materialize_param_ghost_bind) >> simp[] >>
  qx_gen_tac `mem` >> strip_tac >>
  qpat_x_assum `!mem. mem_word_at _ mem = _ ==> _` irule >>
  mp_tac (Q.INST [`dst` |-> `dst`, `value` |-> `Var src`, `s` |-> `s`,
    `a` |-> `a`, `w` |-> `w`, `id` |-> `id`, `tn` |-> `tn`,
    `tnf` |-> `step_taint (mk_inst id MSTORE [Var dst; Var src] []) s
      (mstore (w2n (a:bytes32)) w s) tn`, `m` |-> `mem`]
    mstore_raw_robust_word) >> simp[]
QED

Theorem materialize_stack_alloc_ghost_vars:
  !D lo d func cenv cx es sa s u id region_size dst PG G tn.
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at sa p) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    (!x span. cenv.ce_return_buf = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    (!x span. cenv.ce_return_pc = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    dst = STRING #"%" (toString sa.cs_next_var) /\
    FLOOKUP s.vs_allocas id = NONE /\ region_size < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x. not_fresh_at sa x ==> x <> dst` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  mp_tac (Q.SPECL [`id`, `region_size`, `dst`, `s`] step_alloca_fresh) >>
  simp[] >> strip_tac >> gvs[] >>
  irule (Q.INST [`s` |-> `s`, `G` |-> `G`, `tn` |-> `tn`, `sa` |-> `sa`,
    `e` |-> `s.vs_alloca_next + region_size`] alloc_buffer_ghost_inv_at_vars) >>
  simp[update_var_def, venom_state_component_equality, lookup_var_def,
       FLOOKUP_UPDATE, op_taint_def] >> conj_tac
  >- (fs[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `id = aid` >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`G`, `func`, `region_size`, `s`, `sa`, `tn`] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem materialize_stack_alloc_ghost:
  !D lo d func cenv cx es sa s u id region_size dst PG G tn.
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    (!x span. cenv.ce_return_buf = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    (!x span. cenv.ce_return_pc = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    dst = STRING #"%" (toString sa.cs_next_var) /\
    FLOOKUP s.vs_allocas id = NONE /\ region_size < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn) u
Proof
  rpt gen_tac >> strip_tac >> irule materialize_stack_alloc_ghost_vars >>
  simp[] >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem materialize_stack_bind_ghost_vars:
  !D lo d func cenv cx es env entry name sa s u id region_size dst src w PG G tn.
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\ es.scopes = [env] /\
    FLOOKUP env name = SOME entry /\ fresh_vars_wrt sa s /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at sa p) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    (!x span. cenv.ce_return_buf = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    (!x span. cenv.ce_return_pc = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    dst = STRING #"%" (toString sa.cs_next_var) /\ not_fresh_at sa src /\
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\
    lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
    (!b mem. mem_word_at b mem = w ==>
       val_in_memory entry.type entry.value b mem) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u ==>
    ghost_inv_at D lo d
      (cenv with ce_vars updated_by (\m. m |+ (name,PtrVar (Var dst) region_size)))
      cx es
      (step_prov PG
        (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
        (mk_inst (id+1) MSTORE [Var dst; Var src] [])
        (mstore s.vs_alloca_next w u))
      (step_taint (mk_inst (id+1) MSTORE [Var dst; Var src] []) u
        (mstore s.vs_alloca_next w u)
        (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn))
      (mstore s.vs_alloca_next w u)
Proof
  rpt gen_tac >> strip_tac >>
  `region_size < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `dst <> src` by (gvs[not_fresh_at_def] >> metis_tac[]) >>
  `not_scope_ptr cenv es.scopes dst` by
    (gvs[] >> irule local_ptrs_rel_fresh_not_scope_ptr >>
     qexistsl_tac [`func`, `s`, `sa`] >> simp[]) >>
  `exec_alloca (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s
     (n2w region_size : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
     PURE_ONCE_REWRITE_TAC [step_inst_base_def] >> simp[mk_inst_def] >> metis_tac[]) >>
  drule_at (Pos hd) local_ptrs_rel_exec_alloca_fresh >>
  disch_then (qspecl_then [`func`, `cenv`, `es.scopes`, `dst`] mp_tac) >>
  simp[mk_inst_def, wordsTheory.w2n_n2w] >> strip_tac >>
  rename1 `w2n dest_word = s.vs_alloca_next` >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `ptr_covers
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
     (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn)
     dst u region_size` by metis_tac[fresh_alloca_ptr_covers] >>
  `ghost_inv_at D lo d cenv cx es
     (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
     (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn) u` by
    (irule materialize_stack_alloc_ghost_vars >> simp[] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`id`, `region_size`, `dst`, `s`] step_alloca_fresh) >>
  simp[] >> strip_tac >>
  `lookup_var src u = SOME w /\
   op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn)
     (Var src) = {}` by
    gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  `dest_word = n2w s.vs_alloca_next` by
    gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_assum `w2n dest_word = s.vs_alloca_next`
    (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  irule (SIMP_RULE std_ss [mk_inst_def] materialize_stack_word_bind) >>
  gvs[mk_inst_def] >> conj_tac
  >- (map_every qx_gen_tac [`nm`, `b`, `span`] >> strip_tac >>
      qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
        (qspecl_then [`nm`, `b`, `span`] mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac) >>
  qexists_tac `func` >> simp[]
QED

Theorem materialize_stack_bind_ghost:
  !D lo d func cenv cx es env entry name sa s u id region_size dst src w PG G tn.
    ghost_inv_at D lo d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\ es.scopes = [env] /\
    FLOOKUP env name = SOME entry /\ fresh_vars_wrt sa s /\
    local_ptrs_reserved cenv sa /\
    (!x span. cenv.ce_return_buf = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    (!x span. cenv.ce_return_pc = SOME (PtrVar (Var x) span) ==>
       not_fresh_at sa x) /\
    dst = STRING #"%" (toString sa.cs_next_var) /\ not_fresh_at sa src /\
    FLOOKUP s.vs_allocas id = NONE /\ 32 <= region_size /\
    s.vs_alloca_next + region_size < dimword (:256) /\
    lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
    (!b mem. mem_word_at b mem = w ==>
       val_in_memory entry.type entry.value b mem) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s = OK u ==>
    ghost_inv_at D lo d
      (cenv with ce_vars updated_by (\m. m |+ (name,PtrVar (Var dst) region_size)))
      cx es
      (step_prov PG
        (step_prov PG G (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) u)
        (mk_inst (id+1) MSTORE [Var dst; Var src] [])
        (mstore s.vs_alloca_next w u))
      (step_taint (mk_inst (id+1) MSTORE [Var dst; Var src] []) u
        (mstore s.vs_alloca_next w u)
        (step_taint (mk_inst id ALLOCA [Lit (n2w region_size)] [dst]) s u tn))
      (mstore s.vs_alloca_next w u)
Proof
  rpt gen_tac >> strip_tac >> irule materialize_stack_bind_ghost_vars >>
  simp[] >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem materialize_params_full:
  !caps cenv st cenv' st' func env s f0 mr ctx lo d cx es PG G tn Ds explicit.
    materialize_internal_params cenv caps st = (cenv',st') /\
    fn_has_code st st' func /\
    (!i. MEM i (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) ==>
         MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func /\ ALL_DISTINCT (MAP FST caps) /\
    mat_pending cenv env st s f0 mr caps /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) /\
    mat_inv func cenv env st s f0 mr /\
    s.vs_alloca_next + internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)
      < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ lo <= f0 /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ es.scopes = [env] /\
    (!nm entry. FLOOKUP env nm = SOME entry ==>
       value_has_type entry.type entry.value) /\
    (!nm p sz. FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at st p) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at st x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at st x) /\
    (!D. D IN Ds ==> ghost_inv_at D lo d cenv cx es G tn s) /\
    EVERY (\c. op_taint tn (SND (SND c)) = {} /\
      (!p off sz entry.
         ~FST (SND c) /\ SND (SND c) = Var p /\
         FLOOKUP cenv.ce_vars (FST c) = SOME (MemLoc off sz) /\
         FLOOKUP env (FST c) = SOME entry ==>
         ptr_covers G tn p s sz /\
         !w mem. lookup_var p s = SOME w /\
           mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n w) mem)) caps ==>
    ?t G' tn'.
      run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s = OK t /\
      mat_inv func cenv' env st' t f0 mr /\ mat_frame st s t /\
      t.vs_alloca_next = s.vs_alloca_next +
        internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps) /\
      (!D. D IN Ds ==> ghost_inv_at D lo d cenv' cx es G' tn' t) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts),G',tn'))

Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \ce cs todo us.
    ?code J qt.
      cs.cs_current_bb = st.cs_current_bb /\
      cs.cs_current_insts = st.cs_current_insts ++ code /\
      run_inst_seq code s = OK us /\ run_inst_seq_mem_ok code s /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                 ~is_terminator i.inst_opcode) code /\
      (!D k. inst_seq_ptr D lo ctx func PG G tn code
        (s with vs_inst_idx := k) J qt) /\
      (!D. D IN Ds ==> ghost_inv_at D lo d ce cx es J qt us) /\
      (!nm p sz. FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
         not_fresh_at cs p) /\
      (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cs x) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
         not_fresh_at cs x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
         not_fresh_at cs x) /\
      EVERY (\c. op_taint qt (SND (SND c)) = {} /\
        (!p off sz entry.
           ~FST (SND c) /\ SND (SND c) = Var p /\
           FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
           FLOOKUP env (FST c) = SOME entry ==>
           ptr_covers J qt p us sz /\
           !w mem. lookup_var p us = SOME w /\
             mem_agree_outside qt.t_mem us.vs_memory mem ==>
             val_in_memory entry.type entry.value (w2n w) mem)) todo` >>
  `P cenv st caps s` by
    (simp[Abbr `P`] >> qexistsl_tac [`G`, `tn`] >>
     simp[run_inst_seq_def, run_inst_seq_mem_ok_def, inst_seq_ptr_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`caps`, `cenv`, `st`, `cenv'`, `st'`, `func`, `env`,
    `s`, `f0`, `mr`, `P`] materialize_run_invariant) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (first_assum ACCEPT_TAC) >> conj_tac
      >- suspend "memory"
      >> suspend "stack") >>
  strip_tac >>
  qpat_x_assum `P cenv' st' [] t` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  qexistsl_tac [`J`, `qt`] >> conj_tac
  >- (first_assum ACCEPT_TAC) >> gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn code s J qt` by
    (qpat_x_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`code`, `st`, `st'`, `s`, `t`, `G`, `tn`, `J`, `qt`]
    bodyFullUnwrapRunTheory.emitted_origin_ptr_path) >> simp[]
QED

Resume materialize_params_full[memory]:
  map_every qx_gen_tac [`ce`, `cs`, `us`, `nm`, `p`, `tail`, `off`, `sz`] >>
  strip_tac >>
  qpat_x_assum `P ce cs _ us` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  qpat_assum `mat_pending ce env cs us f0 mr ((nm,F,Var p)::tail)`
    (mp_tac o REWRITE_RULE [mat_pending_def, listTheory.EVERY_DEF]) >>
  simp[] >> strip_tac >>
  rename1 `FLOOKUP env nm = SOME borrowed_entry` >>
  qpat_assum `FLOOKUP env nm = SOME borrowed_entry`
    (fn lk => qpat_assum `!entry. FLOOKUP env nm = SOME entry ==> _`
      (fn th => strip_assume_tac (MP (Q.SPEC `borrowed_entry` th) lk))) >>
  qexistsl_tac [`J`, `qt`] >> conj_tac
  >- (first_assum ACCEPT_TAC) >> conj_tac
  >- (qx_gen_tac `bound` >> strip_tac >>
      mp_tac (Q.INST [`D` |-> `bound`, `cenv` |-> `ce`, `s` |-> `us`,
        `G` |-> `J`, `tn` |-> `qt`, `name` |-> `nm`, `sz` |-> `sz`,
        `p` |-> `p`, `entry` |-> `borrowed_entry`] materialize_param_ghost_bind) >>
      impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`key`, `q`, `span`] >> strip_tac >>
      Cases_on `key = nm` >> gvs[FLOOKUP_UPDATE] >>
      qpat_x_assum `!nm p sz. FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) sz) ==> _`
        (qspecl_then [`key`, `q`, `span`] mp_tac) >> simp[]) >>
  qpat_x_assum `EVERY (\c. op_taint qt (SND (SND c)) = {} /\ _) tail`
    (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
  simp[listTheory.EVERY_MEM] >> strip_tac >> qx_gen_tac `cap` >> strip_tac >>
  qpat_x_assum `!c. MEM c tail ==> op_taint qt (SND (SND c)) = {} /\ _`
    (qspec_then `cap` strip_assume_tac) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FST cap = nm` >> gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `!p off sz entry. _` drule_all >> simp[]
QED

Resume materialize_params_full[stack]:
  map_every qx_gen_tac [`ce`, `cs`, `us`, `mid`, `ut`, `nm`, `p`,
                       `tail`, `off`, `sz`] >>
  strip_tac >>
  qpat_x_assum `P ce cs _ us` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  qpat_assum `mat_pending ce env cs us f0 mr ((nm,T,Var p)::tail)`
    (mp_tac o REWRITE_RULE [mat_pending_def, listTheory.EVERY_DEF]) >>
  simp[] >> strip_tac >>
  qabbrev_tac `dst = STRING #"%" (toString cs.cs_next_var)` >>
  qabbrev_tac `alloc_inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]` >>
  qabbrev_tac `store_inst = mk_inst (cs.cs_next_id + 1) MSTORE [Var dst;Var p] []` >>
  `?u. step_inst_base alloc_inst us = OK u /\ step_inst_base store_inst u = OK ut` by
    (qpat_x_assum `run_inst_seq _ us = OK ut` mp_tac >>
     Cases_on `step_inst_base
       (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)]
         [STRING #"%" (toString cs.cs_next_var)]) us` >>
     gvs[Abbr `alloc_inst`, Abbr `store_inst`, Abbr `dst`, run_inst_seq_def] >>
     BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
  qpat_assum `mat_inv func ce env cs us f0 mr`
    (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
  `FLOOKUP us.vs_allocas cs.cs_next_id = NONE` by
    (simp[FLOOKUP_DEF] >> strip_tac >>
     qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> simp[]) >>
  `sz < dimword (:256) /\ us.vs_alloca_next < dimword (:256)` by decide_tac >>
  `dst <> p` by
    (gvs[Abbr `dst`, not_fresh_at_def] >> metis_tac[]) >>
  `allocas_from lo us /\ lo <= us.vs_alloca_next` by
    (simp[allocas_from_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  qunabbrev_tac `alloc_inst` >> qunabbrev_tac `store_inst` >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `sz`, `dst`, `us`] step_alloca_fresh) >>
  simp[] >> strip_tac >>
  `ut = mstore us.vs_alloca_next a u` by
    (qpat_x_assum `step_inst_base (mk_inst _ MSTORE _ _) u = OK ut` mp_tac >>
     PURE_ONCE_REWRITE_TAC [step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          wordsTheory.w2n_n2w] >> fs[lookup_var_def]) >>
  rename1 `FLOOKUP env nm = SOME stack_entry` >>
  `value_has_type stack_entry.type stack_entry.value` by
    (qpat_x_assum `!nm entry. FLOOKUP env nm = SOME entry ==> _`
       (qspecl_then [`nm`, `stack_entry`] mp_tac) >> simp[]) >>
  `!b mem. mem_word_at b mem = a ==>
     val_in_memory stack_entry.type stack_entry.value b mem` by
    (rpt strip_tac >> irule memory_value_rel_val_in_memory >>
     simp[] >> qpat_x_assum `!b m. mem_word_at b m = a ==> _` drule >> simp[]) >>
  qabbrev_tac `J2 = step_prov PG
      (step_prov PG J (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) u)
      (mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []) ut` >>
  qabbrev_tac `qt2 = step_taint
      (mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []) u ut
      (step_taint (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) us u qt)` >>
  qexistsl_tac [`J2`, `qt2`] >>
  suspend "stack_finish"
QED

Resume materialize_params_full[stack_finish]:
  conj_tac
  >- (mp_tac (Q.SPECL [`code`,
        `[mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst];
          mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []]`, `s`, `us`]
        run_inst_seq_append) >> simp[run_inst_seq_def]) >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[] >>
      mp_tac (Q.SPECL [`us`, `u`, `ut`, `cs.cs_next_id`, `sz`, `dst`, `p`]
        materialize_stack_seq_mem) >> simp[]) >>
  simp[is_terminator_def] >> conj_tac
  >- suspend "stack_pointer" >>
  conj_tac
  >- suspend "stack_ghost" >>
  suspend "stack_tail"
QED

Resume materialize_params_full[stack_pointer]:
  `!D k. inst_seq_ptr D lo ctx func PG J qt
    [mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst];
     mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []]
    (us with vs_inst_idx := k) J2 qt2` by
    (mp_tac (Q.SPECL [`us`, `u`, `ut`, `cs.cs_next_id`, `sz`, `dst`, `p`,
       `PG`, `J`, `qt`, `lo`, `ctx`, `func`] materialize_stack_seq_ptr_cursors) >>
     simp[Abbr `J2`, Abbr `qt2`]) >>
  gen_tac >> mp_tac (Q.INST [`xs` |-> `code`,
    `ys` |-> `[mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst];
               mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []]`,
    `s` |-> `s`, `t` |-> `us`, `G1` |-> `J`, `tn1` |-> `qt`,
    `G2` |-> `J2`, `tn2` |-> `qt2`, `fn` |-> `func`]
    inst_seq_ptr_uniform_append) >> simp[] >>
  impl_tac >- (fs[listTheory.EVERY_MEM] >> rpt strip_tac >> res_tac) >> simp[]
QED

Resume materialize_params_full[stack_ghost]:
  qx_gen_tac `bound` >> strip_tac >>
  mp_tac (Q.SPECL [`bound`, `lo`, `d`, `func`, `ce`, `cx`, `es`, `env`,
    `stack_entry`, `nm`, `cs`, `us`, `u`, `cs.cs_next_id`, `sz`, `dst`, `p`,
    `a`, `PG`, `J`, `qt`] materialize_stack_bind_ghost_vars) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[Abbr `J2`, Abbr `qt2`]
QED

Resume materialize_params_full[stack_tail]:
  `!q. not_fresh_at cs q ==> not_fresh_at mid q` by
    (rw[not_fresh_at_def] >>
     qpat_x_assum `!n. cs.cs_next_var <= n ==> _` irule >> decide_tac) >>
  `not_fresh_at mid dst` by
    (simp[not_fresh_at_def, Abbr `dst`, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> decide_tac) >>
  conj_tac
  >- (map_every qx_gen_tac [`key`, `q`, `span`] >> strip_tac >>
      Cases_on `key = nm` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  suspend "stack_pending"
QED

Resume materialize_params_full[stack_pending]:
  `J2 = J |+ (dst,(us.vs_alloca_next,sz)) /\
   qt2.t_var = qt.t_var |+ (dst,{}) /\
   (!i. i < us.vs_alloca_next ==> (i IN qt2.t_mem <=> i IN qt.t_mem))` by
    (drule_all fresh_alloca_ghost >>
     disch_then (qspecl_then [`PG`, `J`, `qt`] strip_assume_tac) >>
     `lookup_var dst u = SOME (n2w us.vs_alloca_next) /\
      eval_operand (Var p) u = SOME a` by
       gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, eval_operand_def] >>
     mp_tac (Q.INST [`dst` |-> `dst`, `value` |-> `Var p`, `s` |-> `u`,
       `a` |-> `n2w us.vs_alloca_next : bytes32`, `w` |-> `a`,
       `PG` |-> `PG`, `G` |-> `step_prov PG J
         (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) u`,
       `id` |-> `cs.cs_next_id+1`, `tn` |-> `step_taint
         (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) us u qt`]
       mstore_raw_ghost_frame) >>
     simp[wordsTheory.w2n_n2w] >> strip_tac >>
     simp[Abbr `J2`, Abbr `qt2`, op_taint_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF] >> decide_tac) >>
  suspend "stack_pending_values"
QED

Resume materialize_params_full[stack_pending_values]:
  RULE_ASSUM_TAC (BETA_RULE o PURE_REWRITE_RULE [listTheory.EVERY_MEM]) >>
  PURE_REWRITE_TAC [listTheory.EVERY_MEM] >> BETA_TAC >>
  qx_gen_tac `cap` >> strip_tac >>
  qpat_assum `MEM cap tail`
    (fn mem => qpat_assum `!c. MEM c tail ==> op_taint qt (SND (SND c)) = {} /\ _`
      (fn th => strip_assume_tac (MP (Q.SPEC `cap` th) mem))) >>
  qpat_assum `MEM cap tail`
    (fn mem => qpat_assum `!c. MEM c tail ==> ?p a off sz entry. _`
      (fn th => strip_assume_tac (MP (Q.SPEC `cap` th) mem))) >>
  rename1 `SND (SND cap) = Var q` >>
  `q <> dst` by (gvs[not_fresh_at_def, Abbr `dst`] >> metis_tac[]) >>
  `dst <> q` by metis_tac[] >>
  `lookup_var q ut = lookup_var q us` by
    (qpat_assum `mat_frame cs us ut`
       (mp_tac o REWRITE_RULE [mat_frame_def]) >> metis_tac[]) >>
  conj_tac >- fs[op_taint_def, FLOOKUP_UPDATE] >>
  map_every qx_gen_tac [`bp`, `boff`, `bsize`, `borrowed_entry`] >> strip_tac >>
  `bp = q` by fs[] >>
  qpat_assum `bp = q` SUBST_ALL_TAC >>
  `FLOOKUP ce.ce_vars (FST cap) = SOME (MemLoc boff bsize)` by
    (Cases_on `FST cap = nm` >> fs[FLOOKUP_UPDATE]) >>
  qpat_assum `!p off sz entry. ~FST (SND cap) /\ _ ==> _`
    (qspecl_then [`q`, `boff`, `bsize`, `borrowed_entry`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> conj_tac
  >- (fs[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE] >> metis_tac[]) >>
  map_every qx_gen_tac [`w`, `mem`] >> strip_tac >>
  `lookup_var q us = SOME w` by
    (Cases_on `dst = q` >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `val_wf borrowed_entry.type borrowed_entry.value /\
   type_memory_size borrowed_entry.type <= bsize /\
   w2n w + bsize <= f0` by (fs[] >> metis_tac[]) >>
  `val_footprint borrowed_entry.type borrowed_entry.value <= bsize` by
    metis_tac[exprSimPropsTheory.val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `mem_bytes_at (w2n w) bsize ut.vs_memory =
   mem_bytes_at (w2n w) bsize us.vs_memory` by
    (fs[mat_frame_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!i. i < bsize ==> (w2n w+i IN qt2.t_mem ==> w2n w+i IN qt.t_mem)` by
    (rpt strip_tac >> `w2n w+i < us.vs_alloca_next` by decide_tac >>
     qpat_x_assum `!i. i < us.vs_alloca_next ==> _`
       (qspec_then `w2n w+i` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`borrowed_entry.type`, `borrowed_entry.value`,
    `w2n (w:bytes32)`, `w2n (w:bytes32)`, `bsize`, `qt.t_mem`, `qt2.t_mem`,
    `us.vs_memory`, `ut.vs_memory`] robust_val_in_memory_copy_transport_mono) >>
  impl_tac
  >- (conj_tac >- (first_assum ACCEPT_TAC) >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qx_gen_tac `oldmem` >> strip_tac >>
      qpat_assum `!w mem. lookup_var q us = SOME w /\ _ ==> _`
        (qspecl_then [`w`, `oldmem`] mp_tac) >> simp[]) >>
  disch_then (qspec_then `mem` mp_tac) >> simp[]
QED

Finalise materialize_params_full
