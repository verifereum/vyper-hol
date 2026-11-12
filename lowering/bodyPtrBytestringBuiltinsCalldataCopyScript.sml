Theory bodyPtrBytestringBuiltinsCalldataCopy
Ancestors
  fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState finite_map codegenRel memLocDefs contextCodegenRel
  robustCopyTransportPtr valueEncodingProps exprSimProps localPtrsProps compileEnv loweringStateRelDefs

Theorem ptr_inst_ok_calldatacopy_operand:
  !D ctx fn G tn s id dst src count n fuel.
    eval_operand count s = SOME n /\ op_taint tn count = {} /\
    op_taint tn src = {} /\ ptr_covers G tn dst s (w2n n) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id CALLDATACOPY [Var dst; src; count] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, sized_source_write_range_def,
       eval_operand_def, mem_write_ops_def] >>
  rpt conj_tac
  >- (Cases_on `eval_operand src s` >> simp[] >> rpt strip_tac >> gvs[])
  >- (metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, combinTheory.K_THM,
                   opcode_case_def] >>
  Cases_on `eval_operand src s` >>
  simp[eval_operand_def, write_memory_with_expansion_def]
QED

Theorem calldatacopy_step:
  !dst s d src a count n fuel ctx id.
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand count s = SOME n ==>
  step_inst fuel ctx (mk_inst id CALLDATACOPY [dst; src; count] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_call_ctx.cc_calldata ++
                     REPLICATE (w2n n) 0w)) s)
Proof
  rpt strip_tac >> simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def]
QED

Theorem calldatacopy_step_prov:
  !PG G id dst src count s'.
    step_prov PG G (mk_inst id CALLDATACOPY [dst; src; count] []) s' = G
Proof
  simp[step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem calldatacopy_step_taint:
  !dst src count s d a n id tn bytes.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand count s = SOME n ==>
    step_taint (mk_inst id CALLDATACOPY [dst; src; count] []) s
      (write_memory_with_expansion (w2n d) bytes s) tn =
    tn with t_mem := tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n n}
Proof
  rpt strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, imm_taint_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, write_memory_with_expansion_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[taint_component_equality]
QED

Theorem ghost_kept_mem_taint_decrease:
  !cenv es sa G0 tn0 s0 G tn m.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ m SUBSET tn.t_mem ==>
    ghost_kept cenv es sa G0 tn0 s0 G (tn with t_mem := m)
Proof
  simp[ghost_kept_def, op_taint_def] >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem calldatacopy_write_ptr_covers:
  !G tn p s sz off bytes m.
    ptr_covers G tn p (write_memory_with_expansion off bytes s)
      sz = ptr_covers G (tn with t_mem := m) p s sz
Proof
  simp[ptr_covers_def, op_taint_def, write_memory_with_expansion_def,
       lookup_var_def]
QED

Theorem write_memory_robust_exterior:
  !tn s off bytes tv v p.
    val_wf tv v /\
    (p + val_footprint tv v <= off \/ off + LENGTH bytes <= p) /\
    (!mem. mem_agree_outside tn s.vs_memory mem ==>
           val_in_memory tv v p mem) ==>
    !mem. mem_agree_outside
      (tn DIFF {i | off <= i /\ i < off + LENGTH bytes})
      (write_memory_with_expansion off bytes s).vs_memory mem ==>
      val_in_memory tv v p mem
Proof
  rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `tn`,
               `{i | off <= i /\ i < off + LENGTH bytes}`] >>
  simp[] >> rpt strip_tac >>
  irule write_memory_mem_bytes_at_disjoint >> decide_tac
QED

Theorem write_memory_ghost_inv:
  !d cenv cx es G tn s off bytes.
    ghost_inv d cenv cx es G tn s /\
    (!name entry p sz w.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME w ==>
       val_wf entry.type entry.value /\
       (w2n w + val_footprint entry.type entry.value <= off \/
        off + LENGTH bytes <= w2n w)) ==>
    ghost_inv d cenv cx es G
      (tn with t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + LENGTH bytes})
      (write_memory_with_expansion off bytes s)
Proof
  rpt gen_tac >> strip_tac >>
  fs[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_covers G tn p s sz` by metis_tac[] >>
      conj_tac
      >- gvs[calldatacopy_write_ptr_covers, ptr_covers_def, op_taint_def] >>
      rpt strip_tac >>
      `lookup_var p s = SOME w` by
        gvs[lookup_var_def, write_memory_with_expansion_def] >>
      irule write_memory_robust_exterior >>
      conj_tac >- metis_tac[] >>
      goal_assum (drule_at Any) >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, calldatacopy_write_ptr_covers,
          ptr_covers_def, op_taint_def, write_memory_with_expansion_def,
          lookup_var_def])
  >- gvs[op_taint_def] >>
  gvs[stor_taint_ok_def, write_memory_with_expansion_def]
QED

Theorem calldatacopy_ghost_step:
  !dst src count s d a n id fuel ctx PG G tn.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand count s = SOME n ==>
    ghost_step fuel ctx PG G tn
      (mk_inst id CALLDATACOPY [dst; src; count] []) s =
    (G, tn with t_mem :=
      tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n n})
Proof
  rpt strip_tac >>
  simp[Once ghost_step_def, calldatacopy_step, calldatacopy_step_prov,
       calldatacopy_step_taint, mk_inst_def] >>
  simp[GSYM mk_inst_def] >>
  `step_inst fuel ctx (mk_inst id CALLDATACOPY [dst; src; count'] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_call_ctx.cc_calldata ++
        REPLICATE (w2n n) 0w)) s)` by
    (irule calldatacopy_step >> simp[]) >>
  simp[] >> irule calldatacopy_step_taint >> metis_tac[]
QED

Theorem calldatacopy_ghost_kept:
  !dst src count s d a n id fuel ctx PG G tn cenv es sa G0 tn0 s0.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand count s = SOME n /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept cenv es sa G0 tn0 s0
      (FST (ghost_step fuel ctx PG G tn
        (mk_inst id CALLDATACOPY [dst; src; count] []) s))
      (SND (ghost_step fuel ctx PG G tn
        (mk_inst id CALLDATACOPY [dst; src; count] []) s))
Proof
  rpt strip_tac >>
  `ghost_step fuel ctx PG G tn
     (mk_inst id CALLDATACOPY [dst; src; count'] []) s =
   (G, tn with t_mem := tn.t_mem DIFF
     {i | w2n d <= i /\ i < w2n d + w2n n})` by
    (irule calldatacopy_ghost_step >> metis_tac[]) >>
  simp[] >> irule ghost_kept_mem_taint_decrease >>
  simp[pred_setTheory.DIFF_SUBSET]
QED

Theorem write_memory_ghost_inv_local_regions:
  !d cenv cx es G tn s off bytes func.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
       regions_disjoint lo sz off (LENGTH bytes)) ==>
    ghost_inv d cenv cx es G
      (tn with t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + LENGTH bytes})
      (write_memory_with_expansion off bytes s)
Proof
  rpt strip_tac >> irule write_memory_ghost_inv >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n w) sz off (LENGTH bytes)` by metis_tac[] >>
  fs[local_ptrs_rel_def] >>
  qpat_x_assum `!name' entry' p' sz'. _` drule_all >> strip_tac >>
  gvs[] >> drule val_footprint_le >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem write_memory_ghost_inv_alloca:
  !d cenv cx es G tn s off bytes func inst q b asz.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\
    b <= off /\ off + LENGTH bytes <= b + asz ==>
    ghost_inv d cenv cx es G
      (tn with t_mem := tn.t_mem DIFF {i | off <= i /\ i < off + LENGTH bytes})
      (write_memory_with_expansion off bytes s)
Proof
  rpt strip_tac >> irule write_memory_ghost_inv_local_regions >>
  conj_tac
  >- (rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem calldatacopy_ghost_inv_alloca:
  !rb cenv cx es G tn s d a n func inst q b asz.
    ghost_inv rb cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\
    b <= w2n d /\ w2n d + w2n n <= b + asz ==>
    ghost_inv rb cenv cx es G
      (tn with t_mem := tn.t_mem DIFF
        {i | w2n d <= i /\ i < w2n d + w2n n})
      (write_memory_with_expansion (w2n d)
        (TAKE (w2n n) (DROP (w2n a) s.vs_call_ctx.cc_calldata ++
                       REPLICATE (w2n n) 0w)) s)
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) bytes s` >>
  `LENGTH bytes = w2n n` by simp[Abbr `bytes`, listTheory.LENGTH_TAKE] >>
  `w2n n = LENGTH bytes` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  irule write_memory_ghost_inv_alloca >> metis_tac[]
QED
