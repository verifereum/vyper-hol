Theory bodyFullTargetMappingScratch
Ancestors
  bodyFullTargetMappingScratchTail bodyFullAllocaFresh
  bodyFullUnwrapRun bodyFullUnwrapSlotPost exprSimMapKey
  fragGasOriginPtr fragGasOriginPtrLoop exprLoweringProps emitHelperProps
  emitHelper context compileEnv pair fragExec
  bodyPtrDefs loweringStateRelDefs venomState venomInst
  finite_map words pred_set list rich_list ASCIInumbers freshWrites
  ptrDiscipline fragGasCopyLoop venomExecSemantics loweringPosts venomMemDefs bodyMemoryDefs

Theorem mapping_scratch_runtime_restore:
  code = [mk_inst is MSTORE [Var p;bop] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  run_inst_seq code s = OK t ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `update_var h hash z` >>
  simp_tac (srw_ss()) [Abbr `z`, update_var_def, mstore_def, LET_THM]
QED

Theorem mapping_slot_full_run:
  compile_mapping_subscript bop key sa = (op,sb) /\
  (!x. bop = Var x \/ key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn bop = {} /\ op_taint tn key = {} /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel (H0 : (bool # 'a word # type_value) list # num list)
    ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H : (bool # 'a word # type_value) list # num list.
     P H ==> stmt_state_rel H ctx func cenv cx es s /\
                 ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    eval_operand op t = SOME (hashmap_slot w0 w1) /\
    op_taint tm op = {} /\ op_prov HG op = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK t,HG,tm) /\
       stmt_state_rel H ctx func cenv cx es t /\
       ghost_inv_at (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >> drule compile_mapping_subscript_parts >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (conj_tac >- metis_tac[ci_mono_compile_alloc_buffer, SND] >>
     `ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq /\ ci_mono sq sb` by
       metis_tac[ci_mono_emit_void, ci_mono_emit_op, SND] >>
     metis_tac[ci_mono_trans]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  suspend "tail"
QED

Resume mapping_slot_full_run[tail]:
  rename1 `lookup_var q t = SOME w` >>
  qabbrev_tac `qr = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `hr = STRING #"%" (toString (sm.cs_next_var+1))` >>
  qabbrev_tac `code =
    [mk_inst sm.cs_next_id MSTORE [Var q;bop] [];
     mk_inst (sm.cs_next_id+1) ADD [Var q;Lit 32w] [qr];
     mk_inst (sm.cs_next_id+2) MSTORE [Var qr;key] [];
     mk_inst (sm.cs_next_id+3) SHA3 [Var q;Lit 64w] [hr]]` >>
  `op = Var hr /\ sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ code` by
    (qpat_assum `emit_void MSTORE _ sm = _` mp_tac >>
     qpat_assum `emit_op ADD _ sn = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ sp = _` mp_tac >>
     qpat_assum `emit_op SHA3 _ sq = _` mp_tac >>
     simp_tac (srw_ss()) [emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[Abbr `qr`, Abbr `hr`, Abbr `code`, APPEND_ASSOC]) >>
  suspend "allocated"
QED
Resume mapping_slot_full_run[allocated]:
  `ALL_DISTINCT [q;qr;hr] /\
   (!x. not_fresh_at sm x ==> x <> qr /\ x <> hr)` by
    (gvs[ALL_DISTINCT, Abbr `qr`, Abbr `hr`, not_fresh_at_def, toString_inj] >>
     metis_tac[]) >>
  `(!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
   local_ptrs_reserved cenv sm` by
    metis_tac[ci_mono_def, not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s`
      (SUBST1_TAC o SYM) >> simp[]) >>
  `(!x. key = Var x ==> x <> qr) /\
   eval_operand bop t = SOME w0 /\ eval_operand key t = SOME w1 /\
   op_taint tn' bop = {} /\ op_taint tn' key = {}` by
    (conj_tac >- metis_tac[] >>
     Cases_on `bop` >> Cases_on `key` >>
     gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `lo <= t.vs_alloca_next /\ ~t.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> decide_tac) >>
  `?root cap. FLOOKUP G' q = SOME (root,cap) /\ root <= w2n w /\
     w2n w+64 <= root+cap /\ lo <= w2n w /\ op_taint tn' (Var q) = {}` by
    (fs[ptr_covers_def] >>
     `lo <= w2n w` by metis_tac[allocas_from_def] >> gvs[]) >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
     ghost_inv_at (DF H) lo d cenv cx es G' tn' t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (qpat_assum `!H'. stmt_state_rel H' _ _ _ _ _ s ==> _` irule >>
                   first_assum ACCEPT_TAC) >>
     irule alloc_buffer_ghost_inv_at >>
     conj_tac >- simp[] >>
     qexistsl_tac [`G`, `H`, `ctx`, `w2n w+64`, `func`, `s`, `sa`, `tn`] >>
     simp[]) >>
  suspend "apply_tail"
QED
Resume mapping_slot_full_run[apply_tail]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[exprSimAllocTheory.buffer_alloc_code] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[] >>
  `!name a n. local_region cenv es.scopes t name a n ==>
     a+n <= w2n w \/ w2n w+64 <= a` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region _ _ t _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `lookup_var q t = SOME (n2w (w2n w))` by simp[] >>
  `code = [mk_inst sm.cs_next_id MSTORE [Var q;bop] [];
     mk_inst (sm.cs_next_id+1) ADD [Var q;Lit 32w] [qr];
     mk_inst (sm.cs_next_id+2) MSTORE [Var qr;key] [];
     mk_inst (sm.cs_next_id+3) SHA3 [Var q;Lit 64w] [hr]]` by simp[Abbr `code`] >>
  ` (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]).inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]).inst_id = SOME (w2n w,64)` by simp[mk_inst_def] >>
  drule_all mapping_scratch_tail_full_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  rename1 `run_inst_seq code t = OK u` >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `HG`, `tm`] >>
  conj_tac >- (qpat_x_assum `eval_operand (Var hr) u = _` mp_tac >>
                simp[eval_operand_def, lookup_var_def]) >>
  suspend "frames"
QED
Resume mapping_slot_full_run[frames]:
  `u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> = t` by
    (irule mapping_scratch_runtime_restore >> metis_tac[]) >>
  `u.vs_current_bb = t.vs_current_bb /\
   u.vs_inst_idx = t.vs_inst_idx /\ u.vs_labels = t.vs_labels` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _|> = t`
      (SUBST1_TAC o SYM) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_asm1_tac >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s`
      (SUBST1_TAC o SYM) >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len <=>
       local_region cenv es.scopes t name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- suspend "wb" >>
  conj_tac >- suspend "pure" >>
  conj_tac >- suspend "kept" >>
  suspend "runtime"
QED
Resume mapping_slot_full_run[wb]:
  rewrite_tac[wb_frame_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `regions_disjoint (w2n w) 64 off sz` by metis_tac[] >>
    `off+sz <= w2n w \/ w2n w+64 <= off` by metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
    simp_tac (srw_ss()) [] >> metis_tac[]) >>
  irule exprSimPropsTheory.locals_kept_regions >>
  rpt strip_tac >>
  `regions_disjoint (w2n w) 64 b sz` by metis_tac[] >>
  `b+sz <= w2n w \/ w2n w+64 <= b` by metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED
Resume mapping_slot_full_run[pure]:
  rewrite_tac[pure_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) 64 b sz` by metis_tac[] >>
      `b+sz <= w2n w \/ w2n w+64 <= b` by metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
      simp_tac (srw_ss()) [] >> metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint off len (w2n w) 64` by
    (first_x_assum irule >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
       [STRING #"%" (toString sa.cs_next_var)]` >>
     conj_tac >- simp[mk_inst_def] >>
     conj_tac >- (simp_tac (srw_ss()) [] >> metis_tac[]) >>
     simp[]) >>
  `off+len <= w2n w \/ w2n w+64 <= off` by metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED
Resume mapping_slot_full_run[kept]:
  `!i. i IN tm.t_mem /\ i < s.vs_alloca_next ==> i IN tn.t_mem` by
    (qpat_assum `tm = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [IN_DIFF] >>
     qpat_assum `!i. i IN tn'.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> decide_tac) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      off+sz <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
      b+sz <= s.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  rewrite_tac[ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >>
    `i < s.vs_alloca_next` by (res_tac >> decide_tac) >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `i < s.vs_alloca_next` by (res_tac >> decide_tac) >> metis_tac[]) >>
  rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED
Resume mapping_slot_full_run[runtime]:
  conj_tac >- (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  conj_tac >- simp_tac (srw_ss()) [] >>
  conj_tac >-
    (`stmt_state_rel H0 ctx func cenv cx es t` by metis_tac[] >>
     `alloca_inv t` by metis_tac[stmt_state_rel_def] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) code` by
       simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
     irule emitted_alloca_history >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`code`, `t`, `sm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  conj_tac >- simp[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >>
  strip_tac >>
  conj_tac >-
    (irule gas_origin_ptr_path_trans >>
     metis_tac[]) >>
  metis_tac[]
QED
Finalise mapping_slot_full_run
