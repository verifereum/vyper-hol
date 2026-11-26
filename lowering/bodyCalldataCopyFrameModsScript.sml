(* Frame the existing output allocation across the dynamic calldata copy. *)
Theory bodyCalldataCopyFrameMods
Ancestors
  bodyFullDynamicBuffer bodyFullPathHistory
  bodyMethodIdScratchFrameMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyMemoryDefs bodyPtrDefs bodyInvSplit loweringSlice loweringPosts
  valueEncodingProps memoryReadProps venomMemProps venomState venomMemDefs stateRelProj
  loweringStateRelDefs stmtFragPtr ptrDiscipline exprLoweringProps
  bodyPtrBytestringBuiltinsExternalSlice contextCodegenRel
  words arithmetic finite_map pred_set list alist

Theorem copy_ghost_restore_mods[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  ghost_inv_at D 0 d ce cx es G' tn' t /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' t
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sm x` by metis_tac[local_ptrs_reserved_imm_base] >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. lo <> 0 /\ _ ==> _` (drule_all_then strip_assume_tac) >> simp[]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem copy_immutable_mods[local]:
  immutable_frame_mods func ce cx ee s /\ local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = (write_memory_with_expansion b bs s).vs_memory /\
  s.vs_alloca_next <= b ==>
  immutable_frame_mods func ce cx ee t
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >> qexists `s` >>
      simp[LENGTH_write_memory_with_expansion] >> disch_tac >> rpt gen_tac >> strip_tac >>
      irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >> disj1_tac >>
      qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ s`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
      qpat_assum `ce.ce_is_ctor ==> _`
        (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac o UNDISCH) >>
      simp[] >> strip_tac >> decide_tac) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_fields >>
  qexistsl [`s`,`ee`] >> simp[] >>
  map_every qx_gen_tac [`id`,`locb`,`sz`] >> disch_tac >> qexists `id` >>
  `local_region (ce with ce_module := src) ee.scopes t id locb sz <=>
   local_region (ce with ce_module := src) ee.scopes s id locb sz` by
    (irule local_region_lookup_cong >> simp[] >>
     rpt strip_tac >> `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  fs[]
QED

Theorem calldata_copy_finish_frame_mods:
  let ib = w2n s.vs_fmp; bs = cx.txn.calldata in
  ctx_has_dalloca ctx /\ allocas_below_fmp s /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee s /\
  immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  s.vs_call_ctx.cc_calldata = bs /\ LENGTH bs < dimword (:256) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
  fn_inst_ids_distinct func /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
  w2n t.vs_fmp = ib + venomLayout$ceil32 (LENGTH bs) /\
  t.vs_memory = (write_memory_with_expansion ib s.vs_call_ctx.cc_calldata s).vs_memory /\
  tn'.t_mem = (tn.t_mem UNION {i | ib <= i /\ i < w2n t.vs_fmp})
              DIFF {i | ib <= i /\ i < ib + LENGTH bs} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  eval_operand dp t = SOME s.vs_fmp /\ eval_operand len t = SOME (n2w (LENGTH bs)) /\
  op_taint tn' dp = {} /\ op_taint tn' len = {} /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G' tn' p t (LENGTH bs)) /\
  (!x. MEM (Var x) [addr;value;gas;ov;op] ==> not_fresh_at sm x) /\
  eval_operand addr s = SOME (w2w target) /\
  eval_operand value s = SOME (n2w amount) /\ eval_operand gas s = SOME gw /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;ov;op] /\
  eval_operand ov s = SOME (n2w ob) /\
  eval_operand op s = SOME (n2w (if cap = 0 then ob else ob + 32)) /\
  (cap = 0 ==> ov = op) /\
  sz = (if cap = 0 then 0 else 32 * ((cap + 31) DIV 32) + 32) /\
  ob + sz < dimword (:256) /\ FLOOKUP s.vs_allocas s6.cs_next_id = SOME (ob,sz) /\
  op_prov G ov = SOME (ob,sz) /\ op_prov G op = SOME (ob,sz) /\
  (!name lb n. local_region cenv ee.scopes s name lb n ==>
    regions_disjoint ob sz lb n) /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          inst.inst_id = s6.cs_next_id) ==>
  stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d cenv cx ee G' tn' t /\
  wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
  return_buf_frame d cenv sa t /\ alloca_history func t /\ allocas_below_fmp t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ lo <= t.vs_alloca_next /\ allocas_from lo t /\
  eval_operand addr t = SOME (w2w target) /\
  eval_operand value t = SOME (n2w amount) /\ eval_operand gas t = SOME gw /\
  eval_operand dp t = SOME (n2w ib) /\ eval_operand len t = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ctx_has_dalloca ctx /\
   w2n t.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t.vs_fmp) /\
  read_memory ib (LENGTH bs) t = bs /\
  (!i. ib <= i /\ i < ib + LENGTH bs ==> i NOTIN tn'.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G' tn' p t (LENGTH bs)) /\
  EVERY (\p. op_taint tn' p = {}) [addr;len;dp;gas;value;ov;op] /\
  eval_operand ov t = SOME (n2w ob) /\
  eval_operand op t = SOME (n2w (if cap = 0 then ob else ob + 32)) /\
  (cap = 0 ==> ov = op) /\ ob + sz < dimword (:256) /\
  FLOOKUP t.vs_allocas s6.cs_next_id = SOME (ob,sz) /\
  mem_bytes_at ob sz t.vs_memory = mem_bytes_at ob sz s.vs_memory /\
  op_prov G' ov = SOME (ob,sz) /\ op_prov G' op = SOME (ob,sz) /\
  (!name lb n. local_region cenv ee.scopes t name lb n ==>
    regions_disjoint ob sz lb n) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob sz)
Proof
  simp[LET_THM] >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_labels = s.vs_labels /\
   t.vs_data_section = s.vs_data_section` by
    (qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _; vs_fmp := _|> = s`
       (fn th => map_every (mp_tac o C AP_TERM th)
         [``venom_state_vs_allocas``,``venom_state_vs_alloca_next``,
          ``venom_state_vs_initial_fmp``,``venom_state_vs_labels``,``venom_state_vs_data_section``]) >>
     simp[]) >>
  `w2n s.vs_initial_fmp <= w2n s.vs_fmp` by fs[allocas_below_fmp_def] >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by
    (drule stateRelProjTheory.stmt_state_rel_fmp_room >>
     simp[fmp_room_def] >> decide_tac) >>
  `lo <= s.vs_alloca_next /\ allocas_from lo s` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >> simp[]) >>
  `t.vs_memory =
      (write_memory_with_expansion (w2n s.vs_fmp) cx.txn.calldata s).vs_memory` by simp[] >>
  `!b n. b+n <= w2n s.vs_fmp ==>
       mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> qpat_assum `t.vs_memory = _` (PURE_ONCE_REWRITE_TAC o single) >>
     irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >> simp[]) >>
  `!i. i < w2n s.vs_fmp /\ i IN tn'.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `tn'.t_mem = _` (fn th => fs[th]) >> decide_tac) >>
  suspend "frame"
QED

Resume calldata_copy_finish_frame_mods[frame]:
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`cenv`,`s`,`sa`] >> simp[]) >>
  `ghost_inv_at D 0 d cenv cx ee G tn s` by
    (irule method_id_ghost_at_zero >> qexists `lo` >> simp[]) >>
  `ghost_kept_at 0 cenv es sa G0 tn0 s0 G tn` by
    (qpat_assum `ghost_kept_at lo _ _ _ _ _ _ _ _` mp_tac >> pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ee t /\ ghost_inv_at D 0 d cenv cx ee G' tn' t /\
   wb_frame cenv es ee sa s0 t /\ ghost_kept_at 0 cenv es sa G0 tn0 s0 G' tn' /\
   return_buf_frame d cenv sm t` by
    (irule (Q.INST [`B` |-> `w2n s.vs_fmp`, `N` |-> `LENGTH cx.txn.calldata`]
              dynamic_buffer_materialized_frame) >>
     simp[] >> conj_tac >- (qexists `H0` >> simp[]) >>
     qexistsl [`G`,`s`,`tn`] >> simp[LENGTH_write_memory_with_expansion] >>
     conj_tac
     >- (rpt strip_tac >> irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >> simp[]) >>
     rpt strip_tac >> fs[] >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ G' tn'` mp_tac >> pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `ghost_inv_at_mods D lo d cenv cx ee G' tn' t` by
    (irule copy_ghost_restore_mods >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`s`,`sm`,`tn`] >>
     `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
       (qpat_assum `!b n. b+n <= w2n s.vs_fmp ==> _` irule >> decide_tac) >>
     `!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem` by
       (rpt strip_tac >> qpat_assum `!i. i < w2n s.vs_fmp /\ _ ==> _` irule >>
        conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `immutable_frame_mods func cenv cx ee t` by
    (irule copy_immutable_mods >> qexistsl [`w2n s.vs_fmp`,`cx.txn.calldata`,`s`,`sm`] >>
     simp[w2n_lt]) >>
  `return_buf_frame d cenv sa t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl [`cenv`,`s`,`sa`] >> simp[] >>
     rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> simp[]) >>
  `alloca_history func t` by
    (drule body_full_path_alloca_history >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     disch_then irule >> simp[]) >>
  `w2n s.vs_initial_fmp <= w2n t.vs_fmp` by decide_tac >>
  `allocas_below_fmp t /\ allocas_from lo t` by
    (fs[allocas_below_fmp_def, allocas_from_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume calldata_copy_finish_frame_mods[finish]:
  `!p. MEM p [addr;value;gas;ov;op] ==>
       eval_operand p t = eval_operand p s /\ op_prov G' p = op_prov G p /\
       op_taint tn' p = op_taint tn p` by
    (gen_tac >> strip_tac >> irule reserved_operand_ghost_frame >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists `sm` >> conj_tac
     >- (rpt strip_tac >> gvs[] >>
         qpat_assum `!x. Var x = addr \/ _ ==> _` (qspec_then `z` irule) >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `!name lb n. local_region cenv ee.scopes t name lb n ==>
       regions_disjoint ob sz lb n` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes t name lb n <=> local_region cenv ee.scopes s name lb n` by
       (irule local_region_lookup_cong >> rpt strip_tac >>
        `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
     `local_region cenv ee.scopes s name lb n` by fs[] >>
     qpat_assum `!name lb n. local_region _ _ s name lb n ==> _`
       (qspecl_then [`name`,`lb`,`n`] mp_tac) >> simp[]) >>
  `cenv.ce_is_ctor ==> !src tops name tv v off.
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
               | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) ob sz` by
    suspend "outbuf_sep" >>
  `read_memory (w2n s.vs_fmp) (LENGTH cx.txn.calldata) t = cx.txn.calldata` by
    simp[read_memory_eq_mem_bytes_at, valueEncodingPropsTheory.write_memory_mem_bytes_at_same] >>
  `!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + LENGTH cx.txn.calldata ==>
       i NOTIN tn'.t_mem` by
    (rpt strip_tac >> qpat_assum `tn'.t_mem = _` (fn th => fs[th])) >>
  `w2n s.vs_fmp + LENGTH cx.txn.calldata <= w2n t.vs_fmp` by
    simp[venomLayoutTheory.ceil32_ge] >>
  `mem_bytes_at ob sz t.vs_memory = mem_bytes_at ob sz s.vs_memory` by
    (qpat_assum `!b n. b+n <= w2n s.vs_fmp ==> _` irule >>
     qpat_assum `allocas_below_fmp s`
       (strip_assume_tac o REWRITE_RULE[allocas_below_fmp_def]) >>
     qpat_assum `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> _`
       (drule_then assume_tac) >> decide_tac) >>
  simp[w2n_lt] >>
  qpat_assum `sz = if cap = 0 then _ else _` (PURE_REWRITE_TAC o single o SYM) >>
  conj_tac
  >- (qpat_assum `t.vs_memory = (write_memory_with_expansion _ cx.txn.calldata s).vs_memory`
        (fn th => qpat_assum `mem_bytes_at ob sz t.vs_memory = _`
          (ACCEPT_TAC o PURE_REWRITE_RULE[th]))) >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume calldata_copy_finish_frame_mods[outbuf_sep]:
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `immutable_frame_mods func cenv cx ee t`
    (strip_assume_tac o REWRITE_RULE[immutable_frame_mods_def, immutable_alloca_sep_mods_def]) >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ t`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
  qpat_assum `cenv.ce_is_ctor ==> _`
    (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac o UNDISCH) >>
  simp[] >> strip_tac >>
  qpat_assum `!i b n. _ ==> regions_disjoint _ _ b n`
    (qspecl_then [`inst`,`ob`,`sz`] mp_tac) >> simp[]
QED

Finalise calldata_copy_finish_frame_mods
