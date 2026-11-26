(* The three real ECAdd cuts, from the second operand to the generated GAS. *)
Theory bodyECAddStageMods
Ancestors
  bodyECAddLaunchCodeMods bodyECAddAllocFrameMods bodyECAddPayloadCutMods
  bodyECAddPayloadFrameMods bodyMemEcArithAssemble bodyFullBuiltinECArithOperands
  bodyFullUnwrapSlotPost bodyFullUnwrapRun stateRelProj exprSimProps
  gasExplicitSites fragGasOriginPtr bodyFullShadowBodyInv vyperStorageFootprint
  exprLoweringProps venomMemDefs ptrDiscipline bodyPtrDefs freshWrites
  stmtReasonLitFragMemory bodyMemEcArithTransfers arithmeticProps venomInst
  venomState loweringHalt fragExec compileEnv loweringStateRelDefs words
  loweringPosts bodyFullAllocaFresh list
Libs monadsyntax horizonTypeLib

val stage_raw_alloc =
  horizonTypeLib.at_horizon alloc_buffer_origin_ptr_path_with_raw_endpoint

Theorem ecadd_stage_fmp[local]:
  stmt_state_rel H ctx func ce cx es s ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp s
Proof
  strip_tac >> strip_tac >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  fs[fmp_room_def,allocas_below_fmp_def] >>
  `alloca_next_valid s` by fs[stmt_state_rel_def,alloca_inv_def] >>
  fs[alloca_next_valid_def] >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem ecadd_stage_payload_code[local]:
  !p q b ca c1 c2 c3 cp.
  (do x <- emit_op ADD [p; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 0w]; emit_void MSTORE [y; v] od) ca = ((),c1) /\
  (do x <- emit_op ADD [p; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 32w]; emit_void MSTORE [y; v] od) c1 = ((),c2) /\
  (do x <- emit_op ADD [q; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 64w]; emit_void MSTORE [y; v] od) c2 = ((),c3) /\
  (do x <- emit_op ADD [q; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [b; Lit 96w]; emit_void MSTORE [y; v] od) c3 = ((),cp) ==>
  cp.cs_current_bb = ca.cs_current_bb /\
  cp.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cp /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca cp)
Proof
  rpt gen_tac >> strip_tac >> dxrule_then strip_assume_tac ec_point_word_transfer_shape >>
  dxrule_then strip_assume_tac ec_point_word_transfer_shape >>
  dxrule_then strip_assume_tac ec_point_word_transfer_shape >>
  dxrule_then strip_assume_tac ec_point_word_transfer_shape >>
  conj_tac >- fs[same_blocks_def] >>
  pure_rewrite_tac[emitted_insts_def] >>
  PURE_ASM_REWRITE_TAC[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
  REWRITE_TAC[listTheory.EVERY_APPEND,listTheory.EVERY_DEF,mk_inst_def] >> simp[is_terminator_def]
QED

Theorem ecadd_stage_covered[local]:
  lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) /\ ptr_covers G tn p s n ==>
  ptr_covers G' tn' p t n
Proof
  simp[ptr_covers_def]
QED

Theorem ecadd_stage_not_fresh[local]:
  ci_mono a b /\ not_fresh_at a x ==> not_fresh_at b x
Proof
  strip_tac >> irule not_fresh_at_mono >> qexists `a` >> fs[ci_mono_def]
QED

Theorem ecadd_stage_mods:
  compile_ecadd_points (Var p) (Var q) sf = (res,sb) /\
  compile_ecadd_points (Var p) (Var q) shf = (shres,shb) /\
  gas_shadow_state sf shf /\ gas_shadow_context ctx shctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code sf sb func /\ fn_has_code shf shb shfunc /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sf /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (lo <> 0 ==> !x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sf x) /\
  ~s.vs_halted /\ s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts /\ alloca_history func s /\
  valid_horizon cx st0 H0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  expr_val_at ce cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lp sf es vp (Var p) s /\
  expr_val_at ce cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lq sf es vq (Var q) s /\
  lookup_var p s = SOME wp /\ lookup_var q s = SOME wq /\
  ptr_covers G tn p s 64 /\ ptr_covers G tn q s 64 /\
  not_fresh_at sf p /\ not_fresh_at sf q /\
  w2n wp + 64 < dimword (:256) /\ w2n wq + 64 < dimword (:256) /\
  w2n wp + 64 <= s.vs_alloca_next /\ w2n wq + 64 <= s.vs_alloca_next /\
  (!i. w2n wp <= i /\ i < w2n wp+64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n wq <= i /\ i < w2n wq+64 ==> i NOTIN tn.t_mem) ==>
  ?ib ca cp ob sm shm src dst gv cv bb wi wo u Gu tnu.
    compile_alloc_buffer 128 sf = (ib,ca) /\ compile_alloc_buffer 64 cp = (ob,sm) /\
    ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\ res = Var dst /\ shres = res /\
    gas_shadow_state sm shm /\ fn_has_code sm sb func /\ fn_has_code shm shb shfunc /\
    ci_mono sf sm /\ ci_mono sm sb /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id GAS [] [gv];
       mk_inst (sm.cs_next_id+1) STATICCALL
         [Var gv; Lit 6w; Var src; Lit 128w; Var dst; Lit 64w] [cv];
       mk_inst (sm.cs_next_id+2) ASSERT [Var cv] []] /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    src <> gv /\ dst <> gv /\ src <> cv /\ dst <> cv /\
    not_fresh_at sm src /\ not_fresh_at sm dst /\
    ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\ local_ptrs_reserved ce sm /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (lo <> 0 ==> !x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP u.vs_inst_idx bb.bb_instructions) /\
    (func.fn_name,sm.cs_next_id) NOTIN gas_explicit_sites ctx shctx /\
    lookup_var src u = SOME wi /\ lookup_var dst u = SOME wo /\
    w2n wi+128 < dimword (:256) /\ w2n wo+64 < dimword (:256) /\
    w2n wi+128 <= u.vs_alloca_next /\ w2n wo+64 <= u.vs_alloca_next /\
    lo <= w2n wo /\ s.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w] [src]) (fn_insts func) /\
    MEM (mk_inst cp.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    sf.cs_next_id <= cp.cs_next_id /\
    FLOOKUP u.vs_allocas sf.cs_next_id = SOME (w2n wi,128) /\
    FLOOKUP u.vs_allocas cp.cs_next_id = SOME (w2n wo,64) /\
    regions_disjoint (w2n wo) 64 (w2n wi) 128 /\
    mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n wp) s.vs_memory /\
    mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n wp+32) s.vs_memory /\
    mem_word_at (w2n wi+64) u.vs_memory = mem_word_at (w2n wq) s.vs_memory /\
    mem_word_at (w2n wi+96) u.vs_memory = mem_word_at (w2n wq+32) s.vs_memory /\
    pure_frame ce func es sf s u /\ wb_frame ce es es sf s u /\
    (!z. not_fresh_at sf z ==> lookup_var z u = lookup_var z s) /\
    (!i. w2n wi <= i /\ i < w2n wi+128 ==> i NOTIN tnu.t_mem) /\
    ptr_covers Gu tnu src u 128 /\ ptr_covers Gu tnu dst u 64 /\
    (!name b n. local_region ce es.scopes u name b n ==>
       regions_disjoint (w2n wo) 64 b n) /\
    (!aid b n. aid < sf.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint (w2n wo) 64 b n) /\
    immutable_frame_mods func ce cx es u /\
    (!src tops. ALOOKUP ce.ce_modules src = SOME tops /\ ce.ce_is_ctor ==>
      (!name ty tv off. FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        ce.ce_module_var_type (src,name) = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
        regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
      (!name tv iv off. FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
                  | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n wo) 64 off (type_memory_size tv))) /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) [] (OK u,Gu,tnu) /\
      ghost_kept_at lo ce es sf G tn s Gu tnu /\
      stmt_state_rel H ctx func ce cx es u /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx es Gu tnu u /\
      local_ptrs_rel func ce es.scopes u /\ allocas_from lo u /\
      stor_taint_ok_at (DF H) tnu u
Proof
  strip_tac >>
  qabbrev_tac `explicit = gas_explicit_sites ctx shctx` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all ecadd_launch_code_mods >>
  disch_then (qx_choosel_then [`ib`,`ca`,`c1`,`c2`,`c3`,`cpost`,`ob`,`sm`,`shm`,
                              `src`,`dst`,`gv`,`cv`] strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by drule_then ACCEPT_TAC ecadd_stage_fmp >>
  `128 < dimword (:256) /\ 64 < dimword (:256)` by simp[dimword_def] >>
  drule_all (Q.SPEC `128` (Q.GEN `n` stage_raw_alloc)) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`src0`,`wi`,`salloc`,`Ga`,`tna`,`ra`] strip_assume_tac)) >>
  `src0 = src` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `salloc = ra with vs_inst_idx := _` (mk_asm "input_cursor") >>
  `salloc.vs_memory = s.vs_memory /\ ~salloc.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `salloc with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es salloc` by
    (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==> stmt_state_rel h _ _ _ _ _ salloc`
       irule >> first_assum ACCEPT_TAC) >>
  `lo <= w2n wi /\ lo <= salloc.vs_alloca_next` by
    (conj_tac >-
       (qpat_assum `allocas_from lo salloc` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
        qpat_assum `!aid b n. FLOOKUP salloc.vs_allocas aid = _ ==> _`
          (drule_then ACCEPT_TAC)) >> decide_tac) >>
  `lookup_var p salloc = SOME wp /\ lookup_var q salloc = SOME wq` by simp[] >>
  `ptr_covers Ga tna p salloc 64 /\ ptr_covers Ga tna q salloc 64` by
    (conj_tac >> irule ecadd_stage_covered >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `(!i. w2n wp <= i /\ i < w2n wp+64 ==> i NOTIN tna.t_mem) /\
   (!i. w2n wq <= i /\ i < w2n wq+64 ==> i NOTIN tna.t_mem)` by
    (conj_tac >> rpt strip_tac >>
     qpat_assum `!j. j IN tna.t_mem <=> _` (qspec_then `i` mp_tac) >>
     `i < s.vs_alloca_next` by decide_tac >>
     `i NOTIN tn.t_mem` by simp[] >> simp[]) >>
  `regions_disjoint (w2n wi) 128 (w2n wp) 64` by
    (qpat_assum `expr_val_at _ _ _ lp _ _ _ (Var p) _`
       (mp_then Any mp_tac ec_point_fresh_scratch_disjoint) >>
     disch_then irule >>
     (conj_tac >- (qexists `salloc` >> conj_tac >- first_assum ACCEPT_TAC >> simp[])) >>
     (conj_tac >- first_assum ACCEPT_TAC) >> simp[eval_operand_def]) >>
  `regions_disjoint (w2n wi) 128 (w2n wq) 64` by
    (qpat_assum `expr_val_at _ _ _ lq _ _ _ (Var q) _`
       (mp_then Any mp_tac ec_point_fresh_scratch_disjoint) >>
     disch_then irule >>
     (conj_tac >- (qexists `salloc` >> conj_tac >- first_assum ACCEPT_TAC >> simp[])) >>
     (conj_tac >- first_assum ACCEPT_TAC) >> simp[eval_operand_def]) >>
  `not_fresh_at ca p /\ not_fresh_at ca q` by
    (conj_tac >> irule ecadd_stage_not_fresh >> qexists `sf` >> simp[]) >>
  `w2n wp+64 <= salloc.vs_alloca_next /\ w2n wq+64 <= salloc.vs_alloca_next` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp salloc` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ salloc` (ACCEPT_TAC o MATCH_MP ecadd_stage_fmp)) >>
  drule_all ecadd_stage_payload_code >> strip_tac >>
  drule_all (Q.SPECL [`ca`,`cpost`,`func`] fn_has_code_code) >>
  disch_then (qx_choose_then `bbpay` strip_assume_tac) >>
  `lookup_block salloc.vs_current_bb func.fn_blocks = SOME bbpay /\
   isPREFIX (emitted_insts ca cpost) (DROP salloc.vs_inst_idx bbpay.bb_instructions)` by simp[] >>
  `!z. not_fresh_at sf z ==> not_fresh_at ca z` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC ecadd_stage_not_fresh) >>
  `!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z` by simp[] >>
  `!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z` by simp[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es salloc /\
     immutable_frame_mods func ce cx es salloc /\
     ghost_inv_at_mods (DF H) lo d ce cx es Ga tna salloc` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
     conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     asm "input_cursor" assume_tac >>
     qpat_assum `run_inst_seq (emitted_insts sf ca) s = OK ra`
       (mp_then Any mp_tac ecadd_alloc_frame_mods) >>
     disch_then drule_all >> strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ib.buf_operand = Var src`
    (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]) >> mk_asm "input_operand" th) >>
  drule_all ecadd_payload_cut_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`rp`,`spay`,`Gp`,`tnp`] strip_assume_tac)) >>
  qpat_x_assum `spay = rp with vs_inst_idx := _` (mk_asm "payload_cursor") >>
  qpat_x_assum `spay.vs_memory = _` kall_tac >>
  `~spay.vs_halted /\ spay.vs_current_bb = cpost.cs_current_bb /\
   spay.vs_inst_idx = LENGTH cpost.cs_current_insts` by
    (qpat_assum `rp with <|vs_vars := _; vs_memory := _|> = salloc`
       (strip_assume_tac o SRULE[venom_state_component_equality]) >>
     asm "payload_cursor" (fn th => simp[th])) >>
  `alloca_history func spay` by
    (`alloca_inv salloc` by
       (qpat_assum `stmt_state_rel H0 _ _ _ _ _ salloc`
          (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
     asm "payload_cursor" SUBST1_TAC >>
     drule_all_then ACCEPT_TAC (Q.SPECL [`emitted_insts ca cpost`,`ca`,`cpost`]
                                         emitted_alloca_history)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es spay /\
     immutable_frame_mods func ce cx es spay /\
     ghost_inv_at_mods (DF H) lo d ce cx es Gp tnp spay /\
     spay.vs_allocas = salloc.vs_allocas /\ spay.vs_alloca_next = salloc.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ salloc /\ _`
       drule >> strip_tac >>
     asm "payload_cursor" assume_tac >>
     qpat_assum `stmt_state_rel H _ _ _ _ _ salloc`
       (mp_then Any mp_tac ecadd_payload_frame_mods) >>
     disch_then drule_all >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ spay /\ _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo spay /\ lo <= spay.vs_alloca_next` by
    ((qpat_assum `allocas_from lo salloc` mp_tac >> simp[allocas_from_def] >> (gvs[allocas_from_def]))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp spay` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ spay` (ACCEPT_TAC o MATCH_MP ecadd_stage_fmp)) >>
  drule_all (Q.SPEC `64` (Q.GEN `n` stage_raw_alloc)) >>
  disch_then (qspecl_then [`tnp`,`explicit`,`PG`,`Gp`]
    (qx_choosel_then [`dst0`,`wo`,`u`,`Gu`,`tnu`,`ru`] strip_assume_tac)) >>
  `dst0 = dst` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `u = ru with vs_inst_idx := _` (mk_asm "output_cursor") >>
  `u.vs_memory = spay.vs_memory /\ ~u.vs_halted` by
    (qpat_assum `~spay.vs_halted` mp_tac >>
     qpat_assum `u with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = spay` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H0 ctx func ce cx es u` by
    (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ spay ==> stmt_state_rel h _ _ _ _ _ u`
       irule >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ u` (ACCEPT_TAC o MATCH_MP ecadd_stage_fmp)) >>
  `lo <= w2n wo` by
    (qpat_assum `allocas_from lo u` (assume_tac o REWRITE_RULE[allocas_from_def]) >>
     qpat_assum `!aid b n. FLOOKUP u.vs_allocas aid = _ ==> _` (drule_then ACCEPT_TAC)) >>
  qpat_assum `!t. ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\ _ ==> _`
    (qspec_then `u` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `bb` strip_assume_tac)) >>
  `!z. not_fresh_at sf z ==> not_fresh_at cpost z` by
    (rpt strip_tac >> irule ecadd_stage_not_fresh >> qexists `ca` >> simp[]) >>
  `!z. not_fresh_at sf z ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule ecadd_stage_not_fresh >> qexists `cpost` >> simp[]) >>
  `!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at cpost z` by simp[] >>
  `!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at cpost z` by simp[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es u /\ ghost_inv_at_mods (DF H) lo d ce cx es Gu tnu u` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ spay /\ _`
       drule >> strip_tac >>
     conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     asm "output_cursor" assume_tac >>
     qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ spay`
       (mp_then Any mp_tac ecadd_alloc_frame_mods) >>
     disch_then drule_all >> strip_tac >> first_assum ACCEPT_TAC) >>
  asm "output_cursor" assume_tac >>
  qpat_assum `run_inst_seq (emitted_insts cpost sm) spay = OK ru`
    (mp_then Any mp_tac ecadd_alloc_frame_mods) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `u = ru with vs_inst_idx := _` kall_tac >>
  `sf.cs_next_id < cpost.cs_next_id` by
    (qpat_assum `compile_alloc_buffer 128 sf = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >> fs[ci_mono_def]) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP u.vs_allocas aid = SOME e` by
    (rpt strip_tac >>
     qpat_assum `!id e. FLOOKUP spay.vs_allocas id = SOME e ==> _` irule >>
     simp[]) >>
  `FLOOKUP u.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` by
    (qpat_assum `!id e. FLOOKUP spay.vs_allocas id = SOME e ==> _` irule >> simp[]) >>
  `allocas_non_overlapping u` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ u`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[alloca_inv_def]) >>
  `!aid b n. aid < cpost.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint (w2n wo) 64 b n` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `allocas_non_overlapping u`
       (mp_tac o REWRITE_RULE[allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`cpost.cs_next_id`,`aid`,`w2n wo`,`64`,`b`,`n`] mp_tac) >>
     `cpost.cs_next_id <> aid` by decide_tac >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `regions_disjoint (w2n wo) 64 (w2n wi) 128` by
    (qpat_assum `!aid b n. aid < cpost.cs_next_id /\ _ ==> _`
       (qspecl_then [`sf.cs_next_id`,`w2n wi`,`128`] mp_tac) >> simp[]) >>
  `!aid b n. aid < sf.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint (w2n wo) 64 b n` by
    (rpt gen_tac >> strip_tac >> `aid < cpost.cs_next_id` by decide_tac >>
     qpat_assum `!aid b n. aid < cpost.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`n`] mp_tac) >> simp[]) >>
  `!z. not_fresh_at sf z ==> lookup_var z u = lookup_var z s /\
     FLOOKUP Gu z = FLOOKUP G z /\ op_taint tnu (Var z) = op_taint tn (Var z)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!z. not_fresh_at sf z ==> lookup_var z salloc = _ /\ _`
       (drule_then strip_assume_tac) >>
     `not_fresh_at ca z /\ not_fresh_at cpost z` by simp[] >>
     qpat_assum `!z. not_fresh_at ca z ==> lookup_var z spay = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ptr_covers Gu tnu src u 128` by
    (irule ecadd_stage_covered >> qexistsl_tac [`Gp`,`spay`,`tnp`] >> simp[]) >>
  `lookup_var src u = SOME wi` by simp[] >>
  `w2n wi + 128 <= u.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!b n. regions_disjoint (w2n wi) 128 b n ==>
     mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory` by simp[] >>
  `!name b n. local_region ce es.scopes s name b n ==>
     regions_disjoint (w2n wi) 128 b n` by
    (rpt gen_tac >> strip_tac >>
     `local_region ce es.scopes salloc name b n` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s`,`sf`,`es.scopes`] >> simp[]) >>
     qpat_assum `!name b n. local_region ce es.scopes salloc name b n ==> _`
       (drule_then ACCEPT_TAC)) >>
  `pure_frame ce func es sf s u` by
    (irule pure_frame_fresh_alloca >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!name b n. local_region ce es.scopes s name b n ==> _`
           (drule_then assume_tac) >> simp[]) >>
     qexistsl_tac [`w2n wi`,`sf.cs_next_id`,`[Lit 128w]`,`[src]`,`128`] >>
     simp[] >> rpt strip_tac >>
     `regions_disjoint (w2n wi) 128 off len` by
       fs[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM] >> simp[]) >>
  `wb_frame ce es es sf s u` by
    (irule unwrap_slot_copy_wb_frame >> conj_tac
     >- (rpt strip_tac >> simp[]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`128`,`w2n wi`] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!name b n. local_region ce es.scopes s name b n ==> _`
           (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!aid b n. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!b n. regions_disjoint (w2n wi) 128 b n ==> mem_bytes_at b n u.vs_memory = _`
       (qspecl_then [`off`,`len`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tnu.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i < spay.vs_alloca_next` by decide_tac >>
     qpat_assum `!j. j IN tnu.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[pred_setTheory.IN_DIFF]) >>
  `!i. i < s.vs_alloca_next /\ i IN tnu.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i < spay.vs_alloca_next` by decide_tac >>
     qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
     `i IN tna.t_mem` by
       (qpat_assum `!j. j IN tnu.t_mem <=> _` (qspec_then `i` mp_tac) >>
        simp[pred_setTheory.IN_DIFF, arithmeticTheory.NOT_LESS_EQUAL] >> strip_tac) >>
     qpat_assum `!j. j IN tna.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `ghost_kept_at lo ce es sf G tn s Gu tnu` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
       (mp_then Any irule ec_staging_ghost_kept_at) >> simp[] >>
     rpt strip_tac >> simp[]) >>
  `ci_mono sf sm` by
    (`ci_mono sf cpost` by (irule ci_mono_trans >> qexists `ca` >> simp[]) >>
     irule ci_mono_trans >> qexists `cpost` >> simp[]) >>
  `sf.cs_next_id <= cpost.cs_next_id` by decide_tac >>
  asm "input_operand" assume_tac >>
  qexistsl_tac [`ib`,`ca`,`cpost`,`ob`,`sm`,`shm`,`src`,`dst`,`gv`,`cv`,`bb`,
                `wi`,`wo`,`u`,`Gu`,`tnu`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (rpt strip_tac >> simp[])
  >- (rpt strip_tac >> simp[])
  >- (rpt strip_tac >> simp[])
  >- simp[Abbr `explicit`]
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ u /\ _`
    drule >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ s /\ _`
    drule >> strip_tac >>
  conj_tac
  >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Ga`,`salloc`,`tna`] >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gp`,`spay`,`tnp`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ u`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ Gu tnu u`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
