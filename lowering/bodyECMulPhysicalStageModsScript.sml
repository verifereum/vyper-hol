(* The physical ECMul prefix ends at the compiler-selected launch cut. *)
Theory bodyECMulPhysicalStageMods
Ancestors
  bodyECMulPayloadCutMods bodyECMulPayloadFrameMods bodyBinopFragMemory
  bodyFullUnwrapSlotPost exprSimProps bodyFullBuiltinECArithOperands
  stmtReasonLitFragMemory bodyMemEcArithAssemble stateRelProj localPtrsProps
  lowerDloadPtrRel assignTuplePtrCopyLen stmtFragPtr bodyMemEcArithTransfers
  arithmeticProps venomInst venomState typedMemoryCopy loweringStateRelDefs
  compileEnv rich_list exprLoweringProps ptrDiscipline abiBufferAllocationCode
  exprSimHash bodyFullHashKeccakFixed bodyFullPostsMods exprSimWordArgs fragGasOriginPtrLoop
Libs monadsyntax

Theorem ecmul_copy_cursor[local]:
  (do x <- emit_op ADD [Var root; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [Var src; Lit 0w]; emit_void MSTORE [y;v] od) ca = ((),c1) /\
  (do x <- emit_op ADD [Var root; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [Var src; Lit 32w]; emit_void MSTORE [y;v] od) c1 = ((),c2) /\
  (do y <- emit_op ADD [Var src; Lit 64w]; emit_void MSTORE [y;scalar] od) c2 = ((),cpost) /\
  cpost.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cpost /\
  s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  alloca_history func s /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts ca cpost) (DROP s.vs_inst_idx bb.bb_instructions) /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
  t.vs_inst_idx = LENGTH cpost.cs_current_insts ==>
  alloca_history func t
Proof
  strip_tac >>
  qpat_assum `_ ca = ((),c1)` (mp_tac o MATCH_MP ec_point_word_transfer_shape) >>
  strip_tac >>
  qpat_assum `_ c1 = ((),c2)` (mp_tac o MATCH_MP ec_point_word_transfer_shape) >>
  strip_tac >>
  qpat_assum `_ c2 = ((),cpost)` (mp_tac o MATCH_MP ec_scalar_store_shape) >>
  strip_tac >>
  `emitted_insts c1 cpost = emitted_insts c1 c2 ++ emitted_insts c2 cpost` by
    (irule emitted_insts_prefix_split >> simp[]) >>
  `emitted_insts ca cpost = emitted_insts ca c1 ++ emitted_insts c1 cpost` by
    (irule emitted_insts_prefix_split >> simp[listTheory.APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts ca cpost)` by
    simp[mk_inst_def] >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts ca cpost)` by simp[] >>
  qabbrev_tac `code = emitted_insts ca cpost` >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)` suffices_by
    (qpat_assum `t.vs_inst_idx = s.vs_inst_idx + LENGTH code`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     `t with vs_inst_idx := t.vs_inst_idx = t` by
       simp[Once venom_state_component_equality] >> simp[]) >>
  irule alloca_history_no_alloca_slice >> simp[] >>
  fs[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem ecmul_copy_frames[local]:
  typed_copy_state_frame ca b 96 s t /\
  local_ptrs_reserved ce ca /\ local_ptrs_rel func ce es.scopes s /\
  (!name p sz. local_region ce es.scopes s name p sz ==> regions_disjoint b 96 p sz) /\
  (!aid p sz. aid < origin.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
    regions_disjoint b 96 p sz) /\
  MEM (mk_inst origin.cs_next_id ALLOCA [Lit 96w] [src]) (fn_insts func) /\
  FLOOKUP s.vs_allocas origin.cs_next_id = SOME (b,96) /\
  origin.cs_next_var <= ca.cs_next_var ==>
  wb_frame ce es es origin s t /\ pure_frame ce func es origin s t /\
  local_ptrs_rel func ce es.scopes t /\
  (!name p sz. local_region ce es.scopes t name p sz <=> local_region ce es.scopes s name p sz)
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[NoAsms, typed_copy_state_frame_def] >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `_ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!name e p sz. lookup_scopes name es.scopes = SOME e /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      lookup_var p t = lookup_var p s` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!k n. regions_disjoint k n b 96 ==>
    mem_bytes_at k n t.vs_memory = mem_bytes_at k n s.vs_memory` by
    (fs[typed_copy_frame_def, regions_disjoint_def] >>
     rpt gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `!name p sz. local_region ce es.scopes s name p sz ==>
    mem_bytes_at p sz t.vs_memory = mem_bytes_at p sz s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!k n. regions_disjoint k n b 96 ==>
         mem_bytes_at k n t.vs_memory = mem_bytes_at k n s.vs_memory` irule >>
     qpat_assum `!name p sz. local_region ce es.scopes s name p sz ==>
         regions_disjoint b 96 p sz` drule_all >>
     fs[regions_disjoint_def, DISJ_COMM]) >>
  `!x. not_fresh_at origin x ==> lookup_var x t = lookup_var x s` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  conj_tac
  >- (irule unwrap_slot_copy_wb_frame >> conj_tac
      >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
      reverse conj_tac >- (rpt gen_tac >> disch_tac >> simp[]) >>
      qexistsl_tac [`96`,`b`] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!name p sz. local_region ce es.scopes s name p sz ==>
              regions_disjoint b 96 p sz`
            (drule_then mp_tac) >> simp[regions_disjoint_def, DISJ_COMM]) >>
      conj_tac
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          qpat_assum `!aid p sz. aid < origin.cs_next_id /\ FLOOKUP s.vs_allocas aid = _ ==> _`
            (drule_all_then mp_tac) >>
          simp[regions_disjoint_def, DISJ_COMM]) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!k n. regions_disjoint k n b 96 ==> _`
        (qspecl_then [`off`,`len`] mp_tac) >> simp[regions_disjoint_def, DISJ_COMM]) >>
  conj_tac
  >- (irule pure_frame_fresh_alloca >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name p sz. local_region ce es.scopes s name p sz ==> _`
            (drule_then ACCEPT_TAC)) >>
      qexistsl_tac [`b`,`origin.cs_next_id`,`[Lit 96w]`,`[src]`,`96`] >> simp[]) >>
  conj_tac
  >- (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!name p sz. local_region ce es.scopes s name p sz ==> _`
            (drule_then mp_tac) >> simp[]) >>
      conj_tac
      >- metis_tac[] >>
      rpt gen_tac >> strip_tac >> fs[]) >>
  rpt gen_tac >> irule local_region_lookup_cong >> first_assum ACCEPT_TAC
QED

Theorem ecmul_physical_stage_given_alloc_mods:
  (!n a b buf s G tn.
    (n = 96 \/ n = 64) /\ compile_alloc_buffer n a = (buf,b) /\
    fn_has_code a b func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
    s.vs_inst_idx = LENGTH a.cs_current_insts /\ alloca_history func s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    local_ptrs_reserved ce a /\
    (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
    (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
    (?H. valid_horizon cx st0 H es2.storage_trace) /\
    local_ptrs_rel func ce es2.scopes s /\ immutable_frame_mods func ce cx es2 s /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
      stmt_state_rel H ctx func ce cx es2 s /\ ghost_inv_at_mods (DF H) lo d ce cx es2 G tn s) ==>
    ?dst w t G' tn'.
      buf.buf_operand = Var dst /\ lookup_var dst t = SOME w /\
      FLOOKUP t.vs_allocas a.cs_next_id = SOME (w2n w,n) /\
      ptr_covers G' tn' dst t n /\ not_fresh_at b dst /\
      lo <= w2n w /\ w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func t /\
      allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      t.vs_memory = s.vs_memory /\ t.vs_outcomes = s.vs_outcomes /\
      (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
      (!z. not_fresh_at a z ==> lookup_var z t = lookup_var z s /\
        FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!i. i IN tn'.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
      (!name p sz. local_region ce es2.scopes t name p sz ==>
        regions_disjoint (w2n w) n p sz) /\
      (!aid p sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,sz) ==>
        regions_disjoint (w2n w) n p sz) /\
      (!src tops. ALOOKUP ce.ce_modules src = SOME tops /\ ce.ce_is_ctor ==>
        !name tv iv off. FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n w) n off (type_memory_size tv)) /\
      wb_frame ce es2 es2 a s t /\ pure_frame ce func es2 a s t /\
      ghost_kept_at lo ce es2 a G tn s G' tn' /\
      local_ptrs_rel func ce es2.scopes t /\ immutable_frame_mods func ce cx es2 t /\
      (!H. valid_horizon cx st0 H es2.storage_trace ==>
        stmt_state_rel H ctx func ce cx es2 t /\ ghost_inv_at_mods (DF H) lo d ce cx es2 G' tn' t) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn'))) ==>
  compile_alloc_buffer 96 s2 = (ib,ca) /\
  (do x <- emit_op ADD [Var root; Lit 0w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [y;v] od) ca = ((),c1) /\
  (do x <- emit_op ADD [Var root; Lit 32w]; v <- emit_op MLOAD [x];
      y <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [y;v] od) c1 = ((),c2) /\
  (do y <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [y;scalar] od) c2 = ((),cpost) /\
  (do xp <- emit_op ADD [Var root; Lit 0w]; x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [Var root; Lit 32w]; y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [dst2; scalar] od) ca = ((),cpost) /\
  compile_alloc_buffer 64 cpost = (ob,sm) /\
  fn_has_code s2 ca func /\ fn_has_code ca cpost func /\ fn_has_code cpost sm func /\
  cpost.cs_current_bb = ca.cs_current_bb /\
  cpost.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cpost /\
  ci_mono s2 ca /\ ci_mono ca cpost /\ ci_mono cpost sm /\ fn_inst_ids_distinct func /\
  ~t2.vs_halted /\ t2.vs_current_bb = s2.cs_current_bb /\
  t2.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func t2 /\
  allocas_from lo t2 /\ lo <= t2.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
  local_ptrs_reserved ce s2 /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  (?H. valid_horizon cx st0 H es2.storage_trace) /\
  local_ptrs_rel func ce es2.scopes t2 /\ immutable_frame_mods func ce cx es2 t2 /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    stmt_state_rel H ctx func ce cx es2 t2 /\ ghost_inv_at_mods (DF H) lo d ce cx es2 G2 tn2 t2) /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME tops /\
  expr_val_at ce cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) point_cut s2 es2 v1 (Var root) t2 /\
  eval_operand (Var root) t2 = SOME wp /\ ptr_covers G2 tn2 root t2 64 /\
  not_fresh_at s2 root /\ w2n wp + 64 < dimword (:256) /\
  w2n wp + 64 <= t2.vs_alloca_next /\
  (!i. w2n wp <= i /\ i < w2n wp + 64 ==> i NOTIN tn2.t_mem) /\
  eval_operand scalar t2 = SOME q /\ op_taint tn2 scalar = {} /\
  (!l. scalar <> Label l) /\ (!z. scalar = Var z ==> not_fresh_at s2 z) /\
  es2.outcomes = SOME t2.vs_outcomes ==>
  ?src dst wi wo u Gu tnu.
    ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u /\
    not_fresh_at sm src /\ not_fresh_at sm dst /\
    s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved ce s2 /\ local_ptrs_reserved ce sm /\
    (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
    eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
    w2n wi + 96 <= u.vs_alloca_next /\ w2n wo + 64 <= u.vs_alloca_next /\
    lo <= w2n wo /\ t2.vs_alloca_next <= u.vs_alloca_next /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    ptr_covers Gu tnu src u 96 /\ ptr_covers Gu tnu dst u 64 /\
    (!i. w2n wi <= i /\ i < w2n wi + 96 ==> i NOTIN tnu.t_mem) /\
    mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n wp) t2.vs_memory /\
    mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n wp+32) t2.vs_memory /\
    mem_word_at (w2n wi+64) u.vs_memory = q /\ es2.outcomes = SOME u.vs_outcomes /\
    MEM (mk_inst cpost.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
    FLOOKUP u.vs_allocas cpost.cs_next_id = SOME (w2n wo,64) /\
    s2.cs_next_id <= cpost.cs_next_id /\
    (!name p sz. local_region ce es2.scopes u name p sz ==> regions_disjoint (w2n wo) 64 p sz) /\
    (!aid p sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (p,sz) ==>
      regions_disjoint (w2n wo) 64 p sz) /\
    (ce.ce_is_ctor ==> !name tv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,iv) ==>
      regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
    wb_frame ce es2 es2 s2 t2 u /\ pure_frame ce func es2 s2 t2 u /\
    immutable_frame_mods func ce cx es2 u /\ local_ptrs_rel func ce es2.scopes u /\
    ghost_kept_at lo ce es2 s2 G2 tn2 t2 Gu tnu /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t2,G2,tn2) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func ce cx es2 u /\ ghost_inv_at_mods (DF H) lo d ce cx es2 Gu tnu u /\
      stor_taint_ok_at (DF H) tnu u)
Proof
  disch_then (mk_asm "alloc") >> strip_tac >>
  asm "alloc" (qspecl_then [`96`,`s2`,`ca`,`ib`,`t2`,`G2`,`tn2`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[] >> HINT_EXISTS_TAC >> simp[])) >>
  disch_then (qx_choosel_then [`src`,`wi`,`ta`,`Ga`,`tna`] strip_assume_tac) >>
  `s2.cs_next_var <= ca.cs_next_var /\ s2.cs_next_id <= ca.cs_next_id /\
   ca.cs_next_var <= cpost.cs_next_var /\ ca.cs_next_id <= cpost.cs_next_id /\
   cpost.cs_next_var <= sm.cs_next_var /\ cpost.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved ce ca /\ local_ptrs_reserved ce cpost /\ local_ptrs_reserved ce sm` by
    (rpt conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `s2` >> simp[] >> decide_tac) >>
  `!z. not_fresh_at s2 z ==> not_fresh_at ca z /\ not_fresh_at cpost z /\ not_fresh_at sm z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `s2` >> simp[] >> decide_tac) >>
  `not_fresh_at ca root /\ !z. scalar = Var z ==> not_fresh_at ca z` by metis_tac[] >>
  `lookup_var root t2 = SOME wp` by fs[eval_operand_def] >>
  `lookup_var root ta = SOME wp /\ ptr_covers Ga tna root ta 64` by
    (qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z ta = _ /\ _`
       (drule_then strip_assume_tac) >> simp[] >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G2`,`t2`,`tn2`] >> simp[]) >>
  `eval_operand scalar ta = SOME q /\ op_taint tna scalar = {}` by
    (Cases_on `scalar` >> gvs[eval_operand_def, op_taint_def] >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z ta = _ /\ _`
       (drule_then strip_assume_tac) >> fs[op_taint_def]) >>
  `w2n wp+64 <= ta.vs_alloca_next /\ lo <= ta.vs_alloca_next` by decide_tac >>
  `!i. w2n wp <= i /\ i < w2n wp+64 ==> i NOTIN tna.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i IN tna.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. _ ==> i NOTIN tn2.t_mem` (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  `!aid p sz. aid < s2.cs_next_id /\ FLOOKUP t2.vs_allocas aid = SOME (p,sz) ==>
      regions_disjoint (w2n wi) 96 p sz` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP ta.vs_allocas aid = SOME (p,sz)` by metis_tac[] >>
     qpat_assum `!aid p sz. _ /\ FLOOKUP ta.vs_allocas aid = _ ==> _` (drule_all_then ACCEPT_TAC)) >>
  `regions_disjoint (w2n wi) 96 (w2n wp) 64` by
    (irule ec_point_fresh_scratch_disjoint >>
     qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `ta` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?bb. lookup_block ta.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts ca cpost) (DROP ta.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> strip_tac >> qexists_tac `bb` >> simp[]) >>
  qpat_assum `ib.buf_operand = Var src`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all ecmul_payload_cut_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`r`,`tp`,`Gp`,`tnp`] strip_assume_tac)) >>
  `MEM (mk_inst s2.cs_next_id ALLOCA [Lit 96w] [src]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer 96 s2 = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_code) >>
     irule hash_emitted_inst_mem >> qexistsl_tac [`s2`,`ca`] >> fs[]) >>
  `tp.vs_current_bb = ta.vs_current_bb /\ tp.vs_inst_idx = LENGTH cpost.cs_current_insts /\
   tp.vs_allocas = ta.vs_allocas /\ tp.vs_alloca_next = ta.vs_alloca_next /\
   tp.vs_outcomes = ta.vs_outcomes /\ ~tp.vs_halted` by
    (qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = ta` (SUBST1_TAC o SYM) >>
     simp[] >> qpat_assum `~ta.vs_halted` mp_tac >>
     qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = ta` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloca_history func tp` by
    (drule_all_then ACCEPT_TAC ecmul_copy_cursor) >>
  `allocas_from lo tp` by
    (qpat_assum `tp.vs_allocas = ta.vs_allocas` (fn th => pure_rewrite_tac [allocas_from_def,th]) >>
     qpat_assum `allocas_from lo ta` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  drule_all_then strip_assume_tac ecmul_copy_frames >>
  `!name tv iv off. ce.ce_is_ctor /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wi) 96 off (type_memory_size tv)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!owner decls. ALOOKUP ce.ce_modules owner = SOME decls /\ _ ==> _`
       (qspecl_then [`ce.ce_module`,`tops`] mp_tac) >> simp[] >> metis_tac[]) >>
  `!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z` by metis_tac[] >>
  `!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at ca z` by metis_tac[] >>
  `!h. valid_horizon cx st0 h es2.storage_trace ==>
    stmt_state_rel h ctx func ce cx es2 tp /\ immutable_frame_mods func ce cx es2 tp /\
    ghost_inv_at_mods (DF h) lo d ce cx es2 Gp tnp tp` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ ta /\ _`
       (drule_then strip_assume_tac) >>
     irule (Q.INST [`sc` |-> `s2`, `inst` |-> `mk_inst s2.cs_next_id ALLOCA [Lit 96w] [src]`]
       (SPEC_ALL ecmul_payload_frame_mods)) >>
     qpat_assum `run_inst_seq (emitted_insts ca cpost) ta = OK r` (irule_at Any) >>
     qpat_assum `MEM (mk_inst s2.cs_next_id ALLOCA [Lit 96w] [src]) (fn_insts func)`
       (irule_at Any) >>
     qpat_assum `typed_copy_state_frame ca (w2n wi) 96 ta tp` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF h) lo d ce cx es2 Ga tna ta` (irule_at Any) >>
     qexistsl_tac [`wp`,`q`,`scalar`,`root`] >>
     simp[mk_inst_def] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
     rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
  `immutable_frame_mods func ce cx es2 tp /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp tp)` by
    (qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ tp /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `tp.vs_current_bb = cpost.cs_current_bb /\ lo <= tp.vs_alloca_next` by simp[] >>
  `(!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at cpost z) /\
   (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at cpost z) /\
   (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by metis_tac[] >>
  asm_x "alloc" (qspecl_then [`64`,`cpost`,`sm`,`ob`,`tp`,`Gp`,`tnp`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[] >> HINT_EXISTS_TAC >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ tp /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`dst`,`wo`,`u`,`Gu`,`tnu`] strip_assume_tac) >>
  `MEM (mk_inst cpost.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer 64 cpost = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_code) >>
     irule hash_emitted_inst_mem >> qexistsl_tac [`cpost`,`sm`] >> fs[]) >>
  `not_fresh_at cpost src /\ not_fresh_at sm src` by
    (conj_tac >> irule not_fresh_at_mono >> qexists_tac `ca` >> simp[] >> decide_tac) >>
  `lookup_var src u = SOME wi /\ ptr_covers Gu tnu src u 96` by
    (qpat_assum `!z. not_fresh_at cpost z ==> lookup_var z u = _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- simp[] >> drule_all_then ACCEPT_TAC ptr_covers_lookup_frame) >>
  `!i. w2n wi <= i /\ i < w2n wi + 96 ==> i NOTIN tnu.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i < tp.vs_alloca_next` by decide_tac >>
     qpat_assum `!j. j IN tnu.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[pred_setTheory.IN_DIFF, arithmeticTheory.NOT_LESS_EQUAL]) >>
  `!i. i < t2.vs_alloca_next /\ i IN tnu.t_mem ==> i IN tn2.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i < tp.vs_alloca_next` by decide_tac >>
     `i IN tnp.t_mem` by
       (qpat_assum `!j. j IN tnu.t_mem <=> _` (qspec_then `i` mp_tac) >>
        simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
     `i IN tna.t_mem` by
       (qpat_x_assum `i IN tnp.t_mem` mp_tac >> simp[pred_setTheory.IN_DIFF]) >>
     qpat_assum `!j. j IN tna.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ t2 /\ _`
    (drule_then strip_assume_tac) >>
  `s2.cs_next_var <= cpost.cs_next_var /\ s2.cs_next_id <= cpost.cs_next_id` by decide_tac >>
  `wb_frame ce es2 es2 s2 t2 tp` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t2` (mp_then Any irule wb_frame_trans) >>
     qpat_assum `wb_frame ce es2 es2 s2 t2 ta` (irule_at Any) >>
     qpat_assum `wb_frame ce es2 es2 s2 ta tp` (irule_at Any) >> simp[]) >>
  `wb_frame ce es2 es2 s2 t2 u` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t2` (mp_then Any irule wb_frame_trans) >>
     qpat_assum `wb_frame ce es2 es2 s2 t2 tp` (irule_at Any) >>
     qpat_assum `wb_frame ce es2 es2 cpost tp u` (irule_at Any) >> simp[]) >>
  `pure_frame ce func es2 s2 t2 tp` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es2`,`s2`,`ta`] >> simp[] >>
     rpt strip_tac >> qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z ta = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `pure_frame ce func es2 s2 t2 u` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es2`,`cpost`,`tp`] >> conj_tac >- first_assum ACCEPT_TAC >>
     simp[]) >>
  `ghost_kept_at lo ce es2 s2 G2 tn2 t2 Gu tnu` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ t2` (mp_then Any irule ec_staging_ghost_kept_at) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!z. not_fresh_at s2 z ==> not_fresh_at ca z /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!z. not_fresh_at cpost z ==> lookup_var z u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `!z. not_fresh_at ca z ==> lookup_var z tp = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z ta = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n wp) t2.vs_memory /\
   mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n wp+32) t2.vs_memory /\
   mem_word_at (w2n wi+64) u.vs_memory = q` by
    (qpat_assum `u.vs_memory = tp.vs_memory` SUBST1_TAC >>
     qpat_assum `ta.vs_memory = t2.vs_memory` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `es2.outcomes = SOME u.vs_outcomes` by simp[] >>
  `s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
   w2n wi + 96 <= u.vs_alloca_next /\ t2.vs_alloca_next <= u.vs_alloca_next` by
     decide_tac >>
  `eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo` by
    simp[eval_operand_def] >>
  `!aid p sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (p,sz) ==>
     regions_disjoint (w2n wo) 64 p sz` by
    (rpt gen_tac >> strip_tac >>
     `aid < cpost.cs_next_id` by decide_tac >>
     qpat_assum `!aid p sz. aid < cpost.cs_next_id /\ FLOOKUP u.vs_allocas aid = _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `(ce.ce_is_ctor ==> !name tv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 64 off (type_memory_size tv))` by
    (disch_tac >>
     qpat_assum `!owner decls. ALOOKUP ce.ce_modules owner = SOME decls /\ _ ==> _`
       (qspecl_then [`ce.ce_module`,`tops`] mp_tac) >> simp[]) >>
  qexistsl_tac [`src`,`dst`,`wi`,`wo`,`u`,`Gu`,`tnu`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  rpt gen_tac >> disch_tac >> rename1 `valid_horizon cx st0 h es2.storage_trace` >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel h _ _ _ _ _ u /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Ga`,`ta`,`tna`] >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gp`,`tp`,`tnp`] >>
      conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `ghost_inv_at_mods (DF h) _ _ _ _ _ Gu tnu u`
    (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
