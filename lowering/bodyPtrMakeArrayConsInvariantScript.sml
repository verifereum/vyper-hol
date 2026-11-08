(* Compact interfaces avoid repeating large endpoint conjunctions in each
   store branch.  Cells describe initialized values, not a partial aggregate. *)
Theory bodyPtrMakeArrayConsInvariant
Ancestors
  bodyPtrMakeArrayMemoryFrame bodyPtrDefs loweringPosts exprSimProps
  wordArgsPtr tupleMemoryFrame compileEnv venomState list pair
  exprSimWordArgs vyperEvalExprPreservesScopesDom freshWrites

Definition literal_prefix_ok_def:
  literal_prefix_ok cells tn s <=>
    EVERY (\(tv,v,p,k). val_wf tv v /\ val_footprint tv v <= k /\
      !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) cells
End

(* fr is the outer frontier, BEFORE aid.  In particular, stores may modify
   the literal allocation although it is old at each child entry. *)
Definition literal_loop_frame_def:
  literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es cs G tn s cells off <=>
    stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
    wb_frame ce ees fr sf s /\
    ghost_kept ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM es.scopes /\
    ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    addr + capacity <= dimword(:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce es.scopes s name p k ==>
       addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
       addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME (p,k) /\ old < fr.cs_next_id ==>
       addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells
End

Theorem literal_prefix_nil[simp]:
  literal_prefix_ok [] tn s
Proof
  simp[literal_prefix_ok_def]
QED

Theorem literal_prefix_append[simp]:
  literal_prefix_ok (xs ++ ys) tn s <=>
  literal_prefix_ok xs tn s /\ literal_prefix_ok ys tn s
Proof
  simp[literal_prefix_ok_def, EVERY_APPEND]
QED

Theorem literal_prefix_cell:
  literal_prefix_ok [(tv,v,p,k)] tn s <=>
  val_wf tv v /\ val_footprint tv v <= k /\
  !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m
Proof
  simp[literal_prefix_ok_def]
QED

Theorem literal_prefix_lookup:
  literal_prefix_ok cells tn s /\ MEM (tv,v,p,k) cells ==>
  val_wf tv v /\ val_footprint tv v <= k /\
  !m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m
Proof
  simp[literal_prefix_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem literal_prefix_transport:
  literal_prefix_ok cells tn s /\
  (!tv v p k. MEM (tv,v,p,k) cells /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v p m) ==>
  literal_prefix_ok cells tm z
Proof
  simp[literal_prefix_ok_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem literal_loop_frame_runtime:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off ==>
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ghost_kept ce ees fr Gf tnf sf G tn /\ ~s.vs_halted /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts
Proof
  simp[literal_loop_frame_def]
QED

Theorem literal_loop_frame_allocation:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off ==>
  not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
  FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
  addr+capacity <= dimword(:256) /\ fr.cs_next_id <= aid /\
  aid < cs.cs_next_id /\ fr.cs_next_var <= cs.cs_next_var /\ off <= capacity
Proof
  simp[literal_loop_frame_def]
QED

Theorem literal_loop_store_ghost:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off ==>
  ghost_kept ce es fr Gf tnf sf G tn
Proof
  simp[literal_loop_frame_def] >> rpt strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def] >>
  metis_tac[local_region_scopes_domain]
QED

Theorem literal_loop_store_exterior:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off /\
  w2n b = addr+off /\ off+k <= capacity ==>
  (!name p n i. local_region ce es.scopes s name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k)) /\
  (!old p n i. FLOOKUP sf.vs_allocas old = SOME (p,n) /\
    old < fr.cs_next_id /\ p <= i /\ i < p+n ==>
    ~(w2n b <= i /\ i < w2n b+k)) /\
  (!name p n i. local_region ce es.scopes sf name p n /\
    p <= i /\ i < p+n ==> ~(w2n b <= i /\ i < w2n b+k))
Proof
  simp[literal_loop_frame_def] >> rpt strip_tac >>
  `!name p n. local_region ce es.scopes sf name p n ==>
     addr+capacity <= p \/ p+n <= addr` by
    (drule local_region_scopes_domain >>
     disch_then (qspecl_then [`ce`, `sf`] assume_tac) >>
     qpat_x_assum `!name p k. local_region ce ees.scopes sf name p k ==> _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `addr+capacity <= p \/ p+n <= addr` by metis_tac[arithmeticTheory.ADD_COMM] >> decide_tac
QED

Theorem literal_loop_prefix_geometry:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off /\ MEM (tv,v,p,k) cells ==>
  addr <= p /\ p+k <= addr+off /\ p+k <= addr+capacity
Proof
  simp[literal_loop_frame_def, EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac
QED

Theorem literal_prefix_expr_frame:
  expr_post ctx func ce cx e esi si sb s0 es' v op z /\
  ghost_kept ce esi si G0 tn0 s0 H tm /\
  FLOOKUP s0.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  (!name b n. local_region ce esi.scopes s0 name b n ==>
     addr+capacity <= b \/ b+n <= addr) /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+capacity) cells /\
  literal_prefix_ok cells tn0 s0 ==>
  literal_prefix_ok cells tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule literal_prefix_transport >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `val_wf tv v' /\ val_footprint tv v' <= k` by
    metis_tac[literal_prefix_lookup] >>
  `addr <= p /\ p+k <= addr+capacity` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     simp[EVERY_MEM, FORALL_PROD] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl [`tn0.t_mem`, `tm.t_mem`, `s0.vs_memory`, `z.vs_memory`, `k`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> `addr <= i /\ i < addr+capacity` by decide_tac >>
      qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_kept_def] >> metis_tac[]) >>
  `mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s0.vs_memory` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> metis_tac[]) >>
  drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`p-addr`, `k`] mp_tac) >>
  `p-addr+k <= capacity /\ addr+(p-addr) = p` by decide_tac >> simp[]
QED

Theorem literal_outer_frame_expr:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  stmt_state_rel ctx func ce cx ees sf /\ local_ptrs_reserved ce fr /\
  expr_post ctx func ce cx e esi si sb s0 es' v op z /\
  ghost_kept ce esi si G0 tn0 s0 H tm ==>
  wb_frame ce ees fr sf z /\ ghost_kept ce ees fr Gf tnf sf H tm
Proof
  simp[literal_loop_frame_def] >> rpt strip_tac >>
  `wb_frame ce esi si s0 z` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `fr.cs_next_id <= si.cs_next_id` by decide_tac >>
  metis_tac[wb_frame_trans, ghost_kept_wb_trans]
QED

Theorem literal_loop_frame_materialized:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\
  stmt_state_rel ctx func ce cx ees sf /\
  local_ptrs_reserved ce fr /\ local_ptrs_reserved ce si /\
  expr_post ctx func ce cx e esi si sb s0 es' v op z /\
  ghost_kept ce esi si G0 tn0 s0 H tm /\ ghost_inv d ce cx es' H tm z /\
  eval_expr cx e esi = (res,es') /\
  si.cs_next_var <= sb.cs_next_var /\ si.cs_next_id <= sb.cs_next_id /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es' sb H tm z cells off /\ literal_prefix_ok cells tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_outer_frame_expr >> strip_tac >>
  qpat_x_assum `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >> simp[literal_loop_frame_def] >> strip_tac >>
  `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  `wb_frame ce esi si s0 z /\ stmt_state_rel ctx func ce cx es' z` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (`EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+capacity) cells` by
        (gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
         first_x_assum drule >> strip_tac >> decide_tac) >>
      `!name b n. local_region ce esi.scopes s0 name b n ==>
         addr+capacity <= b \/ b+n <= addr` by metis_tac[arithmeticTheory.ADD_COMM] >>
      drule_all literal_prefix_expr_frame >> simp[]) >>
  `!name p k. local_region ce esi.scopes s0 name p k <=>
              local_region ce es'.scopes z name p k` by
    (drule_all wb_frame_local_regions >> simp[]) >>
  `lookup_var root z = SOME (n2w addr)` by gvs[wb_frame_def] >>
  `FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` by gvs[wb_frame_def] >>
  `FLOOKUP H root = SOME (addr,capacity) /\ ptr_covers H tm root z capacity` by
    (gvs[ghost_kept_def, ptr_covers_def] >> metis_tac[]) >>
  `not_fresh_at sb root` by metis_tac[not_fresh_at_mono] >>
  `aid < sb.cs_next_id /\ fr.cs_next_var <= sb.cs_next_var` by decide_tac >>
  simp[literal_loop_frame_def] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem literal_loop_frame_advance:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s cells off /\ off+k <= capacity ==>
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es cs G tn s (cells ++ [(tv,v,addr+off,k)]) (off+k)
Proof
  simp[literal_loop_frame_def, EVERY_APPEND, EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac
QED
