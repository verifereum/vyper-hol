(* Semantic transport at the actual allocation and copy endpoints. *)
Theory bodyCopyMaterializedRhsPostMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullUnwrapSlotPost
  exprPtrUnwrapAllocSemantic exprPtrUnwrapStoragePost robustCopyTransportPtr
  exprSimCopy exprSimStorageCopy exprSimProps exprLoweringProps loweringSlice
  bodyInvSplit loweringPosts loweringStateRelDefs localPtrsProps bodyPtrDefs
  ptrDiscipline freshWrites compileEnv valueEncodingProps venomInst venomState
  context arithmetic finite_map pred_set words
  actualAllocExec[qualified] frameActivationSeparation exprSimMemDefs
  venomMemDefs[qualified]

Theorem materialized_immutable_frame[local]:
  immutable_frame_mods func ce cx ee s /\
  exec_alloca inst s (n:bytes32) = OK u /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (dst,nb) /\
  z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
  z.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!src id b len. local_region (ce with ce_module := src) ee.scopes u id b len ==>
    local_region (ce with ce_module := src) ee.scopes s id b len) /\
  (!src id b len. local_region (ce with ce_module := src) ee.scopes z id b len ==>
    local_region (ce with ce_module := src) ee.scopes u id b len) /\
  (!off len. off+len <= dst \/ dst+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  immutable_frame_mods func ce cx ee z
Proof
  strip_tac >>
  `immutable_alloca_sep_mods func ce cx ee u` by
    (fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
     rpt strip_tac >> irule immutable_alloca_sep_exec_alloca >>
     qexistsl_tac [`inst`, `n`, `s`] >> simp[] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      `immutable_alloca_sep func (ce with ce_module := src) cx ee u` by metis_tac[] >>
      fs[immutable_alloca_sep_def] >>
      qpat_assum `ce.ce_is_ctor ==> !name tv v off. _` mp_tac >> simp[] >>
      disch_then (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac) >> simp[] >>
      strip_tac >> first_x_assum (qspecl_then [`inst`, `dst`, `nb`] mp_tac) >>
      simp[regions_disjoint_def]) >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`u`, `ee`] >> simp[] >> metis_tac[]
QED

Theorem materialized_local_robust[local]:
  val_wf tv v /\ val_footprint tv v <= len /\
  mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
  (!j. b <= j /\ j < b+len /\ j IN tf.t_mem ==> j IN tn.t_mem) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v b m) ==>
  !m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory tv v b m
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  qabbrev_tac `extra = tn.t_mem UNION (tf.t_mem DIFF {j | b <= j /\ j < b+len})` >>
  irule robust_val_in_memory_copy_transport >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `z.vs_memory`, `len`, `b`, `tn.t_mem`, `extra`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `extra`] >> rpt strip_tac >> decide_tac) >>
  fs[mem_agree_outside_def, Abbr `extra`] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `b <= i /\ i < b+len` >> gvs[] >> metis_tac[]
QED

Theorem materialized_linked_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func ce ee.scopes s /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    dst+nb <= b \/ b+len <= dst) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= dst \/ dst+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < dst \/ dst+nb <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) /\
  lo <= dst /\ stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf z
Proof
  strip_tac >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  fs[ghost_inv_at_mods_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
      rpt strip_tac >> `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      `local_region ce ee.scopes s name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      `dst+nb <= w2n w \/ w2n w+sz <= dst` by metis_tac[] >>
      `val_footprint entry.type entry.value <= sz` by
        (irule LESS_EQ_TRANS >> qexists_tac `type_memory_size entry.type` >> simp[val_footprint_le]) >>
      `mem_bytes_at (w2n w) sz z.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by
        (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >> decide_tac) >>
      `!j. w2n w <= j /\ j < w2n w+sz /\ j IN tf.t_mem ==> j IN tn.t_mem` by
        (qx_gen_tac `j` >> strip_tac >>
         qpat_assum `!j. j < dst \/ dst+nb <= j ==> _`
           (irule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[] >> decide_tac) >>
      irule materialized_local_robust >> simp[] >>
      qexistsl_tac [`sz`, `s`, `tf`, `tn`, `z`] >> simp[] >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME arg) ce Gf tf z` >> PairCases_on `arg` >>
      gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* The raw value's location is irrelevant to these expression-frame clauses. *)
Theorem materialized_expr_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel H ctx func ce cx ee z /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  (!aid p. FLOOKUP s.vs_allocas aid = SOME p ==> FLOOKUP z.vs_allocas aid = SOME p) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) nb b len) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    regions_disjoint (w2n w) nb b len) /\
  (!name b len. local_region ce ee.scopes z name b len ==>
    regions_disjoint (w2n w) nb b len) /\
  (!off len. off+len <= w2n w \/ w2n w+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  val_wf rt v /\ val_in_memory rt v (w2n w) z.vs_memory /\
  val_footprint rt v <= nb /\ eval_operand op z = SOME w ==>
  expr_post H ctx func ce cx e es sa sb s0 ee v op z
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
    regions_disjoint (w2n w) nb b len` by
    (rpt gen_tac >> disch_tac >> first_x_assum irule >> qexists_tac `name` >>
     irule local_region_frame_fwd >> qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
  `locals_kept ce es ee s0 z` by
    (irule copy_buffer_locals_kept_frame >> qexistsl_tac [`w2n w`, `s`, `nb`] >>
     fs[regions_disjoint_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 z` by
    (strip_tac >> irule pure_frame_buffer_tail >>
     qexistsl_tac [`w2n w`, `nb`, `inst`, `s`] >> fs[regions_disjoint_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name b k. local_region ce es.scopes s0 name b k ==> off + len <= b \/ b + k <= off) ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     `aid < sm.cs_next_id` by decide_tac >>
     `regions_disjoint (w2n w) nb off len` by metis_tac[] >>
     `mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
       (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
        fs[regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  rpt conj_tac
  >- (disj1_tac >> qexistsl_tac [`sm.cs_next_id`, `w2n w`, `nb`] >>
      fs[regions_disjoint_def] >> first_assum ACCEPT_TAC)
  >- (strip_tac >> disj1_tac >> qexistsl_tac [`sm.cs_next_id`, `w2n w`, `nb`] >>
      fs[regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem materialized_ghost_kept[local]:
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint dst nb b len) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
    regions_disjoint dst nb b len) /\
  (!j. j < dst \/ dst+nb <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) /\ lo <= dst ==>
  ghost_kept_at lo ce es sa Gi ti s0 Gf tf
Proof
  strip_tac >> irule unwrap_slot_copy_ghost_kept_at >>
  qexistsl_tac [`G`, `tn`] >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  (qpat_assum `!j. j < dst \/ dst+nb <= j ==> _`
    (irule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[]) >>
  FIRST [qpat_assum `!aid b len. aid < _ /\ FLOOKUP _ _ = _ ==> _` (drule_all_then mp_tac),
         qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _` (drule_then mp_tac),
         all_tac] >>
  simp[regions_disjoint_def] >> decide_tac
QED

(* Use the allocation actually run in the suffix; its site can be reused
   (e.g. across iterations). Only the suffix's write window changes bytes. *)
Theorem copy_materialized_rhs_post_mods:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var < sb.cs_next_var /\
  fn_inst_ids_distinct func /\ nb < dimword (:256) /\
  root = STRING #"%" (toString sm.cs_next_var) /\
  MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func) /\
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
  copy_static z = copy_static u /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= w2n w \/ w2n w+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n w \/ w2n w+nb <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  z.vs_data_section = s.vs_data_section /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  val_wf rt v /\ type_memory_size rt <= nb /\
  type_memory_bytes ce (lowered_value_type ce e) <= nb /\
  eval_operand (Var root) z = SOME w /\ ptr_covers Gf tf root z nb /\
  (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v (Var root) z /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf z /\
  ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
  ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
  ptr_buf_ok ce e (Var root) Gf z /\
  expr_store_bound cx (post_value_type ce e) v (Var root) z /\
  FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
  lo <= w2n w /\ w2n w + nb <= z.vs_alloca_next /\ not_fresh_at sb root /\
  wb_frame ce ee ee sm s z /\
  ghost_kept_at lo ce ee sm G tn s Gf tf /\
  (!x cap. not_fresh_at sm x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)
Proof
  strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
   inst.inst_outputs = [root] /\ inst.inst_operands = [Lit (n2w nb)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  `stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b)` by
    fs[vv_post_mods_def] >>
  `not_local_ptr ce ee.scopes root` by
    (qpat_assum `root = _` SUBST1_TAC >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (drule_at (Pat `exec_alloca _ _ _ = OK u`) stmt_state_rel_exec_alloca >>
     disch_then drule_all >> simp[]) >>
  `u.vs_memory = s.vs_memory /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
   (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s)` by
    ((drule_all actualAllocExecTheory.actual_literal_alloca_frame >> strip_tac >> simp[] >>
     rpt strip_tac >> first_x_assum (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, not_fresh_at_def] >> (gvs[eval_operand_def, not_fresh_at_def, actualAllocExecTheory.actual_literal_alloca_frame]))) >>
  drule copy_static_fields >> strip_tac >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry` by simp[] >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u` by metis_tac[] >>
  `!name b len. local_region ce ee.scopes u name b len <=> local_region ce ee.scopes s name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> metis_tac[]) >>
  `!name b len. local_region ce ee.scopes z name b len <=> local_region ce ee.scopes u name b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> metis_tac[]) >>
  `alloca_inv u /\ local_ptrs_rel func ce ee.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name b len. local_region ce ee.scopes u name b len ==> regions_disjoint (w2n w) nb b len` by
    (`MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
       fs[Abbr `inst`] >>
     drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`) unwrap_alloc_local_disjoint >>
     metis_tac[]) >>
  `!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) nb b len` by
    (rpt gen_tac >> strip_tac >> irule unwrap_alloc_old_disjoint >>
     qexistsl_tac [`sm.cs_next_id`, `aid`, `s`, `u`] >> simp[]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==> regions_disjoint (w2n w) nb b len` by
    (rpt gen_tac >> disch_tac >>
     `local_region ce ee.scopes s name b len` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
     metis_tac[]) >>
  `stmt_state_rel H ctx func ce cx ee z` by
    (irule copy_buffer_state_rel_frame >> qexistsl_tac [`w2n w`, `inst`, `u`, `sm`, `nb`] >>
     fs[regions_disjoint_def] >> conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next /\ stor_taint_ok_at D tn s` by
    fs[ghost_inv_at_mods_def] >>
  `allocas_from lo z` by
    (drule_all allocas_from_exec_alloca >> simp[allocas_from_def]) >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,nb)` by simp[] >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `w2n w + nb <= z.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> qpat_assum `!aid b sz. FLOOKUP u.vs_allocas aid = _ ==> _`
       (qspec_then `sm.cs_next_id` mp_tac) >> simp[ADD_COMM]) >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  `stor_taint_ok_at D tf z` by fs[stor_taint_ok_at_def] >>
  `immutable_frame_mods func ce cx ee z` by
    (irule materialized_immutable_frame >> qexistsl_tac [`w2n w`, `inst`, `n2w nb`, `nb`, `s`, `u`] >>
     fs[local_region_def] >> first_assum ACCEPT_TAC) >>
  `val_in_memory rt v (w2n w) z.vs_memory /\ val_footprint rt v <= nb` by
    (conj_tac
     >- (first_x_assum irule >> simp[mem_agree_outside_def]) >>
     drule val_footprint_le >> decide_tac) >>
  `ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
   ptr_buf_ok ce e (Var root) Gf z` by
    (drule_all unwrap_storage_pointer_posts >> simp[]) >>
  simp[expr_post_mods_def] >> rpt conj_tac
  >- (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) materialized_expr_post >>
      disch_then irule >> simp[] >> conj_tac >- (qexists_tac `inst` >> simp[]) >>
      fs[] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]])
  >- (irule materialized_linked_ghost >> simp[] >>
      qexistsl_tac [`G`, `w2n w`, `func`, `nb`, `s`, `sa`, `tn`] >>
      fs[regions_disjoint_def] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]])
  >- (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) materialized_ghost_kept >>
      disch_then irule >> simp[] >> qexistsl_tac [`w2n w`, `nb`] >>
      fs[] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]])
  >- (qpat_x_assum `root = _` SUBST_ALL_TAC >>
      simp[expr_store_bound_def] >> drule val_store_size_le >> decide_tac)
  >- (rw[not_fresh_at_def] >> irule emitHelperPropsTheory.fresh_var_distinct >> decide_tac)
  >- (irule unwrap_slot_copy_wb_frame >> simp[] >>
      qexistsl_tac [`nb`, `w2n w`] >>
      fs[regions_disjoint_def] >> rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> metis_tac[])
      >- (rpt gen_tac >> strip_tac >> metis_tac[]) >> first_assum ACCEPT_TAC)
  >- (irule materialized_ghost_kept >> qexistsl_tac [`G`, `w2n w`, `nb`, `tn`] >>
      fs[wordArgsPtrTheory.ghost_kept_at_refl] >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
  fs[ptr_covers_def] >> metis_tac[]
QED
