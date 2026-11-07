(* Runtime single-slot materialization. Allocation coverage does not imply
   initialized bytes; cleanliness is established only after the store. *)
Theory bodyPtrStructLitSingleSlotMaterialize
Ancestors
  bodyPtrStructLitAlloc bodyPtrStructLitNonmemoryRead
  bodyPtrStructLitFieldStore allocationPtr context emitHelper compileEnv
  contextCodegenRel exprLoweringProps loweringPosts list fragExec
  venomExecSemantics venomInst venomState fragGasPathPtr ptrDiscipline finite_map
  bodyPtrDefs bodyPtrStructLitNonmemoryLoad typedCopyPtr decoderGhostFramePtr
  robustCopyTransportPtr pred_set exprSimProps

Theorem single_slot_materialize_code:
  compile_ensure_in_memory src (slot_loc tr) 32 1 F imm sa = (buf,sb) ==>
  ?out tmp.
    buf = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [out];
       mk_inst (sa.cs_next_id + 1) (if tr then TLOAD else SLOAD) [src] [tmp];
       mk_inst (sa.cs_next_id + 2) MSTORE [Var out; Var tmp] []] /\
    sb.cs_next_id = sa.cs_next_id + 3 /\
    sb.cs_next_var = sa.cs_next_var + 2 /\
    ~not_fresh_at sa out /\ ~not_fresh_at sa tmp /\ out <> tmp
Proof
  Cases_on `tr` >>
  simp[slot_loc_def, compile_ensure_in_memory_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_return_def,
    fresh_id_def, comp_ignore_bind_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[not_fresh_at_def, APPEND_ASSOC] >>
  qexists `"%" ++ toString (sa.cs_next_var + 1)` >>
  simp[ASCIInumbersTheory.toString_inj] >>
  qexists `sa.cs_next_var + 1` >> simp[]
QED

Theorem single_slot_materialize_instructions:
  compile_ensure_in_memory src (slot_loc tr) 32 1 F imm sa = (buf,sb) /\
  fn_has_code sa sb fn ==>
  ?out tmp bb.
    buf = Var out /\ out <> tmp /\
    ~not_fresh_at sa out /\ ~not_fresh_at sa tmp /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [out]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id + 1) (if tr then TLOAD else SLOAD) [src] [tmp]) /\
    get_instruction bb (SUC (SUC (LENGTH sa.cs_current_insts))) =
      SOME (mk_inst (sa.cs_next_id + 2) MSTORE [Var out; Var tmp] [])
Proof
  strip_tac >> drule single_slot_materialize_code >> strip_tac >> gvs[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl [`tmp`, `bb`] >> simp[] >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac >- (first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  first_x_assum (qspec_then `2` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

Theorem fresh_buffer_counted:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  u = update_var out (n2w s.vs_alloca_next)
    (s with <| vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,n));
               vs_alloca_next := s.vs_alloca_next + n |>) /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn /\
  s1 = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
  ptr_covers G1 tn1 out s1 n /\
  (!r sz. r <> out /\ ptr_covers G tn r s sz ==> ptr_covers G1 tn1 r s1 sz) /\
  s1.vs_memory = s.vs_memory /\ s1.vs_accounts = s.vs_accounts /\
  s1.vs_transient = s.vs_transient /\ s1.vs_call_ctx = s.vs_call_ctx /\
  tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u` by
    (qpat_x_assum `u = _` SUBST_ALL_TAC >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_alloca_def, wordsTheory.w2n_n2w]) >>
  `~u.vs_halted` by (qpat_x_assum `u = _` SUBST_ALL_TAC >> simp[update_var_def]) >>
  conj_tac
  >- (drule_all structlit_alloca_counted_edge >>
      disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >>
      qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
      qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
      qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
      strip_tac >> drule (cj 2 gas_path_ptr_rules) >>
      simp[gas_path_ptr_rules, update_var_def]) >>
  drule_all fresh_alloca_ptr_covers >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] assume_tac) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      op_taint_def] >> rpt strip_tac >> gvs[]
QED

Theorem slot_load_store_inputs:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME b /\ dst <> tmp /\
  opc = (if tr then TLOAD else SLOAD) /\
  w = (if tr then tload a s else sload a s) /\
  u = update_var tmp w s /\
  G1 = step_prov PG G (mk_inst id opc [src] [tmp]) u /\
  tn1 = step_taint (mk_inst id opc [src] [tmp]) s u tn /\
  s1 = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK u /\
  ptr_covers G1 tn1 dst s1 32 /\ lookup_var dst s1 = SOME b /\
  eval_operand (Var tmp) s1 = SOME w /\ op_taint tn1 (Var tmp) = {} /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = SUC s.vs_inst_idx /\
  s1.vs_halted = s.vs_halted
Proof
  strip_tac >>
  qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  conj_tac
  >- (Cases_on `tr` >> gvs[] >>
      simp[Once step_inst_base_def, mk_inst_def, exec_read1_def]) >>
  `MEM opc [SLOAD; TLOAD; DLOAD]` by (Cases_on `tr` >> simp[]) >>
  `op_taint (step_taint (mk_inst id opc [src] [tmp]) s
     (update_var tmp w s) tn) (Var tmp) = {}` by
    (irule nonmemory_word_load_clean >>
     reverse conj_tac >- (Cases_on `tr` >> simp[]) >>
     qexists `a` >> Cases_on `tr` >> gvs[]) >>
  simp[ptr_covers_def, step_prov_other_output, step_taint_other_output,
       mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  gvs[ptr_covers_def, lookup_var_def]
QED

Theorem slot_load_store_counted:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME b /\ dst <> tmp /\
  opc = (if tr then TLOAD else SLOAD) /\
  w = (if tr then tload a s else sload a s) /\
  u = update_var tmp w s /\
  G1 = step_prov PG G (mk_inst id opc [src] [tmp]) u /\
  tn1 = step_taint (mk_inst id opc [src] [tmp]) s u tn /\
  s1 = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1
    (step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) s1
      (mstore (w2n b) w s1) tn1)
    (OK (mstore (w2n b) w s1 with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  strip_tac >> drule_all slot_load_store_inputs >> strip_tac >>
  `MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD]` by
    (Cases_on `tr` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
     irule nonmemory_word_load_counted >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G1
    (step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) s1
      (mstore (w2n b) w s1) tn1)
    (OK (mstore (w2n b) w s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule covered_word_store_counted >> simp[] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem robust_below_frontier_taint:
  val_wf tv v /\ p + val_footprint tv v <= frontier /\
  (!m. mem_agree_outside taints mem m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside
    (taints UNION {i | frontier <= i /\ i < frontier + n}) mem m ==>
    val_in_memory tv v p m
Proof
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >> qexistsl [`mem`, `mem`, `taints`,
    `taints UNION {i | frontier <= i /\ i < frontier + n}`,
    `{i | frontier <= i /\ i < frontier + n}`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED

Theorem live_local_fresh_taint_robust:
  local_ptrs_rel fn cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  !m. mem_agree_outside
    (tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n})
    s.vs_memory m ==> val_in_memory entry.type entry.value (w2n w) m
Proof
  strip_tac >>
  `val_wf entry.type entry.value /\
   w2n w + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (gvs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  rpt strip_tac >> irule robust_below_frontier_taint >> simp[] >>
  qexistsl [`s.vs_alloca_next`, `s.vs_memory`, `n`, `tn.t_mem`] >>
  simp[] >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem fresh_buffer_ghost_inv:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  s1 = (update_var out w (s with
    <| vs_allocas := allocas; vs_alloca_next := frontier |>)) /\
  G1 = G |+ (out,site) /\
  tn1 = (tn with <| t_mem := tn.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n};
    t_var := tn.t_var |+ (out,{}) |>) ==>
  ghost_inv d cenv cx es G1 tn1 s1
Proof
  strip_tac >>
  `!p. p <> out ==> lookup_var p s1 = lookup_var p s /\
      FLOOKUP G1 p = FLOOKUP G p /\
      op_taint tn1 (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> simp[lookup_var_def, update_var_def,
      op_taint_def, FLOOKUP_UPDATE]) >>
  `s1.vs_memory = s.vs_memory` by simp[update_var_def] >>
  rewrite_tac[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  conj_tac >- suspend "return_buffer" >>
  conj_tac >- (rpt strip_tac >> `x <> out` by metis_tac[] >>
    gvs[ghost_inv_def] >> metis_tac[]) >>
  gvs[ghost_inv_def, stor_taint_ok_def, update_var_def]
QED

Resume fresh_buffer_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >> `p <> out` by metis_tac[] >>
  `ptr_covers G tn p s sz /\
   (!w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem)` by
    (qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_inv_def] >> strip_tac >>
     qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
       drule_all >> simp[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `lookup_var p s = SOME w'` by metis_tac[] >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`) live_local_fresh_taint_robust >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then (qspec_then `n` mp_tac) >>
  gvs[] >> metis_tac[]
QED

Resume fresh_buffer_ghost_inv[return_buffer]:
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[ghost_inv_def, return_buf_ptr_def] >>
  rename1 `cenv.ce_return_buf = SOME (PtrVar (Var r) sz)` >>
  `r <> out` by metis_tac[] >>
  gvs[ptr_covers_def, lookup_var_def, update_var_def,
      op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Finalise fresh_buffer_ghost_inv

Theorem ghost_kept_taint_above_frontier:
  ghost_kept cenv es sa G0 tn0 initial G tn /\
  (!aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==>
    b + sz <= frontier) /\
  (!name b sz. local_region cenv es.scopes initial name b sz ==>
    b + sz <= frontier) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  (!i. i < frontier /\ i IN tn1.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept cenv es sa G0 tn0 initial G1 tn1
Proof
  strip_tac >> rewrite_tac[ghost_kept_def] >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> `off + sz <= frontier` by metis_tac[] >>
      `i < frontier` by decide_tac >>
      `i IN tn.t_mem` by metis_tac[] >> metis_tac[]) >>
  rpt strip_tac >> `b + sz <= frontier` by metis_tac[] >>
  `i < frontier` by decide_tac >>
  `i IN tn.t_mem` by metis_tac[] >> metis_tac[]
QED

Theorem fresh_word_store_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  (!name entry p sz b. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b ==>
    val_wf entry.type entry.value /\
    (w2n b + val_footprint entry.type entry.value <= w2n a \/
     w2n a + 32 <= w2n b)) /\
  tn1 = step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn ==>
  ghost_inv d cenv cx es G tn1
    (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `G`, `id`] strip_assume_tac) >>
  `tn1.t_var = tn.t_var /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\
   tn1.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    metis_tac[] >>
  `tn1.t_imm = tn.t_imm` by
    (simp[step_taint_def, mk_inst_def, set_var_taint_def,
      store_taint_def, adopt_reset_def, imm_taint_def]) >>
  qpat_x_assum `tn1 = _` kall_tac >>
  qpat_x_assum `step_prov _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(step_taint _ _ _ _).t_var = _` kall_tac >>
  qpat_x_assum `(step_taint _ _ _ _).t_stor = _` kall_tac >>
  qpat_x_assum `(step_taint _ _ _ _).t_trans = _` kall_tac >>
  qpat_x_assum `(step_taint _ _ _ _).t_mem = _` kall_tac >>
  `!p sz. ptr_covers G tn1 p
    (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) sz <=>
    ptr_covers G tn p s sz` by
    simp[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def] >>
  rewrite_tac[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[ghost_inv_def, return_buf_ptr_def,
        mstore_def, lookup_var_def] >> metis_tac[]) >>
  gvs[ghost_inv_def, stor_taint_ok_def, op_taint_def, mstore_def]
QED

Resume fresh_word_store_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s sz /\
   (!b mem. lookup_var p s = SOME b /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n b) mem)` by
    (qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_inv_def] >> strip_tac >>
     qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
       drule_all >> simp[]) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  `lookup_var p s = SOME w'` by gvs[lookup_var_def, mstore_def] >>
  `val_wf entry.type entry.value /\
    (w2n w' + val_footprint entry.type entry.value <= w2n a \/
     w2n a + 32 <= w2n w')` by metis_tac[] >>
  irule word_store_robust_exterior >> simp[] >>
  qexistsl [`w2n a`, `s`, `tn.t_mem`, `w`] >> simp[] >>
  gvs[mstore_def]
QED

Finalise fresh_word_store_ghost_inv
