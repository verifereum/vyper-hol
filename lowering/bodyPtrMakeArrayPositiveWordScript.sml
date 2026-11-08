(* Scalar store continuation on its actual fetched MSTORE edge. *)
Theory bodyPtrMakeArrayPositiveWord
Ancestors
  bodyPtrMakeArrayPositiveFrame bodyPtrMakeArrayWordStore
  bodyPtrMakeArrayConsInvariant annAssignPtrScratch bodyPtrDefs
  bodyPtrMakeArrayStoreFrame calldataReconstruction venomState
  typedCopyPtr loweringPosts pred_set bodyPtrMakeArrayPrimitiveInstall context

Theorem literal_word_store_frames:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  w2n a = addr+off /\ off+32 <= capacity /\
  local_ptrs_reserved ce sa /\ ~ce.ce_is_ctor /\
  z = (mstore (w2n a) w s) with vs_inst_idx := idx /\
  tm = tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} ==>
  ghost_inv d ce cx es G tm z /\ ghost_kept ce es fr Gf tnf sf G tm /\
  stmt_state_rel ctx func ce cx es z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_loop_store_ghost >> strip_tac >>
  `!i. ~(w2n a <= i /\ i < w2n a+32) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (gvs[] >> rpt strip_tac >>
     mp_tac (Q.SPECL [`s`, `addr+off`, `w`] mstore_memory_frame) >>
     simp[mem_agree_outside_def] >> metis_tac[]) >>
  `!name p n i. local_region ce es.scopes s name p n /\ p <= i /\ i < p+n ==>
    ~(w2n a <= i /\ i < w2n a+32)` by
    (gvs[literal_loop_frame_def] >> rpt strip_tac >>
     `addr+capacity <= p \/ n+p <= addr` by metis_tac[] >> decide_tac) >>
  `ghost_inv d ce cx es G tm z` by
    (gvs[] >> simp[mstore_def] >> irule annassign_ghost_exterior_ptr >>
     reverse conj_tac >- metis_tac[literal_loop_frame_runtime] >>
     qexists `{i | addr+off <= i /\ i < addr+(off+32)}` >>
     gvs[mstore_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ghost_kept ce es fr Gf tnf sf G tm` by
    (drule_all literal_loop_store_exterior >> strip_tac >>
     irule annassign_ghost_kept_exterior_ptr >>
     qexistsl [`tn`, `{i | w2n a <= i /\ i < w2n a+32}`] >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[] >> irule literal_store_runtime_frame >> simp[] >>
  qexistsl [`addr+off`, `32`, `s`, `sa`] >> simp[] >>
  gvs[mstore_def, lookup_var_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[literal_loop_frame_runtime] >>
  simp[listTheory.LENGTH_TAKE] >> IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem literal_word_loop_store:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  literal_prefix_ok cells tn s /\
  lookup_var dst s = SOME a /\ w2n a = addr+off /\ ptr_covers G tn dst s 32 /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ val_footprint tv v <= 32 /\ off+32 <= capacity /\
  lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sa.cs_current_insts) = SOME (mk_inst id MSTORE [Var dst;op] []) /\
  sb.cs_current_bb = sa.cs_current_bb /\ LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce fr /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor ==>
  ?z tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es sb G tm z (cells ++ [(tv,v,addr+off,32)]) (off+32) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,32)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule literal_loop_frame_runtime >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id MSTORE [Var dst;op] [])` by simp[] >>
  drule_all make_array_word_store_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z)` >>
  qpat_x_assum `H = G` SUBST_ALL_TAC >>
  `tm = tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    simp[ptrDisciplineTheory.taint_component_equality] >>
  drule_all literal_word_store_frames >> strip_tac >>
  `!x. lookup_var x z = lookup_var x s` by simp[mstore_def, lookup_var_def] >>
  `!i. ~(addr+off <= i /\ i < addr+off+32) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)` by (gvs[mem_agree_outside_def] >> metis_tac[]) >>
  `FLOOKUP G root = SOME (addr,capacity) /\ ptr_covers G tm root z capacity` by
    metis_tac[literal_loop_frame_allocation] >>
  `z.vs_allocas = s.vs_allocas /\ ~z.vs_halted /\
   z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[mstore_def] >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb G tm z cells off` by
    (irule literal_loop_store_endpoint >> simp[] >>
     qexistsl [`G`, `32`, `s`, `sa`, `tn`] >> gvs[] >> metis_tac[]) >>
  `literal_prefix_ok cells tm z` by
    (irule literal_prefix_store_frame >> qexistsl [`addr+off`, `32`, `s`, `tn`] >> simp[] >>
     gvs[literal_loop_frame_def, listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb G tm z (cells ++ [(tv,v,addr+off,32)]) (off+32)` by
    (irule literal_loop_frame_advance >> simp[]) >>
  qexistsl [`z`, `tm`] >> gvs[literal_prefix_cell] >>
  metis_tac[calldata_word_representation]
QED

Theorem literal_scalar_loop_store:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  literal_prefix_ok cells tn s /\
  lookup_var dst s = SOME a /\ w2n a = addr+off /\ ptr_covers G tn dst s 32 /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ val_footprint tv v <= 32 /\ off+32 <= capacity /\
  compile_store_memory ce op (Var dst) ty sty sa = ((),sb) /\ fn_has_code sa sb func /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce fr /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor ==>
  ?z tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es sb G tm z (cells ++ [(tv,v,addr+off,32)]) (off+32) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,32)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emit_void MSTORE [Var dst;op] sa = ((),sb)` by gvs[compile_store_memory_def] >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  drule_all literal_word_loop_store >> simp[]
QED
