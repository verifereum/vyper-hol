(* The joint encoder body endpoint, before length/method-id packaging. *)
Theory bodyFullAbiEncodeSuffix
Ancestors
  abiEncoderWindowJoint abiEncoderWindowContract bodyPtrDefs ghostObservationPtr abiDecodeStaticProps
  localPtrsProps loweringStateRelDefs valueEncodingProps valueEncodingProofs abiAllocationHistory
  exprSimAbiEncodeExecFrame abiEncoderRegisteredEffect ptrDiscipline bodyFullPathHistory
  exprSimProps externalReturnEncoderSites arithmetic finite_map pred_set words list

(* Protected caller bytes lie below the entry frontier. Reused scratch
   sites must miss them; new scratch sites miss them by allocation growth. *)
Theorem abi_encode_protected_bytes[local]:
  window_strong_result ctx func st en out at av d s t /\
  (!i. (i < d \/ d + LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!i. i IN P ==> i < s.vs_alloca_next /\
    (i < d \/ d + LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)) ==>
  !i. i IN P ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >>
  drule window_strong_result_effect >> strip_tac >>
  drule window_strong_result_growth >> strip_tac >>
  `!id r. FLOOKUP s.vs_allocas id = SOME r ==> FLOOKUP t.vs_allocas id = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  gen_tac >> disch_tac >>
  `i < s.vs_alloca_next /\ (i < d \/ d+LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)` by metis_tac[] >>
  `!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i` by
    (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
     >- (fs[window_alloca_growth_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     rename1 `SOME r` >> `FLOOKUP t.vs_allocas id = SOME r` by metis_tac[] >>
     gvs[] >> metis_tac[]) >>
  (conj_tac >- (fs[abi_encoder_registered_effect_def] >> metis_tac[]) >>
   qpat_x_assum `!i. _ ==> (i IN tn'.t_mem <=> i IN tn.t_mem)`
     (qspec_then `i` mp_tac) >> asm_rewrite_tac[])
QED

Theorem abi_encode_caller_inv_at[local]:
  ghost_inv_at D lo ret ce cx es G tn s /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce st /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p w. not_fresh_at st p /\ lookup_var p s = SOME w ==> lookup_var p t = SOME w) /\
  (!p. not_fresh_at st p ==> FLOOKUP G' p = FLOOKUP G p /\
    op_taint tn' (Var p) = op_taint tn (Var p)) /\
  (!i. i IN P ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!name b sz i. local_region ce es.scopes s name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!i. i < lo ==> i IN P) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo ret ce cx es G' tn' t
Proof
  strip_tac >>
  `!p sz. not_fresh_at st p /\ ptr_covers G tn p s sz ==> ptr_covers G' tn' p t sz` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "locals" >>
  conj_tac
  >- (Cases_on `ret` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[ghost_inv_at_def, return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac >- gvs[ghost_inv_at_def, stor_taint_ok_at_def] >>
  conj_tac
  >- (`mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
        (irule mem_bytes_at_bytewise >> simp[] >> metis_tac[]) >>
      fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac >- (fs[ghost_inv_at_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[]
QED

Resume abi_encode_caller_inv_at[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at st p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ptr_covers G tn p s sz` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  `?v. lookup_var p s = SOME v /\ val_wf entry.type entry.value /\
    val_footprint entry.type entry.value <= sz /\
    local_region ce es.scopes s name (w2n v) sz` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
     drule val_footprint_le >> strip_tac >>
     simp[local_region_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `w = v` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  irule robust_val_in_memory_exterior_no_new_taint >> conj_tac >- simp[] >>
  qexistsl_tac [`COMPL P`, `s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >>
  simp[] >> conj_tac
  >- (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[ghost_inv_at_def] >> strip_tac >>
      qpat_x_assum `!name entry p sz. _` drule_all >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!i. i IN P ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!name b sz i. _` irule >>
  qexistsl_tac [`w2n v`, `name`, `sz`] >> simp[] >> decide_tac
QED

Finalise abi_encode_caller_inv_at

(* P consists of live caller bytes, including kept origin allocations and
   the immutable prefix. The destination buffer is fresh, hence outside P.
   Only scratch sites already present at entry need explicit exclusion. *)
Theorem abi_encode_suffix_full:
  compile_abi_encode_to_buf (Var dp) src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dp) s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn (Var dp) = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\ not_fresh_at st dp /\
  ptr_covers G tn dp s dstcap /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (enc at av) ==> ptr_covers G tn dp s (LENGTH (enc at av))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce st /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> not_fresh_at st p) /\
  (!i. i IN P ==> i < s.vs_alloca_next /\
    (i < d \/ d + LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)) /\
  (!name b sz i. local_region ce es.scopes s name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!name b sz i. local_region ce es.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz ==> i IN P) /\
  (!i. i < lo ==> i IN P) ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      mem_bytes_at d (LENGTH (enc at av)) mem = enc at av) /\
    ptr_covers G' tn' dp t dstcap /\
    alloca_inv t /\ alloca_room ctx func t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (abi_alloca_history (fn_insts func) s ==>
      abi_alloca_history (fn_insts func) t) /\
    (alloca_history func s ==> alloca_history func t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. i IN P ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G' tn' /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn') /\
      (ghost_inv_at D lo ret ce cx es G tn s ==>
       ghost_inv_at D lo ret ce cx es G' tn' t)
Proof
  strip_tac >>
  `!x. src = Var x \/ Var dp = Var x ==> not_fresh_at st x` by (simp[] >> metis_tac[]) >>
  `0 < LENGTH (enc at av) ==> ?p. Var dp = Var p /\
    ptr_covers G tn p s (LENGTH (enc at av))` by metis_tac[] >>
  drule_all compile_abi_encode_to_buf_window_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  drule abi_encoder_window_result_resources >> strip_tac >>
  drule abi_encoder_window_result_control >> strip_tac >>
  `!p w. not_fresh_at st p /\ lookup_var p s = SOME w ==> lookup_var p t = SOME w` by
    metis_tac[abi_encoder_window_result_vars] >>
  `!i. i IN P ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (match_mp_tac abi_encode_protected_bytes >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "bytes" >>
  conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
  conj_asm1_tac >- suspend "allocas" >>
  conj_asm1_tac >- suspend "frontier" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "ordinary_history" >>
  conj_tac >- suspend "kept" >>
  gen_tac >> asm_rewrite_tac[] >> strip_tac >> suspend "inv"
QED

Resume abi_encode_suffix_full[bytes]:
  rpt strip_tac >>
  `mem_bytes_at d (LENGTH (enc at av)) mem =
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory` suffices_by simp[] >>
  irule mem_bytes_at_bytewise >> simp[] >>
  fs[mem_agree_outside_def] >> metis_tac[]
QED
Resume abi_encode_suffix_full[allocas]:
  drule window_strong_result_growth >>
  simp[window_alloca_growth_def, allocas_from_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas aid`
  >- metis_tac[LESS_EQ_TRANS] >>
  rename1 `SOME r` >>
  drule window_strong_result_effect >> strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  metis_tac[allocas_from_def, optionTheory.SOME_11]
QED
Resume abi_encode_suffix_full[frontier]:
  drule window_strong_result_growth >> simp[window_alloca_growth_def]
QED
Resume abi_encode_suffix_full[history]:
  disch_tac >>
  drule window_strong_result_effect >> strip_tac >>
  pure_rewrite_tac[abi_alloca_history_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `id IN window_alloca_sites func (frag_ids st en)`
  >- (`sz = 32` by metis_tac[window_strong_result_sizes] >>
      qpat_x_assum `id IN window_alloca_sites _ _` mp_tac >>
      simp_tac (srw_ss()) [window_alloca_sites_def] >> strip_tac >>
      `inst.inst_operands = [Lit 32w]` by
        metis_tac[encoder_function_alloca_shape] >>
      qexistsl_tac [`inst`, `32w`] >>
      asm_rewrite_tac[] >>
      simp_tac std_ss [wordsTheory.w2n_n2w, dimword_def,
        fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  `FLOOKUP s.vs_allocas id = SOME (off,sz)` by
    (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_encoder_registered_effect_def] >> metis_tac[]) >>
  qpat_x_assum `abi_alloca_history _ _` mp_tac >>
  pure_rewrite_tac[abi_alloca_history_def] >> metis_tac[]
QED
Resume abi_encode_suffix_full[ordinary_history]:
  strip_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `ARB` assume_tac) >>
  drule_all body_full_path_alloca_history >> simp[]
QED
Resume abi_encode_suffix_full[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
  pure_rewrite_tac[ghost_kept_at_def] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED
Resume abi_encode_suffix_full[inv]:
  irule abi_encode_caller_inv_at >> asm_rewrite_tac[] >>
  qexistsl_tac [`G`, `P`, `func`, `s`, `st`, `tn`] >>
  asm_rewrite_tac[] >>
  drule window_strong_result_effect >>
  fs[abi_encoder_registered_effect_def, abi_encode_exec_frame_def]
QED
Finalise abi_encode_suffix_full
