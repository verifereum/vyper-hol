(* From the physical setup endpoint through the encoder and length store. *)
Theory bodyFullAbiEncodeReadyFinish
Ancestors
  bodyFullAbiEncodeSuffix bodyFullAbiEncodeFinish exprSimAbiEncodeSemantic
  abiEncodeVarFlow freshWrites representationCleanPtr reasonCopySourcePtr
  exprPtrUnwrapFrames tupleMemoryFrame wordArgsPtr fragGasOriginPtrLoop
  abiEncoderWindowContract typedMemoryCopy localPtrsProps abiAllocationHistory
  bodyPtrDefs loweringStateRelDefs arithmetic finite_map pred_set words list

(* Only the selector bytes, not the whole setup MSTORE word, belong to P. *)
Theorem abi_encode_ready_finish_origin_split:
  compile_abi_encode_to_buf (Var dp) src ei st = (out,en) /\
  abi_builtin_encode_finish (Var root) out (LENGTH selector) en = ((),fin) /\
  fn_has_code st en func /\ fn_has_code en fin func /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dp) s = SOME (n2w (p+32+LENGTH selector)) /\
  op_taint tn src = {} /\ op_taint tn (Var dp) = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\ not_fresh_at st dp /\
  ptr_covers G tn dp s dstcap /\
  fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap)
      (p+32+LENGTH selector,LENGTH (enc at av)) /\
    ?x. src = Var x /\ ptr_covers G tn x s cap) /\
  p+32+LENGTH selector+LENGTH (enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (enc at av) ==> ptr_covers G tn dp s (LENGTH (enc at av))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (p+32+LENGTH selector,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_ptrs_rel func ce ee.scopes s /\ local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x. not_fresh_at sa x ==> not_fresh_at st x) /\
  (!i. i IN P ==> i < s.vs_alloca_next /\
    (i < p+32+LENGTH selector \/ p+32+LENGTH selector+LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)) /\
  (!name b sz i. local_region ce ee.scopes s name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!name b sz i. local_region ce es.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz ==> i IN P) /\
  (!i. i < lo ==> i IN P) /\
  lookup_var root s = SOME (n2w p) /\ not_fresh_at st root /\
  p < dimword(:256) /\ lo <= p /\ 32 <= N /\ ptr_covers G tn root s N /\
  FLOOKUP s.vs_allocas site = SOME (p,N) /\
  LENGTH (enc at av)+LENGTH selector < dimword(:256) /\
  (!name b sz. local_region ce ee.scopes s name b sz ==>
    loweringStateRelDefs$regions_disjoint p 32 b sz) /\
  (!i. p+32 <= i /\ i < p+32+LENGTH selector ==> i IN P) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_bytes_at (p+32) (LENGTH selector) mem = selector) ==>
  ?t Gf tnf u Gu tnu.
    ((!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tnu) [] (OK t,Gf,tnf)) /\
     window_strong_result ctx func st en out at av (p+32+LENGTH selector) s u /\
     abi_encoder_registered_effect {} [(p,32)] u t /\
     t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
     (!op. (!x. op = Var x ==> not_fresh_at en x) ==>
       eval_operand op t = eval_operand op u)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = fin.cs_current_bb /\
    t.vs_inst_idx = LENGTH fin.cs_current_insts /\
    lookup_var root t = SOME (n2w p) /\ ptr_covers Gf tnf root t N /\
    FLOOKUP t.vs_allocas site = SOME (p,N) /\
    mload p t = n2w (LENGTH (enc at av)+LENGTH selector) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (LENGTH (enc at av)+LENGTH selector) /\
      mem_bytes_at (p+32) (LENGTH selector) mem = selector /\
      mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) mem = enc at av) /\
    alloca_inv t /\ alloca_room ctx func t /\ allocas_from lo t /\
    (alloca_history func s ==> alloca_history func t) /\
    (abi_alloca_history (fn_insts func) s ==> abi_alloca_history (fn_insts func) t) /\
    window_alloca_growth s t /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
      [(p+32+LENGTH selector,LENGTH (enc at av));(p,32)] s t /\
    abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!i. i IN P /\ (i < p \/ p+32 <= i) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf /\
    !D. ghost_inv_at D lo ret ce cx ee G tn s ==> ghost_inv_at D lo ret ce cx ee Gf tnf t
Proof
  strip_tac >>
  `!n b sz. local_region ce ee.scopes s0 n b sz <=> local_region ce es.scopes s0 n b sz` by
    metis_tac[local_region_scopes_domain] >>
  `ghost_kept_at lo ce ee sa G0 tn0 s0 G tn` by
    (qpat_x_assum `ghost_kept_at lo ce es _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >>
     qpat_assum `!n b sz. local_region ce ee.scopes s0 n b sz <=> _`
       (fn th => pure_rewrite_tac[th]) >> simp_tac bool_ss []) >>
  `(!name b sz i. local_region ce ee.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
   (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b sz'. local_region ce ee.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
     off <= i /\ i < off+sz ==> i IN P)` by
    (qpat_assum `!n b sz. local_region ce ee.scopes s0 n b sz <=> _`
       (fn th => pure_rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all abi_encode_suffix_full >>
  disch_then (qspecl_then [`ret`,`explicit`,`cx`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))) >>
  drule_then assume_tac window_strong_result_public >>
  drule_then assume_tac window_strong_result_effect >>
  drule_then assume_tac window_strong_result_growth >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w` by
    (drule abi_encoder_window_result_vars >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at en x` by
    metis_tac[compile_abi_encode_next_var,freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var root u = SOME (n2w p) /\ not_fresh_at en root` by metis_tac[] >>
  `ptr_covers Gu tnu root u N` by
    (irule (iffRL copy_ptr_covers_transport) >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `ptr_covers Gu tnu root u 32` by metis_tac[ptr_covers_mono] >>
  `p+32 <= u.vs_alloca_next` by
    (irule window_alloca_growth_frontier >> goal_assum (drule_at Any) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `abi_encode_exec_frame func s u` (fn frame =>
       qpat_assum `alloca_inv u` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _` (fn bound =>
           mp_tac (MATCH_MP abiEncoderWindowJointPhasesTheory.window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound]))))) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all abi_encode_finish_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))) >>
  `abi_encoder_registered_effect {} [(p,32)] u t` by
    (qpat_assum `typed_copy_state_frame en p 32 u t` mp_tac >>
     simp[NoAsms, typed_copy_state_frame_def, typed_copy_frame_def,
       abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def,
       venomStateTheory.venom_state_component_equality] >>
     rpt strip_tac >>
     `a+1 <= p \/ p+32 <= a` by decide_tac >> metis_tac[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at en x) ==>
     eval_operand op t = eval_operand op u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!op. _ ==> eval_operand op t = eval_operand op u /\ _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`,`u`,`Gu`,`tnu`] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >-
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> metis_tac[]) >>
  `lookup_var root t = SOME (n2w p)` by
    (rewrite_tac[GSYM (cj 2 venomStateTheory.eval_operand_def)] >> first_assum ACCEPT_TAC) >>
  `ptr_covers Gf tnf root t N` by metis_tac[] >>
  `FLOOKUP u.vs_allocas site = SOME (p,N)` by
    metis_tac[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated] >>
  `!a n. a+n <= p \/ p+32 <= a ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n u.vs_memory` by
    (qpat_assum `typed_copy_state_frame en p 32 u t` mp_tac >>
     rewrite_tac[typed_copy_state_frame_def,typed_copy_frame_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "bytes" >>
  conj_tac >- metis_tac[alloca_inv_fields] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.alloca_room_fields] >>
  conj_tac >-
    (asm_rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[abi_alloca_history_frame] >>
  conj_tac >-
    (asm_rewrite_tac[window_alloca_growth_def] >>
     qpat_assum `window_alloca_growth s u` (ACCEPT_TAC o REWRITE_RULE[window_alloca_growth_def])) >>
  conj_tac >- suspend "registered" >>
  conj_tac >- suspend "exec_frame" >>
  conj_tac >- suspend "labels" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "protected" >>
  simp[] >>
  conj_tac >- suspend "kept" >>
  suspend "inv"
QED

Resume abi_encode_ready_finish_origin_split[bytes]:
  gen_tac >> strip_tac >>
  conj_tac >- metis_tac[] >>
  `mem_bytes_at (p+32) (LENGTH selector) s.vs_memory = selector` by
    (qpat_assum `!mem. _ ==> mem_bytes_at (p+32) (LENGTH selector) mem = selector`
       (qspec_then `s.vs_memory` mp_tac) >>
     rewrite_tac[mem_agree_outside_def]) >>
  `!i. p+32 <= i /\ i < p+32+LENGTH selector ==> i NOTIN tn.t_mem` by
    (qpat_assum `!mem. _ ==> mem_bytes_at (p+32) (LENGTH selector) mem = selector`
       (mp_then Any ACCEPT_TAC robust_mem_bytes_at_clean)) >>
  `mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) u.vs_memory = enc at av` by
    (qpat_assum `!mem. _ ==> mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) mem = enc at av`
       (qspec_then `u.vs_memory` mp_tac) >>
     rewrite_tac[mem_agree_outside_def]) >>
  `!i. p+32+LENGTH selector <= i /\ i < p+32+LENGTH selector+LENGTH (enc at av) ==>
    i NOTIN tnu.t_mem` by
    (qpat_assum `!mem. _ ==> mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) mem = enc at av`
       (mp_then Any ACCEPT_TAC robust_mem_bytes_at_clean)) >>
  qpat_x_assum `mem_agree_outside _ t.vs_memory mem`
    (STRIP_ASSUME_TAC o REWRITE_RULE[mem_agree_outside_def]) >>
  conj_tac
  >- (`mem_bytes_at (p+32) (LENGTH selector) mem =
        mem_bytes_at (p+32) (LENGTH selector) s.vs_memory` suffices_by simp[] >>
      irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
      rpt strip_tac >>
      `i IN P /\ i NOTIN tn.t_mem` by metis_tac[] >>
      `i NOTIN tnu.t_mem` by metis_tac[] >>
      `i NOTIN tnu.t_mem DIFF {i | p <= i /\ i < p+32}` by simp[] >>
      `i+1 <= p \/ p+32 <= i` by decide_tac >> metis_tac[]) >>
  `mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) mem =
     mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) u.vs_memory` suffices_by simp[] >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  rpt strip_tac >>
  `i NOTIN tnu.t_mem` by metis_tac[] >>
  `i NOTIN tnu.t_mem DIFF {i | p <= i /\ i < p+32}` by simp[] >>
  `i+1 <= p \/ p+32 <= i` by decide_tac >> metis_tac[]
QED

Resume abi_encode_ready_finish_origin_split[registered]:
  `window_alloca_growth u t` by metis_tac[window_alloca_growth_fields] >>
  irule (cj 1 window_alloca_growth_sequence) >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
    `[(p+32+LENGTH selector,LENGTH (enc at av))]`, `{}`, `[(p,32)]`, `u`] >>
  rewrite_tac[EVERY_DEF,pairTheory.pair_case_thm,EMPTY_SUBSET,SUBSET_REFL] >>
  conj_tac >- (gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_ready_finish_origin_split[exec_frame]:
  `abi_encode_exec_frame func u t` suffices_by
    metis_tac[exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_trans] >>
  qpat_assum `typed_copy_state_frame en p 32 u t` mp_tac >>
  simp[NoAsms, typed_copy_state_frame_def, typed_copy_frame_def,
    venomStateTheory.venom_state_component_equality] >> strip_tac >>
  simp[exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def,
    abi_encode_semantic_obs_def, exprLoweringPropsTheory.pending_alloca_size_def]
QED

Resume abi_encode_ready_finish_origin_split[labels]:
  qpat_assum `typed_copy_state_frame en p 32 u t` mp_tac >>
  simp[NoAsms,typed_copy_state_frame_def,venomStateTheory.venom_state_component_equality] >>
  metis_tac[window_strong_result_labels]
QED

Resume abi_encode_ready_finish_origin_split[protected]:
  gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  conj_tac
  >- (`i+1 <= p \/ p+32 <= i` by
        (qpat_assum `i < p \/ p+32 <= i` mp_tac >> decide_tac) >>
      metis_tac[]) >>
  `i IN tnu.t_mem <=> i IN tn.t_mem` by metis_tac[] >>
  `~(p <= i /\ i < p+32)` by
    (qpat_assum `i < p \/ p+32 <= i` mp_tac >> decide_tac) >>
  qpat_assum `i IN tnu.t_mem <=> i IN tn.t_mem` mp_tac >>
  qpat_assum `~(p <= i /\ i < p+32)` mp_tac >>
  simp[NoAsms,IN_DIFF]
QED

Resume abi_encode_ready_finish_origin_split[kept]:
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
    op_taint tnf (Var x) = op_taint tnu (Var x)` by metis_tac[] >>
  qpat_assum `ghost_kept_at lo ce ee sa G0 tn0 s0 Gu tnu` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >>
  qpat_assum `!n b sz. local_region ce ee.scopes s0 n b sz <=> _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gf x = _ /\ _` mp_tac >>
  qpat_assum `tnf.t_mem = _` SUBST1_TAC >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rewrite_tac[IN_DIFF] >> metis_tac[]
QED

Resume abi_encode_ready_finish_origin_split[inv]:
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at st x` by
    (qpat_assum `local_ptrs_reserved ce st` mp_tac >>
     rewrite_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name entry x sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    lookup_var x u = lookup_var x s` by
    (qpat_assum `local_ptrs_rel func ce ee.scopes s`
       (mp_tac o CONJUNCT1 o REWRITE_RULE[local_ptrs_rel_def]) >>
     qpat_assum `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> _` mp_tac >>
     qpat_assum `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!name off sz. local_region ce ee.scopes u name off sz ==>
    regions_disjoint p 32 off sz` by metis_tac[local_region_lookup_cong] >>
  `local_ptrs_rel func ce ee.scopes u` by
    (qpat_assum `window_alloca_growth s u`
       (strip_assume_tac o REWRITE_RULE[window_alloca_growth_def]) >>
     irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> asm_rewrite_tac[] >>
     conj_tac
     >- (rpt strip_tac >> irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
         rpt strip_tac >> `i IN P` by metis_tac[] >> metis_tac[]) >>
     conj_tac
     >- (qpat_assum `!i b sz. FLOOKUP s.vs_allocas i = NONE /\ _ ==> _` mp_tac >>
         simp_tac bool_ss [CONJ_COMM]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `abi_encoder_registered_effect _ _ s u`
       (mp_then Any irule
         abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated) >>
     first_assum ACCEPT_TAC) >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x` by
    (qpat_assum `local_ptrs_reserved ce st`
       (mp_tac o cj 3 o REWRITE_RULE[local_ptrs_reserved_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `ghost_inv_at D lo ret ce cx ee Gu tnu u` by metis_tac[] >>
  qpat_assum `!D d ce cx es origin G0 tn0 s0. _ ==> ghost_inv_at _ _ _ _ _ _ Gf tnf t /\ _`
    (qspecl_then [`D`,`ret`,`ce`,`cx`,`ee`,`sa`,`G0`,`tn0`,`s0`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[])) >>
  disch_then (ACCEPT_TAC o CONJUNCT1)
QED

Finalise abi_encode_ready_finish_origin_split

Theorem abi_encode_ready_finish_origin:
  compile_abi_encode_to_buf (Var dp) src ei st = (out,en) /\
  abi_builtin_encode_finish (Var root) out (LENGTH selector) en = ((),fin) /\
  fn_has_code st en func /\ fn_has_code en fin func /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Var dp) s = SOME (n2w (p+32+LENGTH selector)) /\
  op_taint tn src = {} /\ op_taint tn (Var dp) = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\ not_fresh_at st dp /\
  ptr_covers G tn dp s dstcap /\
  fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap)
      (p+32+LENGTH selector,LENGTH (enc at av)) /\
    ?x. src = Var x /\ ptr_covers G tn x s cap) /\
  p+32+LENGTH selector+LENGTH (enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (enc at av) ==> ptr_covers G tn dp s (LENGTH (enc at av))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (p+32+LENGTH selector,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_ptrs_rel func ce ee.scopes s /\ local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x. not_fresh_at sa x ==> not_fresh_at st x) /\
  (!i. i IN P ==> i < s.vs_alloca_next /\
    (i < p+32+LENGTH selector \/ p+32+LENGTH selector+LENGTH (enc at av) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)) /\
  (!name b sz i. local_region ce ee.scopes s name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!name b sz i. local_region ce es.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz ==> i IN P) /\
  (!i. i < lo ==> i IN P) /\
  lookup_var root s = SOME (n2w p) /\ not_fresh_at st root /\
  p < dimword(:256) /\ lo <= p /\ 32 <= N /\ ptr_covers G tn root s N /\
  FLOOKUP s.vs_allocas site = SOME (p,N) /\
  LENGTH (enc at av)+LENGTH selector < dimword(:256) /\
  (!name b sz. local_region ce ee.scopes s name b sz ==>
    loweringStateRelDefs$regions_disjoint p 32 b sz) /\
  (!i. p+32 <= i /\ i < p+32+LENGTH selector ==> i IN P) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_bytes_at (p+32) (LENGTH selector) mem = selector) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = fin.cs_current_bb /\
    t.vs_inst_idx = LENGTH fin.cs_current_insts /\
    lookup_var root t = SOME (n2w p) /\ ptr_covers Gf tnf root t N /\
    FLOOKUP t.vs_allocas site = SOME (p,N) /\
    mload p t = n2w (LENGTH (enc at av)+LENGTH selector) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (LENGTH (enc at av)+LENGTH selector) /\
      mem_bytes_at (p+32) (LENGTH selector) mem = selector /\
      mem_bytes_at (p+32+LENGTH selector) (LENGTH (enc at av)) mem = enc at av) /\
    alloca_inv t /\ alloca_room ctx func t /\ allocas_from lo t /\
    (alloca_history func s ==> alloca_history func t) /\
    (abi_alloca_history (fn_insts func) s ==> abi_alloca_history (fn_insts func) t) /\
    window_alloca_growth s t /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
      [(p+32+LENGTH selector,LENGTH (enc at av));(p,32)] s t /\
    abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!i. i IN P /\ (i < p \/ p+32 <= i) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf /\
    !D. ghost_inv_at D lo ret ce cx ee G tn s ==> ghost_inv_at D lo ret ce cx ee Gf tnf t
Proof
  strip_tac >> drule_all abi_encode_ready_finish_origin_split >>
  disch_then (qspecl_then [`ret`, `explicit`, `cx`, `PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
        strip_assume_tac))))))) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED
