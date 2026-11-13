(* Spatial caller framing for the combined setup/body/finish endpoint.
   ids contains the output site and the encoder's scratch sites. *)
Theory abiEncodePtrGhostFrame
Ancestors
  exprSimAbiEncodeStateTransport logFieldGhostPtr bodyPtrDefs
  abiEncoderRegisteredEffect abiBuiltinEncodeSetup loweringStateRelDefs
  compileEnv venomState finite_map pred_set arithmetic
  exprSimAbiEncodeCallerFrame exprLoweringProps venomMemDefs

Theorem abi_encode_ghost_inv_exterior_defined:
  ghost_inv d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
  local_ptrs_reserved ce sm /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!n b sz i. local_region ce es.scopes s n b sz /\ b <= i /\ i < b+sz ==>
    i NOTIN writes) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!p. not_fresh_at sm p ==> FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) /\
  (!p v. not_fresh_at sm p /\ lookup_var p s = SOME v ==> lookup_var p t = SOME v) ==>
  ghost_inv d ce cx es H tm t
Proof
  strip_tac >> simp[ghost_inv_def] >> conj_tac
  >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[ghost_inv_def,return_buf_ptr_def,ptr_covers_def] >>
      metis_tac[]) >>
  gvs[ghost_inv_def,stor_taint_ok_def]
QED
Resume abi_encode_ghost_inv_exterior_defined[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[ghost_inv_def] >>
  `?u. lookup_var p s = SOME u` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[optionTheory.SOME_11] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> strip_tac >> first_x_assum drule_all >> gvs[]) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[exprSimPropsTheory.val_footprint_le,LESS_EQ_TRANS] >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tm.t_mem`,`writes`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `i < w2n w + sz` by decide_tac >> metis_tac[]
QED
Finalise abi_encode_ghost_inv_exterior_defined

Theorem abi_encode_phases_ghost_transport_defined:
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  st.cs_next_id IN ids /\ FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
  32+w <= outsz /\ alloca_inv actual /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==> FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i b sz. FLOOKUP actual.vs_allocas i = SOME (b,sz) /\
     FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= b) /\
  (!i. i IN ids ==> st.cs_next_id <= i) /\
  (!name entry ptr sz inst.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) /\
  (!i. (!id b sz. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (b,sz) ==>
       i < b \/ b+sz <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
    lookup_var x actual = SOME v) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_accounts = initial.vs_accounts /\
  actual.vs_transient = initial.vs_transient ==>
  ghost_inv rb cenv cx es G' tn' actual /\
  ghost_kept cenv es st G tn initial G' tn'
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes initial` by fs[stmt_state_rel_def, state_rel_def] >>
  qabbrev_tac `writes = {i | ?id b sz. id IN ids /\
    FLOOKUP actual.vs_allocas id = SOME (b,sz) /\ b <= i /\ i < b+sz}` >>
  `!name b sz i. local_region cenv es.scopes initial name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes` by
    (suspend "locals") >>
  `!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (simp[Abbr `writes`] >> rpt strip_tac >> first_x_assum irule >>
     rpt strip_tac >> first_x_assum drule_all >> simp[] >> decide_tac) >>
  conj_tac
  >- (irule abi_encode_ghost_inv_exterior_defined >>
      qexistsl [`G`, `func`, `initial`, `st`, `tn`, `writes`] >> simp[] >>
      conj_tac >- metis_tac[] >> rpt strip_tac >> irule abi_encode_separated_interval_frame >>
      qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `abi_encoder_registered_effect ids [] prepared actual` (irule_at Any) >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `i NOTIN writes` mp_tac >>
      simp[Abbr `writes`] >> disch_then drule_all >> simp[] >> decide_tac) >>
  simp_tac bool_ss [ghost_kept_def] >> conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  suspend "rows"
QED

Resume abi_encode_phases_ghost_transport_defined[locals]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [local_region_def] >> strip_tac >> gvs[] >>
  `!id q k. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (q,k) ==>
    w2n w' + sz <= q \/ q+k <= w2n w'` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_local_ptr_separation >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[Abbr `writes`] >> rpt gen_tac >> strip_tac >>
  Cases_on `id IN ids` >> simp[] >>
  qpat_x_assum `!id q k. _` drule_all >> decide_tac
QED

Resume abi_encode_phases_ghost_transport_defined[rows]:
  rpt gen_tac >> strip_tac >>
  `i NOTIN writes` by
    (simp[Abbr `writes`] >> rpt gen_tac >> strip_tac >>
     Cases_on `id IN ids` >> simp[] >>
     `st.cs_next_id <= id` by metis_tac[] >>
     `aid <> id` by decide_tac >>
     `FLOOKUP actual.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     qpat_x_assum `alloca_inv actual` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
     first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise abi_encode_phases_ghost_transport_defined

Theorem abi_encode_phases_ghost_transport:
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  st.cs_next_id IN ids /\ FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
  32+w <= outsz /\ alloca_inv actual /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==> FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i b sz. FLOOKUP actual.vs_allocas i = SOME (b,sz) /\
     FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= b) /\
  (!i. i IN ids ==> st.cs_next_id <= i) /\
  (!name entry ptr sz inst.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) /\
  (!i. (!id b sz. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (b,sz) ==>
       i < b \/ b+sz <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at st x ==>
    lookup_var x actual = lookup_var x initial /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_accounts = initial.vs_accounts /\
  actual.vs_transient = initial.vs_transient ==>
  ghost_inv rb cenv cx es G' tn' actual /\
  ghost_kept cenv es st G tn initial G' tn'
Proof
  strip_tac >> irule abi_encode_phases_ghost_transport_defined >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!i b sz. _` drule_all >> simp[]) >>
  qexistsl [`ctx`,`func`,`ids`,`prepared`,`w`] >> simp[] >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val _ = Parse.hide "body";

(* The method and data intervals are adjacent; the final store cleans the header. *)
Theorem abi_encode_phases_prefix_clean[local]:
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  d = p+32+m /\ p+32+m <= prepared.vs_alloca_next /\
  window_alloca_growth prepared body /\
  abi_encoder_registered_effect ids [(d,n)] prepared body /\
  (!id b sz. id IN ids /\ FLOOKUP prepared.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  tf.t_mem = (if fresh then tn.t_mem UNION {i | p <= i /\ i < p+outsz}
              else tn.t_mem) DIFF
    (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64}) /\
  (!i. d <= i /\ i < d+n ==> i NOTIN tbody.t_mem) /\
  (!i. (i < d \/ d+n <= i) /\
    (!id b sz. id IN ids /\ FLOOKUP body.vs_allocas id = SOME (b,sz) ==>
      i < b \/ b+sz <= i) ==> (i IN tbody.t_mem <=> i IN tf.t_mem)) /\
  tn'.t_mem = tbody.t_mem DIFF {i | p <= i /\ i < p+32} ==>
  !i. p <= i /\ i < p+32+m+n ==> i NOTIN tn'.t_mem
Proof
  strip_tac >>
  `!id b sz. id IN ids /\ FLOOKUP body.vs_allocas id = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `FLOOKUP prepared.vs_allocas id` >-
       (qpat_x_assum `window_alloca_growth _ _` mp_tac >>
        simp_tac bool_ss [abiEncoderWindowContractTheory.window_alloca_growth_def] >>
        strip_tac >> first_x_assum drule_all >>
        simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rename1 `FLOOKUP prepared.vs_allocas id = SOME row` >>
     `row = (b,sz)` by
       (drule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
        metis_tac[optionTheory.SOME_11]) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  pure_asm_rewrite_tac[pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
  Cases_on `i < p+32` >- simp[] >>
  Cases_on `d <= i` >- metis_tac[] >>
  `i NOTIN tf.t_mem` by
    (qpat_x_assum `tf.t_mem = _` SUBST1_TAC >>
     qpat_x_assum `m = _` mp_tac >>
     Cases_on `method_id` >> simp[] >> decide_tac) >>
  `!id b sz. id IN ids /\ FLOOKUP body.vs_allocas id = SOME (b,sz) ==>
    i < b \/ b+sz <= i` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!id b sz. _ ==> venomMemDefs$regions_disjoint _ _` drule_all >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!i. (i < d \/ _) /\ _ ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem abi_encode_phases_taint_exterior[local]:
  stid IN ids /\ FLOOKUP actual.vs_allocas stid = SOME (p,outsz) /\
  p <= d /\ d+n <= p+outsz /\ 32+w <= outsz /\
  (method_id <> NONE ==> w = 32) /\
  (!id. id IN body_ids ==> id IN ids) /\ actual.vs_allocas = body.vs_allocas /\
  tf.t_mem = (if fresh then tn.t_mem UNION {i | p <= i /\ i < p+outsz}
              else tn.t_mem) DIFF
    (case method_id of NONE => {} | SOME mid => {i | p+32 <= i /\ i < p+64}) /\
  (!i. (i < d \/ d+n <= i) /\
    (!id b sz. id IN body_ids /\ FLOOKUP body.vs_allocas id = SOME (b,sz) ==>
      i < b \/ b+sz <= i) ==> (i IN tbody.t_mem <=> i IN tf.t_mem)) /\
  tn'.t_mem = tbody.t_mem DIFF {i | p <= i /\ i < p+32} ==>
  !i. (!id b sz. id IN ids /\ FLOOKUP actual.vs_allocas id = SOME (b,sz) ==>
        i < b \/ b+sz <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `i < p \/ p+outsz <= i` by metis_tac[] >>
  `i < d \/ d+n <= i` by decide_tac >>
  `!id b sz. id IN body_ids /\ FLOOKUP body.vs_allocas id = SOME (b,sz) ==>
    i < b \/ b+sz <= i` by metis_tac[] >>
  `i IN tbody.t_mem <=> i IN tf.t_mem` by metis_tac[] >>
  `i IN tf.t_mem <=> i IN tn.t_mem` by
    (qpat_x_assum `tf.t_mem = _` SUBST1_TAC >>
     Cases_on `fresh` >> Cases_on `method_id` >> gvs[] >> decide_tac) >>
  qpat_x_assum `tn'.t_mem = _` SUBST1_TAC >> simp[] >> decide_tac
QED
