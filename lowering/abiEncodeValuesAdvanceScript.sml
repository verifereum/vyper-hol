Theory abiEncodeValuesAdvance
Ancestors
  abiEncodeValuesLayout abiEncodeValuesPhases abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderTuple abiEncoderOpenInput abiStaticAggregateProps
  loweringPosts bodyPtrDefs loweringStateRelDefs compileEnv
  ptrDiscipline venomState venomMemDefs valueEncodingDefs contractABI
  finite_map pred_set list arithmetic

(* The row writes immediately after the existing head and tail prefixes.
   Both prefixes lie in the destination's registered allocation. *)
Theorem abi_encode_values_phase_advance:
  LENGTH pre = LENGTH pvs /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  hs = abi_member_head_size at /\ ts = abi_member_tail_size at av /\
  h + hs <= hl /\ abi_encoder_layout_valid at av /\
  abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
  (!i. d <= i /\ i < d + h ==> i NOTIN tn.t_mem) /\
  (!i. d + hl <= i /\ i < d + off ==> i NOTIN tn.t_mem) /\
  window_phase ctx func st en ids outs s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas dst_site = SOME (dst_base,dst_cap) /\ dst_site NOTIN ids /\
  dst_base <= d /\ d + off + ts <= dst_base + dst_cap /\
  outs = (if is_dynamic at then [(d+h,hs); (d+off,ts)] else [(d+h,hs)]) /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) outs /\
     (!id b n. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (b,n) ==>
       i < b \/ b+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (!i. d+h <= i /\ i < d+h+hs ==> i NOTIN tn'.t_mem) /\
  (!i. d+off <= i /\ i < d+off+ts ==> i NOTIN tn'.t_mem) /\
  (is_dynamic at ==>
    mem_word_at (d+h) t.vs_memory = n2w off /\
    mem_bytes_at (d+off) ts t.vs_memory = enc at av) /\
  (~is_dynamic at ==>
    mem_bytes_at (d+h) hs t.vs_memory = enc at av) ==>
  abi_encoder_tuple_prefix hl (pre ++ [at]) (pvs ++ [av]) d t.vs_memory /\
  (!i. d <= i /\ i < d+h+hs ==> i NOTIN tn'.t_mem) /\
  (!i. d+hl <= i /\ i < d+off+ts ==> i NOTIN tn'.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `tl = LENGTH (FLAT (abi_tuple_tails pre pvs))` >>
  `off = hl + tl` by simp[Abbr `tl`] >>
  `!q n. ((q = d /\ n = h) \/ (q = d+hl /\ n = tl)) ==>
      mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory /\
      (!i. q <= i /\ i < q+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     `dst_base <= q /\ q+n <= dst_base+dst_cap` by decide_tac >>
     `EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs` by
       (Cases_on `is_dynamic at` >>
        fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     mp_tac (Q.INST [`q` |-> `q`, `n` |-> `n`, `b` |-> `dst_base`,
       `sz` |-> `dst_cap`, `owner` |-> `dst_site`] abi_encode_values_registered_window) >>
     asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `!q n. _ ==> _` (fn th =>
    MAP_EVERY (fn args => strip_assume_tac (SIMP_RULE bool_ss [] (Q.SPECL args th)))
      [[`d`,`h`],[`d+hl`,`tl`]]) >>
  `!i. (d <= i /\ i < d+h) \/ (d+hl <= i /\ i < d+off) ==>
      i IN tn'.t_mem ==> i IN tn.t_mem` by
    (gen_tac >> strip_tac >> disch_tac >>
     Cases_on `i < d+h`
     >- (qpat_assum `!j. d <= j /\ j < d+h /\ _ ==> _` (qspec_then `i` mp_tac) >>
         impl_tac >- (asm_rewrite_tac[] >> decide_tac) >> simp[]) >>
     qpat_assum `!j. d+hl <= j /\ j < d+hl+tl /\ _ ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> decide_tac) >> simp[]) >>
  mp_tac (Q.INST [`heads` |-> `h`, `tails` |-> `tl`, `ty` |-> `at`, `v` |-> `av`]
    abi_encode_values_advance_prefix) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `tl`]) >>
  disch_then ACCEPT_TAC
QED

(* Materializing a delayed argument may allocate and copy. The cursor
   and both prefixes were already registered at its input cut. *)
Theorem abi_encode_values_unwrap_prefix:
  wb_frame ce ee ee st s t /\ ghost_kept_at lo ce ee st G tn s G' tn' /\
  FLOOKUP s.vs_allocas dst_site = SOME (dst_base,dst_cap) /\ dst_site < st.cs_next_id /\
  FLOOKUP s.vs_allocas cursor_site = SOME (slot,32) /\ cursor_site < st.cs_next_id /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    (dst_base + dst_cap <= p \/ p+k <= dst_base) /\
    (slot + 32 <= p \/ p+k <= slot)) /\
  dst_base <= d /\ d+h <= dst_base+dst_cap /\ d+hl+tl <= dst_base+dst_cap /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tl = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
  (!i. d <= i /\ i < d+h ==> i NOTIN tn.t_mem) /\
  (!i. d+hl <= i /\ i < d+hl+tl ==> i NOTIN tn.t_mem) /\
  mem_word_at slot s.vs_memory = n2w (hl+tl) /\
  (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn.t_mem) ==>
  FLOOKUP t.vs_allocas dst_site = SOME (dst_base,dst_cap) /\
  FLOOKUP t.vs_allocas cursor_site = SOME (slot,32) /\
  abi_encoder_tuple_prefix hl pre pvs d t.vs_memory /\
  (!i. d <= i /\ i < d+h ==> i NOTIN tn'.t_mem) /\
  (!i. d+hl <= i /\ i < d+hl+tl ==> i NOTIN tn'.t_mem) /\
  mem_word_at slot t.vs_memory = n2w (hl+tl) /\
  (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn'.t_mem)
Proof
  strip_tac >>
  `!q n. dst_base <= q /\ q+n <= dst_base+dst_cap ==>
    FLOOKUP t.vs_allocas dst_site = SOME (dst_base,dst_cap) /\
    mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory /\
    (!i. q <= i /\ i < q+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`id` |-> `dst_site`, `b` |-> `dst_base`,
       `sz` |-> `dst_cap`, `len` |-> `n`] abi_encode_values_unwrap_window) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `!q n. dst_base <= q /\ _ ==> _` (fn th =>
    MAP_EVERY (fn args =>
      mp_tac (Q.SPECL args th) >> impl_tac >- decide_tac >> strip_tac)
      [[`d`,`h`],[`d+hl`,`tl`]]) >>
  mp_tac (Q.INST [`id` |-> `cursor_site`, `b` |-> `slot`, `sz` |-> `32`,
    `q` |-> `slot`, `len` |-> `32`] abi_encode_values_unwrap_window) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >>
  `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
    (qpat_assum `mem_bytes_at slot 32 t.vs_memory = _` (fn th =>
       PURE_REWRITE_TAC [abiStaticAggregatePropsTheory.mem_word_at_bytes, th]) >> REFL_TAC) >>
  `abi_encoder_tuple_prefix hl pre pvs d t.vs_memory` by
    (qpat_assum `abi_encoder_tuple_prefix hl pre pvs d s.vs_memory` mp_tac >>
     qpat_assum `h = _` (fn hh => qpat_assum `tl = _` (fn tt =>
       PURE_REWRITE_TAC [abi_encoder_tuple_prefix_def, GSYM hh, GSYM tt])) >>
     asm_rewrite_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> metis_tac[]
QED
