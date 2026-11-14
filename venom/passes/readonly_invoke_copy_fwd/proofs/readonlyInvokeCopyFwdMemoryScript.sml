(* Memory-only relocation interfaces.  Variable binding and operational
   outcomes are deliberately left to the instruction transport theory.
   For ordinary disjoint instruction writes use ircf_cross_base_frame;
   for unchanged memory use ircf_cross_memory_transport directly. *)
Theory readonlyInvokeCopyFwdMemory
Ancestors
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim o1LowerDloadJointMemoryRead
  o1LowerDloadRangeTransport regularCallEmitSim taintAgree
  list rich_list pred_set finite_map ptrDiscipline codegenRel venomState venomExecSemantics

Theorem ricf_cross_read_bytes:
  ircf_cross tn gam s t /\ (db,sb,sz) IN gam /\ off + len <= sz ==>
  !k. k < len ==>
    (db+off+k IN tn.t_mem <=> sb+off+k IN tn.t_mem) /\
    (db+off+k NOTIN tn.t_mem ==>
      read_byte (db+off+k) s.vs_memory =
      read_byte (sb+off+k) t.vs_memory)
Proof
  strip_tac >> drule_all ricf_cross_finite_read >>
  simp_tac std_ss [LIST_REL_EL_EQN, LENGTH_GENLIST, EL_GENLIST,
                   arithmeticTheory.ADD_ASSOC]
QED

Theorem ricf_cross_mload:
  ircf_cross tn gam s t /\ (db,sb,sz) IN gam /\ off + 32 <= sz ==>
  word_agree_except (mem_word_taint tn.t_mem (db+off))
    (mload (db+off) s) (mload (sb+off) t) /\
  mem_word_taint tn.t_mem (db+off) = mem_word_taint tn.t_mem (sb+off)
Proof
  strip_tac >>
  `!k. k < 32 ==>
    (db+off+k IN tn.t_mem <=> sb+off+k IN tn.t_mem) /\
    (db+off+k NOTIN tn.t_mem ==>
      read_byte (db+off+k) s.vs_memory = read_byte (sb+off+k) t.vs_memory)` by
    metis_tac[ricf_cross_read_bytes] >>
  conj_tac
  >- (irule ld_mload_masked_bytes >>
      simp_tac std_ss [mem_word_taint_def, GSPECIFICATION] >> metis_tac[]) >>
  simp_tac std_ss [mem_word_taint_def, EXTENSION, GSPECIFICATION] >> metis_tac[]
QED

Theorem ricf_cross_read_slice:
  ircf_cross tn gam s t /\ (db,sb,sz) IN gam /\ off + len <= sz ==>
  !k. k < len /\ db+off+k NOTIN tn.t_mem ==>
    EL k (read_memory (db+off) len s) =
    EL k (read_memory (sb+off) len t)
Proof
  rpt strip_tac >>
  asm_simp_tac std_ss [ld_read_memory_element] >>
  metis_tac[ricf_cross_read_bytes]
QED

(* A zero-length slice needs no active site, address bound or cleanliness. *)
Theorem ricf_cross_clean_slice:
  len = 0 \/
  (ircf_cross tn gam s t /\ (db,sb,sz) IN gam /\ off + len <= sz /\
   (!k. k < len ==> db+off+k NOTIN tn.t_mem)) ==>
  read_memory (db+off) len s = read_memory (sb+off) len t
Proof
  strip_tac >- simp[read_memory_def] >>
  irule LIST_EQ >> simp_tac std_ss [ld_read_memory_length] >> rpt strip_tac >>
  irule ricf_cross_read_slice >> metis_tac[]
QED

(* Cross facts can survive writes without requiring equality of entire
   memories, or of all memory taint.  Only protected intervals matter. *)
Theorem ricf_cross_byte_frame:
  ircf_cross tn gam s t /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    (db+k IN tn'.t_mem <=> db+k IN tn.t_mem) /\
    (sb+k IN tn'.t_mem <=> sb+k IN tn.t_mem) /\
    read_byte (db+k) s'.vs_memory = read_byte (db+k) s.vs_memory /\
    read_byte (sb+k) t'.vs_memory = read_byte (sb+k) t.vs_memory) ==>
  ircf_cross tn' gam s' t'
Proof
  simp[ircf_cross_def] >> metis_tac[]
QED

(* Activating a new copy is exactly the existing IRCF source-copy lemma.
   Existing translations are kept separately, with explicit byte framing
   and taint framing across the copy, including overlapping target keys. *)
Theorem ricf_cross_activate_copy:
  ircf_cross tn gam s t /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!b c z k. (b,c,z) IN gam /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ircf_cross tn' (gam UNION {(db,sb,len)}) (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross tn' {(db,sb,len)} (mcopy db sb len s) t` by
    (qpat_x_assum `tn' = _` SUBST1_TAC >>
     irule ircf_cross_source_mcopy >> asm_rewrite_tac[]) >>
  `ircf_cross tn' gam (mcopy db sb len s) t` by
    (irule ricf_cross_byte_frame >> qexistsl_tac [`s`, `t`, `tn`] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     rpt gen_tac >> strip_tac >>
     `~(db <= db'+k /\ db'+k < db+len) /\
      ~(db <= sb'+k /\ sb'+k < db+len)` by metis_tac[] >>
     `!q. q < len ==> db'+k <> db+q /\ sb'+k <> db+q` by
       (rpt strip_tac >> decide_tac) >>
     qpat_x_assum `tn' = _` SUBST1_TAC >>
     asm_simp_tac (srw_ss()) [mcopy_def, LET_THM, GSYM read_memory_def,
       regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
       ld_read_memory_length] >> metis_tac[]) >>
  qpat_x_assum `tn' = _` kall_tac >>
  fs[ircf_cross_def, IN_UNION] >> metis_tac[]
QED

(* The copy changes only memory and memory taint.  In particular it does
   not activate a translation in the caller's local-value map. *)
Theorem ricf_frame_source_mcopy:
  ricf_frame_agree D X sites PG G tn s t /\
  {i | db <= i /\ i < db+len /\ i < s.vs_alloca_next} SUBSET X /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!b c z k. (b,c,z) IN ricf_site_triples sites /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_frame_agree D X sites PG G tn' (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross tn' (ricf_site_triples sites) (mcopy db sb len s) t` by
    (irule ricf_cross_source_mcopy_frame >>
     fs[ricf_frame_agree_def] >> metis_tac[]) >>
  `taint_agree D X tn' (mcopy db sb len s)
     (t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>)` by
    (qpat_x_assum `tn' = _` SUBST1_TAC >>
     `mcopy db sb len s = s with vs_memory := (mcopy db sb len s).vs_memory` by
       simp[mcopy_def, write_memory_with_expansion_def] >>
     pop_assum SUBST1_TAC >>
     `taint_agree D X
       (tn with t_mem := (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
                         {db+q | q < len /\ sb+q IN tn.t_mem})
       (s with vs_memory := (mcopy db sb len s).vs_memory)
       ((t with <| vs_vars := s.vs_vars; vs_params := s.vs_params |>)
          with vs_memory := t.vs_memory)` suffices_by
       (simp[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_def] >>
        metis_tac[]) >>
     irule taint_agree_memory_update >>
     reverse conj_tac >- fs[ricf_frame_agree_def] >>
     rpt strip_tac >>
     `~(db <= i /\ i < db+len)` by
       (fs[SUBSET_DEF] >> metis_tac[]) >>
     `i NOTIN tn.t_mem` by gvs[] >>
     simp[mcopy_def, regularCallEmitSimTheory.read_byte_write_memory_with_expansion,
          GSYM read_memory_def, ld_read_memory_length] >>
     fs[ricf_frame_agree_def, taint_agree_def] >> metis_tac[]) >>
  qpat_x_assum `tn' = _` SUBST_ALL_TAC >>
  fs[ricf_frame_agree_def, mcopy_def, write_memory_with_expansion_def,
     op_taint_def]
QED

Theorem ricf_mcopy_merge:
  merge_callee_state a (mcopy db sb len s) =
  mcopy db sb len (merge_callee_state a s)
Proof
  simp[merge_callee_state_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem ricf_live_stack_source_mcopy:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!j b c z k. j < LENGTH stk /\
    (b,c,z) IN ricf_site_triples (EL j maps) /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_live_stack_agree D ids tn' maps stk targets (mcopy db sb len s) t
Proof
  pure_rewrite_tac [ricf_live_stack_agree_def, ricf_mcopy_merge] >>
  strip_tac >> asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  match_mp_tac (ricf_frame_source_mcopy |> Q.INST
    [`tn` |-> `tn with t_var := (EL j stk).cf_tvar`]) >>
  asm_simp_tac (srw_ss()) [GSYM merge_callee_state_def,
    merge_callee_state_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ricf_cross_source_mcopy_frame:
  ircf_cross tn gam s t /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!b c z k. (b,c,z) IN gam /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ircf_cross tn' gam (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross tn' (gam UNION {(db,sb,len)}) (mcopy db sb len s) t` by
    (match_mp_tac ricf_cross_activate_copy >> asm_rewrite_tac[]) >>
  qpat_x_assum `ircf_cross tn' _ _ _` mp_tac >>
  simp[ircf_cross_def] >> metis_tac[]
QED

(* Both suspended index lists and the inherited local-value map stay fixed.
   The boundary variable taint is explicitly re-entered from the updated
   memory taint; no operational instruction-step claim is made here. *)
Theorem ricf_cert_activate_copy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  {i | db <= i /\ i < db+len} SUBSET ircf_dead ids s stk /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn0.t_mem} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !b c z k. (b,c,z) IN gam /\ k < z ==>
      ~(db <= b+k /\ b+k < db+len) /\
      ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
    fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
    (mcopy db sb len s) t
Proof
  strip_tac >>
  `ircf_cross un (cur UNION {(db,sb,len)}) (mcopy db sb len s) t` by
    (irule ricf_cross_activate_copy >>
     fs[ricf_cert_core_def] >> metis_tac[]) >>
  `ricf_cert_crosses un curs stk (mcopy db sb len s) t` by
    (fs[ricf_cert_core_def, ricf_cert_crosses_def, EVERY_MEM] >>
     rpt strip_tac >>
     match_mp_tac (ricf_cross_source_mcopy_frame |> Q.INST [`tn` |-> `tn0`]) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `ricf_frame_agree D (ircf_dead ids s stk) sites
     (ricf_complete_params PG s.vs_params) G0 un (mcopy db sb len s) t` by
    (match_mp_tac (ricf_frame_source_mcopy |> Q.INST [`tn` |-> `tn0`]) >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def, SUBSET_DEF] >> metis_tac[]) >>
  `ricf_live_stack_agree D ids un maps stk targets (mcopy db sb len s) t` by
    (match_mp_tac (ricf_live_stack_source_mcopy |> Q.INST [`tn` |-> `tn0`]) >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def, SUBSET_DEF] >> metis_tac[]) >>
  qpat_x_assum `un = _` SUBST_ALL_TAC >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def,
     ircf_dead_def, entry_prov_def, entry_taint_vars_def,
     mcopy_def, write_memory_with_expansion_def]
QED

(* A genuinely nonidentity copy, with an unrelocated destination local.
   Arbitrary other shared fields are retained, rather than hidden behind
   an assumption that the desired post-copy relation already holds. *)
Definition ricf_copy_probe_state_def:
  ricf_copy_probe_state s = s with
    <| vs_prev_bb := NONE; vs_params := [];
       vs_vars := FEMPTY |+ ("dst",0w);
       vs_allocas := FEMPTY |+ (7,(0,1)); vs_alloca_next := 2;
       vs_memory := [7w;9w] |>
End

Theorem ricf_cert_nonidentity_copy_probe:
  !s D fn.
  ricf_cert_core D {7} [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint fn
    FEMPTY [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint {(0,1,1)} []
    (mcopy 0 1 1 (ricf_copy_probe_state s)) (ricf_copy_probe_state s) /\
  FLOOKUP (FEMPTY |+ ("dst",(0,1))) "dst" = SOME (0,1) /\
  FLOOKUP (ricf_copy_probe_state s).vs_vars "dst" = SOME 0w /\
  FLOOKUP (mcopy 0 1 1 (ricf_copy_probe_state s)).vs_vars "dst" = SOME 0w /\
  read_byte 0 (mcopy 0 1 1 (ricf_copy_probe_state s)).vs_memory = 9w /\
  read_byte 0 (ricf_copy_probe_state s).vs_memory = 7w
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `mcopy 0 1 1 a` >>
  `taint_agree D (ircf_dead {7} a []) entry_taint a a` by
    simp[taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_refl,
         word_agree_except_def] >>
  `ricf_cert_core D {7} [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint fn
     FEMPTY [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint {} [] a a` by
    (simp[ricf_cert_core_def, ricf_live_boundary_core_def,
          ricf_cert_crosses_def, ricf_frame_agree_completed_identity,
          ircf_cross_def, Abbr `a`, ricf_copy_probe_state_def] >>
     irule ricf_frame_agree_completed_identity >>
     fs[Abbr `a`, ricf_copy_probe_state_def]) >>
  `ricf_cert_core D {7} [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint fn
     FEMPTY [] [] (FEMPTY |+ ("dst",(0,1))) entry_taint {(0,1,1)} []
     (mcopy 0 1 1 a) a` by
    (drule ricf_cert_activate_copy >>
     disch_then (qspecl_then [`entry_taint`, `1`, `1`, `0`] mp_tac) >>
     simp[Abbr `a`, ricf_copy_probe_state_def, entry_taint_def,
          ircf_dead_def, site_bytes_def, ricf_site_triples_def,
          FLOOKUP_UPDATE, SUBSET_DEF]) >>
  simp[Abbr `a`, ricf_copy_probe_state_def, mcopy_def,
       write_memory_with_expansion_def, read_byte_def, FLOOKUP_UPDATE]
QED
