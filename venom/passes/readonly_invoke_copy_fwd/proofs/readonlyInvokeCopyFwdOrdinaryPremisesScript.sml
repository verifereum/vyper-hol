Theory readonlyInvokeCopyFwdOrdinaryPremises
Ancestors
  readonlyInvokeCopyFwdStepsDret readonlyInvokeCopyFwdMemory readonlyInvokeCopyFwdRel
  o1LowerDloadOccurrence allocaFrontierBound ptrDiscipline taintAgree
  venomExecSemantics venomState list pred_set finite_map words

(* The raw/effective conversion changes variable taint only.  Observation
   cleanliness is supplied by source pointer discipline, not by agreement. *)
Theorem ricf_cert_raw_memory_taint:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  tn.t_mem = tn0.t_mem /\ tn.t_stor = tn0.t_stor /\
  tn.t_trans = tn0.t_trans
Proof
  simp[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  strip_tac >> Cases_on `s.vs_prev_bb = NONE` >>
  gvs[entry_taint_vars_def, AllCaseEqs()]
QED

Theorem ricf_reachable_observation_slice:
  ptr_discipline lo C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  MEM inst.inst_opcode [SHA3; LOG; CREATE; CREATE2] /\
  ~in_revert_forward fn s /\
  MEM (db+off,len) (source_memory_read_ranges inst s) /\
  ircf_cross tn0 gam s t /\ (db,sb,sz) IN gam /\ off+len <= sz ==>
  read_memory (db+off) len s = read_memory (sb+off) len t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_mem = tn0.t_mem` by metis_tac[ricf_cert_raw_memory_taint] >>
  irule ricf_cross_clean_slice >> qexistsl_tac [`gam`, `sz`, `tn0`] >>
  disj2_tac >> simp[] >>
  rpt strip_tac >>
  drule_all taint_ok_observation_read >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem ricf_reachable_concrete_accounts:
  ptr_discipline lo C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2] ==>
  tn0.t_stor = {} /\ tn0.t_trans = {}
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  drule ricf_cert_raw_memory_taint >> strip_tac >>
  gvs[taint_ok_def]
QED

Theorem ricf_reachable_no_dalloca:
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ ~ctx_has_dalloca C ==>
  inst.inst_opcode <> DALLOCA
Proof
  strip_tac >>
  `?n a U B HP H.
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[frame_reachable_occurrence_lift] >>
  drule occ_frame_reachable_annotation >> strip_tac >>
  drule active_inst_mem_fn_insts >>
  fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]
QED

(* An empty certificate needs no protected geometry.  Nonempty certificates
   need an origin theorem; cross agreement alone supplies no such theorem. *)
Theorem ricf_pack_footprint_empty_entry:
  ricf_pack_footprint FEMPTY [] [] {} [] = {}
Proof
  simp[ricf_pack_footprint_def, ricf_site_triples_def, EXTENSION]
QED

(* Both copies initially read equal bytes.  The first destination overlaps
   only the source run's second read: initial slice equality is insufficient
   for pack_checks, even with no protected triples and completely clean taint.
   This is an interface probe, not a reachable-program counterexample. *)
Theorem ricf_pack_two_overlap_probe:
  let s = s0 with vs_memory :=
    GENLIST (\i. if i = 0 \/ i = 64 then 1w else 2w) 128 in
  read_memory 0 1 s = read_memory 64 1 s /\
  read_memory 32 1 s = read_memory 96 1 s /\
  ~ricf_pack_checks {} (32w:bytes32)
    ([(0w,1w);(32w,1w)]:(bytes32 # bytes32) list)
    ([(64w,1w);(96w,1w)]:(bytes32 # bytes32) list) {} s s
Proof
  `dimword (:256) = 2 ** 256` by
    simp[wordsTheory.dimword_def, fcpTheory.index_bit0,
      wordsTheory.dimindex_128, wordsTheory.finite_128,
      fcpTheory.finite_bit0, fcpTheory.index_one, fcpTheory.finite_one] >>
  asm_simp_tac std_ss [LET_THM, ricf_pack_checks_def, ricf_pack_mem_def,
    wordsTheory.word_0_n2w, wordsTheory.w2n_n2w] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[wordsTheory.dimword_def, fcpTheory.index_bit0,
    fcpTheory.finite_bit0, fcpTheory.index_one, fcpTheory.finite_one]
QED

(* Geometry discharge boundary: the missing producer is allocation origin,
   not this arithmetic step.  In particular cert_core does not imply the
   bounded-endpoint hypothesis below. *)
Theorem ricf_pack_protected_frontier:
  (!db sb n. (db,sb,n) IN ricf_pack_footprint sites maps stk cur curs ==>
     db+n <= frontier /\ sb+n <= frontier) /\ frontier <= w2n cursor ==>
  !db sb n k. (db,sb,n) IN ricf_pack_footprint sites maps stk cur curs /\ k < n ==>
    ~(w2n cursor <= db+k /\ db+k < w2n cursor+w2n sz) /\
    ~(w2n cursor <= sb+k /\ sb+k < w2n cursor+w2n sz)
Proof
  rpt strip_tac >>
  `db+n <= frontier /\ sb+n <= frontier` by metis_tac[] >> decide_tac
QED

Theorem ricf_pack_copy_frontier_extension:
  (!b c n. (b,c,n) IN ricf_pack_footprint sites maps stk cur curs ==>
     b+n <= frontier /\ c+n <= frontier) /\
  db+sz <= frontier /\ sb+sz <= frontier ==>
  !b c n. (b,c,n) IN
      ricf_pack_footprint sites maps stk (cur UNION {(db,sb,sz)}) curs ==>
    b+n <= frontier /\ c+n <= frontier
Proof
  simp[ricf_pack_footprint_def] >> metis_tac[]
QED

(* Remaining producer obligations (NOT established by this probe):

   A. Reachable origin: each (db,sb,n) in pack_footprint must have
      owner-indexed allocation witnesses in the occurrence annotation B,
      with valid readonly call history for inherited maps.  This must imply
      db+n <= frontier /\ sb+n <= frontier at every write use.  The empty
      case and a bounded copy insertion are checked above, but Calls must
      transport owners through entry/restore and the block proof must
      relate activated copies to their actual source allocation witnesses.

   B. Observation address classification: eval of a related memory address
      must yield either a same-address unprotected slice or db+off/sb+off
      for a footprint triple, with off+len <= n.  Source access_ok and
      provenance soundness are the needed producers.  Once classified,
      ricf_reachable_observation_slice discharges clean equality for
      SHA3/LOG/CREATE/CREATE2.  CALL-family clean slices need their own
      taint_ok opcode analysis; they are not covered by that theorem.

   C. External concrete accounts: ricf_reachable_concrete_accounts proves
      the raw-index stor/trans emptiness from discipline exactly for
      DELEGATECALL/CREATE/CREATE2.  No global emptiness assumption is needed.
      Clean operand evaluation uses taint_ok plus the Values interfaces;
      an active pointer operand still requires address classification (B).

   D. DRET: for every finite prefix p, let (M_p,s_p,t_p,c_p) be obtained by
      the recursive pack_mem/mcopy/cursor equations.  Need related reads
      at M_p, not merely M_0, and disjointness of the c_p write from every
      protected triple.  In addition to origin (A), a cursor invariant must
      justify a suitable frontier <= w2n c_p without modular wrap, and
      earlier writes must not destroy future related source reads (or an
      overlap-aware invariant must track them).  The checked two-element
      overlap probe refutes deriving this solely from entry slice equality.
      No theorem about the frozen task is refuted by this auxiliary probe.

   All A/B/D producers must be proved available at the actual recursive
   block/Calls use sites before the conditional adapters yield coverage.
   No new admissibility predicate has been adopted here: its initialization
   alone would not establish the required call and DRET preservation.
*)
