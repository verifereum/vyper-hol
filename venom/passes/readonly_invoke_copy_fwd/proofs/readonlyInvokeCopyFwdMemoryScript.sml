(* Memory-only relocation interfaces.  Variable binding and operational
   outcomes are deliberately left to the instruction transport theory.
   For ordinary disjoint instruction writes use ircf_cross_base_frame;
   for unchanged memory use ircf_cross_memory_transport directly. *)
Theory readonlyInvokeCopyFwdMemory
Ancestors
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim o1LowerDloadJointMemoryRead
  o1LowerDloadRangeTransport regularCallEmitSim
  list rich_list pred_set ptrDiscipline codegenRel venomState venomExecSemantics

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
