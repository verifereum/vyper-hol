(* The final taint is allocation-relative: unused padding is not written. *)
Theory bodyPtrBytestringBuiltinsSliceEndpoint
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice bodyPtrBytestringBuiltinsCalldataCopy
  exprSimPtrLiteralBuffer bodyPtrDefs ptrDiscipline words pred_set

Theorem external_slice_written_taint:
  32 <= N /\ w2n (a:bytes32) + N < dimword (:256) /\
  tm.t_mem = (dirty DIFF {i | w2n (a + 32w) <= i /\
    i < w2n (a + 32w) + w2n wn})
    DIFF {i | w2n a <= i /\ i < w2n a + 32} ==>
  tm.t_mem SUBSET dirty /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n wn ==> i NOTIN tm.t_mem)
Proof
  strip_tac >>
  `w2n (a + 32w) = w2n a + 32` by
    (`w2n a + 32 < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  gvs[] >> decide_tac
QED

(* The two separation premises are supplied by allocation replay.  Variable
   freshness alone does not establish either memory separation fact. *)
Theorem external_slice_allocated_ghost_kept:
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_mem SUBSET (tn.t_mem UNION dirty) /\
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off + sz ==> i NOTIN dirty) /\
  (!name off sz i. local_region cenv es.scopes s name off sz /\
    off <= i /\ i < off + sz ==> i NOTIN dirty) ==>
  ghost_kept cenv es sa G tn s H tm
Proof
  simp[ghost_kept_def, SUBSET_DEF] >> rpt strip_tac >> metis_tac[]
QED

Theorem external_slice_allocated_endpoint:
  32 <= N /\ w2n (a:bytes32) + N < dimword (:256) /\
  tm.t_mem = ((tn.t_mem UNION new_site_bytes s u)
    DIFF {i | w2n (a + 32w) <= i /\ i < w2n (a + 32w) + w2n wn})
    DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off + sz ==>
    i NOTIN new_site_bytes s u) /\
  (!name off sz i. local_region cenv es.scopes s name off sz /\
    off <= i /\ i < off + sz ==> i NOTIN new_site_bytes s u) ==>
  tm.t_mem SUBSET (tn.t_mem UNION new_site_bytes s u) /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n wn ==> i NOTIN tm.t_mem) /\
  ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >> drule_all external_slice_written_taint >> strip_tac >>
  qpat_x_assum `tm.t_mem = _` kall_tac >> simp[] >>
  irule external_slice_allocated_ghost_kept >> simp[] >>
  qexists_tac `new_site_bytes s u` >> metis_tac[]
QED

Theorem external_slice_suffix_taint:
  tm.t_mem = (tn.t_mem DIFF {i | dst <= i /\ i < dst + n})
    DIFF {i | root <= i /\ i < root + 32} ==>
  tm.t_mem SUBSET tn.t_mem /\
  (!i. dst <= i /\ i < dst + n ==> i NOTIN tm.t_mem) /\
  (!i. root <= i /\ i < root + 32 ==> i NOTIN tm.t_mem)
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED
