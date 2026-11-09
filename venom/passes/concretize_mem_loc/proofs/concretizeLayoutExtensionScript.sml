Theory concretizeLayoutExtension
Ancestors concretizeMemLocProofs concretizeMemLocDefs finite_map list arithmetic
  enumeral toto pair

(* Public form of the allocator proof's private symmetry fact. *)
Theorem layout_sinter_nonempty_comm:
  !cmp l m. sinter cmp l m <> [] ==> sinter cmp m l <> []
Proof
  ho_match_mp_tac sinter_ind >> rpt conj_tac
  >- simp[sinter]
  >- simp[sinter]
  >- simp[sinter]
  >> rpt gen_tac >> strip_tac
  >> once_rewrite_tac[sinter] >> strip_tac
  >> Cases_on `apto cmp x y` >> gvs[]
  >> simp[Once toto_swap_cases]
QED

Theorem allocation_extension:
  !G A T M.
  ALL_DISTINCT (MAP FST T) /\
  (!a l s l0 p0 s0. MEM (a,l,s) T ==> ~MEM (a,l0,p0,s0) A) ==>
  ?E.
    MAP (\(a,l,p,s). (a,l,s)) E = T /\
    (!a l p s. MEM (a,l,p,s) E ==>
      FLOOKUP (allocate_with_livesets G A T M) a = SOME p) /\
    (!a. ~MEM a (MAP FST T) ==>
      FLOOKUP (allocate_with_livesets G A T M) a = FLOOKUP M a) /\
    (!a l p s gp gs. MEM (a,l,p,s) E /\ MEM (gp,gs) G ==>
      p+s <= gp \/ gp+gs <= p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\ MEM (b,k,q,t) A /\
      sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\ MEM (b,k,q,t) E /\
      a <> b /\ sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p)
Proof
  ho_match_mp_tac allocate_with_livesets_ind
  >> conj_tac
  >- (rpt strip_tac >> qexists `[]` >> simp[allocate_with_livesets_def])
  >> suspend "step"
QED

Resume allocation_extension[step]:
  rpt gen_tac >> strip_tac >> strip_tac
  >> simp[Once allocate_with_livesets_def]
  >> pairarg_tac >> simp[]
  >> qmatch_asmsub_abbrev_tac `allocate_one reserved sz = (pos,rest)`
  >> first_x_assum (qspecl_then [`reserved`,`pos`,`rest`] mp_tac)
  >> simp[Abbr `reserved`]
  >> (impl_tac >- (gvs[ALL_DISTINCT, MEM_APPEND, MEM_MAP, EXISTS_PROD] >> metis_tac[]))
  >> strip_tac
  >> qexists `(alloc,live_insts,pos,sz)::E`
  >> simp[]
  >> conj_tac >- (rpt strip_tac >> gvs[ALL_DISTINCT, FLOOKUP_UPDATE] >> metis_tac[])
  >> conj_tac >- suspend "untouched"
  >> conj_tac >- suspend "global"
  >> conj_tac >- suspend "old"
  >> suspend "new"
QED

Resume allocation_extension[untouched]:
  simp[Once allocate_with_livesets_def]
  >> rpt strip_tac >> simp[FLOOKUP_UPDATE]
QED

Resume allocation_extension[global]:
  rpt strip_tac >> gvs[]
  >> drule allocate_one_avoids
  >> disch_then (qspecl_then [`gp`,`gs`] mp_tac)
  >> simp[MEM_APPEND] >> metis_tac[]
QED

Resume allocation_extension[old]:
  rpt strip_tac >> gvs[]
  >- (`MEM (q,t) (MAP (\(_,_,p,s). (p,s))
        (FILTER (\(_,k,_,_). sinter inst_addr_to k l <> []) A))`
        by (simp[MEM_MAP, MEM_FILTER, EXISTS_PROD]
            >> metis_tac[layout_sinter_nonempty_comm])
      >> drule allocate_one_avoids
      >> disch_then (qspecl_then [`q`,`t`] mp_tac)
      >> simp[MEM_APPEND])
  >> metis_tac[]
QED

Resume allocation_extension[new]:
  rpt strip_tac >> gvs[] >> metis_tac[layout_sinter_nonempty_comm]
QED

Finalise allocation_extension

Theorem allocation_extension_old_avoids:
  !G A T M R a l s p b k q t.
  ALL_DISTINCT (MAP FST T) /\
  (!a l s l0 p0 s0. MEM (a,l,s) T ==> ~MEM (a,l0,p0,s0) A) /\
  R = allocate_with_livesets G A T M /\
  MEM (a,l,s) T /\ FLOOKUP R a = SOME p /\
  MEM (b,k,q,t) A /\ sinter inst_addr_to l k <> [] ==>
  p+s <= q \/ q+t <= p
Proof
  rpt strip_tac
  >> drule_all allocation_extension
  >> disch_then (qspecl_then [`G`,`M`] strip_assume_tac)
  >> gvs[MEM_MAP, EXISTS_PROD]
  >> metis_tac[optionTheory.SOME_11]
QED

Theorem allocation_extension_new_avoids:
  !G A T M R a l s p b k q t.
  ALL_DISTINCT (MAP FST T) /\
  (!a l s l0 p0 s0. MEM (a,l,s) T ==> ~MEM (a,l0,p0,s0) A) /\
  R = allocate_with_livesets G A T M /\
  MEM (a,l,s) T /\ FLOOKUP R a = SOME p /\
  MEM (b,k,t) T /\ FLOOKUP R b = SOME q /\
  a <> b /\ sinter inst_addr_to l k <> [] ==>
  p+s <= q \/ q+t <= p
Proof
  rpt strip_tac
  >> drule_all allocation_extension
  >> disch_then (qspecl_then [`G`,`M`] strip_assume_tac)
  >> gvs[MEM_MAP, EXISTS_PROD]
  >> metis_tac[optionTheory.SOME_11]
QED

(* No old/old assertion is supplied by allocation_extension.  This
   generic list lemma requires that fact explicitly for both lists. *)
Theorem layout_avoidance_append:
  (!a l p s b k q t.
     MEM (a,l,p,s) A /\ MEM (b,k,q,t) A /\ a <> b /\
     sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p) /\
  (!a l p s b k q t.
     MEM (a,l,p,s) E /\ MEM (b,k,q,t) E /\ a <> b /\
     sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p) /\
  (!a l p s b k q t.
     MEM (a,l,p,s) E /\ MEM (b,k,q,t) A /\
     sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p) ==>
  !a l p s b k q t.
    MEM (a,l,p,s) (A ++ E) /\ MEM (b,k,q,t) (A ++ E) /\ a <> b /\
    sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p
Proof
  simp[MEM_APPEND] >> metis_tac[layout_sinter_nonempty_comm]
QED

Theorem allocation_extension_untouched:
  !G A T M R a.
  ALL_DISTINCT (MAP FST T) /\
  (!a l s l0 p0 s0. MEM (a,l,s) T ==> ~MEM (a,l0,p0,s0) A) /\
  R = allocate_with_livesets G A T M /\ ~MEM a (MAP FST T) ==>
  FLOOKUP R a = FLOOKUP M a
Proof
  rpt strip_tac >> drule_all allocation_extension
  >> disch_then (qspecl_then [`G`,`M`] strip_assume_tac)
  >> gvs[]
QED
