(* Root-relative provenance and taint across the reserve and typed copy. *)
Theory bodyIfExpTypedKeptMods
Ancestors
  bodyPtrDefs freshWrites loweringStateRelDefs ptrDiscipline arithmetic

Theorem ifexp_typed_exterior_taint[local]:
  (!i. i < next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!i. ~(dst <= i /\ i < dst+n) ==> (i IN tf.t_mem <=> i IN ta.t_mem)) /\
  b+len <= next /\ regions_disjoint dst n b len /\
  b <= i /\ i < b+len /\ i IN tf.t_mem ==> i IN tn.t_mem
Proof
  strip_tac >>
  `i < next` by decide_tac >>
  `~(dst <= i /\ i < dst+n)` by (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!j. ~(dst <= j /\ j < dst+n) ==> _`
    (qspec_then `i` mp_tac) >>
  simp[]
QED

(* Allocation is observed below the pre-reserve frontier; the typed store is
   observed outside the destination.  Neither bound identifies the other. *)
Theorem ifexp_typed_reserve_store_kept:
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= k.cs_next_var /\
  (!x. not_fresh_at sm x ==>
    FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
  (!x. not_fresh_at k x ==>
    FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!i. ~(dst <= i /\ i < dst+n) ==> (i IN tf.t_mem <=> i IN ta.t_mem)) /\
  (!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    b+len <= s.vs_alloca_next /\ regions_disjoint dst n b len) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
    b+len <= s.vs_alloca_next /\ regions_disjoint dst n b len) ==>
  ghost_kept_at lo ce es sa Gi ti s0 Gf tf
Proof
  pure_rewrite_tac[ghost_kept_at_def] >> strip_tac >> conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at sm x /\ not_fresh_at k x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b len. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      drule_all_then assume_tac ifexp_typed_exterior_taint >>
      qpat_assum `!aid b len i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> i IN ti.t_mem`
        (drule_all_then ACCEPT_TAC)) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then assume_tac ifexp_typed_exterior_taint >>
  qpat_assum `!name b len i. local_region ce es.scopes s0 name b len /\ _ ==> i IN ti.t_mem`
    (drule_all_then ACCEPT_TAC)
QED
