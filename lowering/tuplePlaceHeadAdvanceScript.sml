(* Structural reconstruction at one chosen store endpoint. *)
Theory tuplePlaceHeadAdvance
Ancestors
  tuplePlaceHead tuplePlacePointerReady tuplePlaceBranchReady freshWrites

Theorem tuple_place_snapshot_endpoint:
  tuple_place_snapshot cenv cx es lo hi tys ltys ltvs w s /\ hi <= hi' /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv es'.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) ==>
  tuple_place_snapshot cenv cx es' lo hi' tys ltys ltvs w t
Proof
  rw[tuplePlacePrefixCertTheory.tuple_place_snapshot_def] >> simp[]
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  qexistsl [`n`, `b`, `sz`] >> gvs[]
QED

Theorem tuple_place_endpoint_local_regions:
  local_ptrs_reserved cenv cs /\
  (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x s) /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  (!n b sz. local_region cenv es'.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> rpt gen_tac >>
  drule_all exprSimCopyTheory.copy_buffer_local_region_frame >>
  disch_then (qspecl_then [`es'.scopes`, `n`, `b`, `sz`] mp_tac) >>
  drule tupleMemoryFrameTheory.local_region_scopes_domain >> metis_tac[]
QED

Theorem tuple_place_head_advance:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s /\
  i < LENGTH ltys /\ sp.cs_next_var <= sb.cs_next_var /\
  sp.cs_next_id <= sb.cs_next_id /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv ff.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s) /\
  stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!j. SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
    val_in_memory (EL j ltvs) (EL j vs)
      (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory) ==>
  tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t
Proof
  strip_tac >>
  `tuple_place_snapshot cenv cx ff lo sb.cs_next_id tys ltys ltvs w t` by
    (irule tuple_place_snapshot_endpoint >>
     fs[tuple_place_head_def] >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  fs[tuple_place_head_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> conj_tac
  >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt strip_tac >>
  `MEM (EL j elems) elems` by (irule listTheory.EL_MEM >> simp[]) >>
  `?x. EL j elems = Var x` by gvs[listTheory.EVERY_MEM] >>
  `i <= j` by simp[] >>
  `not_fresh_at sp x` by metis_tac[] >>
  qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `j` mp_tac) >>
  simp[venomStateTheory.eval_operand_def]
QED
