Theory bodyPtrPopSpatialSplit
Ancestors bodyPtrPopHistoryStore normalizationPrefixPtr abiStaticAggregateProps
  representationCleanPtr valueEncoding
  valueEncodingProps exprSimMemoryTransport pred_set list bodyPtrDefs venomMemProofs
  bodyPtrPopMemoryHeader exprSimAggregateEncoding robustCopyTransportPtr valueEncodingProofs typedCopyPtr exprSimPop

Theorem pop_clean_word_agreement[local]:
  (!i. p <= i /\ i < p + 32 ==> i NOTIN dirty) /\
  mem_agree_outside dirty mem mem' ==>
  mem_word_at p mem' = mem_word_at p mem
Proof
  strip_tac >> simp[mem_word_at_bytes] >> AP_TERM_TAC >>
  irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
  `p + x NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (p+x) 1 mem = mem_bytes_at (p+x) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

(* The shortened owner and the removed child share the same exact store
   endpoint; no historical-owner compatibility is assumed here. *)
Theorem pop_shortened_owner_robust_store_nat:
  vs <> [] /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (p) mem) /\
  t = ((mstore (p) (n2w (LENGTH vs - 1)) s)
    with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (FRONT vs)))
      (p) mem
Proof
  strip_tac >>
  `!i. p <= i /\ i < p + 32 ==> i NOTIN tn.t_mem` by
    (`!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        mem_word_at p mem = (n2w (LENGTH vs):bytes32)` by
       (rpt strip_tac >>
        qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
        simp[val_in_memory_def]) >>
     drule robust_mem_word_at_clean >> simp[]) >>
  `mem_agree_outside {i | p <= i /\ i < p + 32}
     t.vs_memory s.vs_memory` by
    (gvs[] >> irule mstore_memory_frame) >>
  ho_match_mp_tac robust_dynarray_assemble >> conj_tac
  >- (rpt strip_tac >>
      `mem_word_at (p) mem = mem_word_at (p) t.vs_memory` by
        (irule pop_clean_word_agreement >> goal_assum (drule_at Any) >> simp[]) >>
      gvs[listTheory.LENGTH_FRONT, valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  rpt strip_tac >>
  `j < LENGTH vs` by (gvs[listTheory.LENGTH_FRONT] >> decide_tac) >>
  `EL j (FRONT vs) = EL j vs` by
    metis_tac[rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >> simp[] >>
  `val_wf tv (EL j vs)` by (irule elems_val_wf_EL >> simp[] >>
    goal_assum (drule_at Any)) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory tv (EL j vs) (p + 32 + j * type_memory_size tv) m` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[valueEncodingTheory.val_in_memory_def] >> strip_tac >>
     drule elems_in_memory_EL >>
     disch_then (qspec_then `j` mp_tac) >> simp[]) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn.t_mem`,
    `{i | p <= i /\ i < p + 32}`] >>
  simp[] >> gvs[mem_agree_outside_def] >> first_assum ACCEPT_TAC
QED

(* Machine-facing specialization; the spatial proof uses natural addresses. *)
Theorem pop_shortened_owner_robust_store:
  vs <> [] /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  t = ((mstore (w2n a) (n2w (LENGTH vs - 1)) s)
    with vs_inst_idx := SUC s.vs_inst_idx) ==>
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (FRONT vs)))
      (w2n a) mem
Proof
  rpt strip_tac >> irule pop_shortened_owner_robust_store_nat >>
  simp[] >> qexistsl_tac [`s`, `tn`] >> gvs[]
QED
