(* Shared representation boundaries for bytestring copy effects. *)
Theory typedCopyRobustTransportPtr
Ancestors typedCopyPtr representationCleanPtr valueCopyBytes valueEncodingProps
  robustCopyTransportPtr loweringPosts exprSimDefs exprSimProps venomMemProofs bodyPtrDefs list arithmetic
  exprSimBufferStore valueEncodingProofs

Theorem robust_representation_exterior_frame:
  !tn tn' mem mem' dst n.
    (!i. ~(dst <= i /\ i < dst+n) ==>
       mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) ==>
    (!i. ~(dst <= i /\ i < dst+n) ==> (i IN tn' <=> i IN tn)) ==>
    !ft fv p. val_wf ft fv ==>
    (p + type_memory_size ft <= dst \/ dst+n <= p) ==>
    (!m. mem_agree_outside tn mem m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory ft fv p m
Proof
  rpt strip_tac >> drule val_footprint_le >> disch_tac >>
  (irule robust_val_in_memory_exterior_frame >>
   conj_tac >- simp[] >>
   qexistsl_tac [`mem`, `mem'`, `tn`, `tn'`,
     `{i | dst <= i /\ i < dst+n}`] >>
   simp[] >> rpt strip_tac >> decide_tac)
QED

Theorem clean_copied_window:
  !tn tn' s sf a b n off k m.
    sf.vs_memory = (mcopy b a n s).vs_memory /\
    (!i. i < n ==> (b+i IN tn' <=> a+i IN tn)) /\
    (!i. a+off <= i /\ i < a+off+k ==> i NOTIN tn) /\
    off+k <= n /\ mem_agree_outside tn' sf.vs_memory m ==>
    mem_bytes_at (b+off) k m = mem_bytes_at (a+off) k s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at (b+off) k m = mem_bytes_at (b+off) k sf.vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < k` >>
     `b+off+j NOTIN tn'` by
       (`off+j < n /\ a+off <= a+(off+j) /\ a+(off+j) < a+off+k`
          by decide_tac >> metis_tac[arithmeticTheory.ADD_ASSOC]) >>
     `mem_bytes_at (b+off+j) 1 sf.vs_memory = mem_bytes_at (b+off+j) 1 m`
       by (fs[mem_agree_outside_def] >> metis_tac[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  asm_rewrite_tac[] >> irule buffer_mcopy_window >> simp[]
QED
