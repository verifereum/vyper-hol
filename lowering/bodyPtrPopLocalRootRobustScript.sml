(* Restore the pre-store word in an arbitrary admissible final memory.
   This reuses the general clean-store inverse, not a new memory definition. *)
Theory bodyPtrPopLocalRootRobust
Ancestors
  bodyPtrPopLocalRootEntry augAssignPtrFieldStore exprSimPop exprSimAggregateEncoding
  valueEncoding valueEncodingProps valueEncodingProofs
  bodyPtrDefs venomState venomMemProofs words list rich_list pred_set arithmetic

Theorem pop_local_robust_shortened:
  vs <> [] /\ elems_val_wf vs tv /\ LENGTH vs <= cap /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) ==>
  !mem. mem_agree_outside (dirty DIFF {i | off <= i /\ i < off+32})
    (mstore off (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (FRONT vs))) off mem
Proof
  rpt strip_tac >> drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off u` by metis_tac[] >>
  `elems_in_memory vs (off+32) tv u` by gvs[val_in_memory_def] >>
  `elems_in_memory vs (off+32) tv
    (mstore off (n2w (LENGTH vs-1)) (s with vs_memory := u)).vs_memory` by
    (irule elems_in_memory_mstore_before >> simp[]) >>
  `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV (FRONT vs))) off
    (mstore off (n2w (LENGTH vs-1)) (s with vs_memory := u)).vs_memory` by
    (simp[val_in_memory_def, LENGTH_FRONT, PRE_SUB1,
          mem_word_at_eq_mload, mload_mstore_same_proof] >>
     metis_tac[elems_in_memory_FRONT]) >>
  irule (cj 1 val_in_memory_mem_agree_proof) >>
  conj_tac >- (simp[val_wf_def, LENGTH_FRONT] >> metis_tac[elems_val_wf_FRONT]) >>
  goal_assum (drule_at Any) >> drule memory_byte_agree_window >> simp[]
QED

Theorem pop_local_robust_last:
  vs <> [] /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) ==>
  !mem. mem_agree_outside (dirty DIFF {i | off <= i /\ i < off+32})
    (mstore off (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory tv (LAST vs) (off+32+(LENGTH vs-1)*type_memory_size tv) mem
Proof
  rpt strip_tac >> drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off u` by metis_tac[] >>
  `elems_in_memory vs (off+32) tv u` by gvs[val_in_memory_def] >>
  `elems_in_memory vs (off+32) tv
    (mstore off (n2w (LENGTH vs-1)) (s with vs_memory := u)).vs_memory` by
    (irule elems_in_memory_mstore_before >> simp[]) >>
  `LENGTH vs-1 < LENGTH vs /\ LAST vs = EL (LENGTH vs-1) vs` by
    (Cases_on `vs` >> gvs[LAST_EL, PRE_SUB1]) >>
  `val_wf tv (LAST vs)` by metis_tac[elems_val_wf_EL] >>
  `val_in_memory tv (LAST vs) (off+32+(LENGTH vs-1)*type_memory_size tv)
    (mstore off (n2w (LENGTH vs-1)) (s with vs_memory := u)).vs_memory` by
    metis_tac[elems_in_memory_EL] >>
  irule (cj 1 val_in_memory_mem_agree_proof) >>
  conj_tac >- simp[] >>
  qexists_tac `(mstore off (n2w (LENGTH vs-1)) (s with vs_memory := u)).vs_memory` >>
  drule memory_byte_agree_window >> simp[]
QED
