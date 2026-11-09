(* Inverse clean-word writes and robust field transport. *)
Theory augAssignPtrFieldStore
Ancestors
  wordLoadStorePtr augAssignPtrStore robustCopyTransportPtr valueEncodingProps valueEncodingProofs
  venomMemProofs venomState list pred_set arithmetic typedCopyPtr bodyPtrDefs byte words
  stmtSimAssignAttr loweringSlice

Theorem memory_window_byte_agree[local]:
  mem_bytes_at off n m1 = mem_bytes_at off n m2 /\ j < n ==>
  mem_bytes_at (off+j) 1 m1 = mem_bytes_at (off+j) 1 m2
Proof
  strip_tac >>
  `EL j (mem_bytes_at off n m1) = EL j (mem_bytes_at off n m2)` by simp[] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem clean_mstore_restore_witness:
  mem_agree_outside (tainted DIFF {i | off <= i /\ i < off + 32})
    (mstore off w s).vs_memory m ==>
  ?u. mem_agree_outside tainted s.vs_memory u /\
      (!i. mem_bytes_at i 1 (mstore off w (s with vs_memory := u)).vs_memory =
           mem_bytes_at i 1 m)
Proof
  strip_tac >>
  qabbrev_tac `r = (s with vs_memory := m)` >>
  qabbrev_tac `u = (write_memory_with_expansion off (mem_bytes_at off 32 s.vs_memory) r).vs_memory` >>
  `mem_bytes_at off 32 u = mem_bytes_at off 32 s.vs_memory` by
    (qspecl_then [`off`, `mem_bytes_at off 32 s.vs_memory`, `r`]
       mp_tac write_memory_mem_bytes_at_same >> simp[Abbr `u`]) >>
  `!i. ~(off <= i /\ i < off + 32) ==>
    mem_bytes_at i 1 u = mem_bytes_at i 1 m` by
    (rpt strip_tac >> simp[Abbr `u`] >>
     irule EQ_TRANS >> qexists `mem_bytes_at i 1 r.vs_memory` >>
     conj_tac >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
     simp[Abbr `r`]) >>
  qexists `u` >> conj_tac
  >- (simp[mem_agree_outside_def] >> rpt strip_tac >>
      Cases_on `off <= i /\ i < off+32`
      >- (`i-off < 32 /\ off+(i-off) = i` by decide_tac >>
          drule_all memory_window_byte_agree >>
          simp[]) >>
      `i NOTIN (tainted DIFF {i | off <= i /\ i < off+32})` by simp[] >>
      mp_tac (Q.SPECL [`s`, `off`, `w`] mstore_memory_frame) >>
      fs[mem_agree_outside_def] >> metis_tac[]) >>
  gen_tac >> Cases_on `off <= i /\ i < off+32`
  >- (`i-off < 32 /\ off+(i-off) = i` by decide_tac >>
      `mem_bytes_at off 32 (mstore off w (s with vs_memory := u)).vs_memory =
       mem_bytes_at off 32 (mstore off w s).vs_memory` by
        (qspecl_then [`off`, `word_to_bytes w T`, `s`] mp_tac
           write_memory_mem_bytes_at_same >>
         qspecl_then [`off`, `word_to_bytes w T`, `s with vs_memory := u`] mp_tac
           write_memory_mem_bytes_at_same >>
         simp[byteTheory.LENGTH_word_to_bytes, mstore_eq_wmwe]) >>
      drule_all memory_window_byte_agree >>
      fs[mem_agree_outside_def]) >>
  `mem_bytes_at i 1 (mstore off w (s with vs_memory := u)).vs_memory =
   mem_bytes_at i 1 u` by
    (qspecl_then [`i`, `1`, `off`, `w`, `s with vs_memory := u`]
       mp_tac mstore_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
  simp[]
QED

Theorem memory_byte_agree_window:
  (!i. mem_bytes_at i 1 m1 = mem_bytes_at i 1 m2) ==>
  !off n. mem_bytes_at off n m1 = mem_bytes_at off n m2
Proof
  strip_tac >> rpt gen_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `off+x` mp_tac) >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem fields_in_memory_mstore_field_robust:
  fields_layout flds fs /\ struct_has_type fs vals /\
  fields_val_wf vals fs /\ ALOOKUP fs fld = SOME ftv /\
  type_memory_size ftv = 32 /\ word_value v /\
  (!m. mem_agree_outside tainted s.vs_memory m ==>
       fields_in_memory vals fs off m) ==>
  !m. mem_agree_outside
       (tainted DIFF {i | off + struct_field_offset flds fld <= i /\
                         i < off + struct_field_offset flds fld + 32})
       (mstore (off + struct_field_offset flds fld) (val_to_w256 v) s).vs_memory m ==>
      fields_in_memory (AFUPDKEY fld (K v) vals) fs off m
Proof
  rpt strip_tac >> drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `fields_in_memory vals fs off u` by metis_tac[] >>
  `fields_in_memory (AFUPDKEY fld (K v) vals) fs off
    (mstore (off + struct_field_offset flds fld) (val_to_w256 v)
      (s with vs_memory := u)).vs_memory` by
    (irule fields_in_memory_mstore_field >> simp[word_value_in_memory] >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule (cj 2 val_in_memory_mem_agree_proof) >>
  conj_tac
  >- (irule fields_val_wf_update >> goal_assum (drule_at Any) >>
      simp[word_value_wf]) >>
  goal_assum (drule_at Any) >>
  drule memory_byte_agree_window >> simp[]
QED
