(* Restoring an overwritten field recovers the old robust struct witness. *)
Theory assignBasePtrFieldRobust
Ancestors stmtSimAssignAttr stmtSimDeclStore exprSimFieldLayout annAssignPtrStore bodyPtrDefs valueEncoding
  valueEncodingProps valueEncodingProofs venomMemProofs venomState
  venomExecSemantics exprSimMemoryTransport representationCleanPtr pred_set list arithmetic

Theorem assign_base_field_restore_witness:
  !dirty s off wd mem.
    mem_agree_outside (dirty DIFF {i | off <= i /\ i < off+32})
      (mstore off wd s).vs_memory mem ==>
    ?mix. mem_agree_outside dirty s.vs_memory mix /\
      (!i. ~(off <= i /\ i < off+32) ==>
        mem_bytes_at i 1 mix = mem_bytes_at i 1 mem)
Proof
  rpt strip_tac >>
  qexists_tac `(write_memory_with_expansion off
    (mem_bytes_at off 32 s.vs_memory) (s with vs_memory := mem)).vs_memory` >>
  conj_tac
  >- (simp[mem_agree_outside_def] >> rpt strip_tac >>
      Cases_on `off <= i /\ i < off+32`
      >- (`mem_bytes_at off 32
            (write_memory_with_expansion off (mem_bytes_at off 32 s.vs_memory)
              (s with vs_memory := mem)).vs_memory =
           mem_bytes_at off 32 s.vs_memory` by
            (qspecl_then [`off`, `mem_bytes_at off 32 s.vs_memory`,
              `s with vs_memory := mem`] mp_tac write_memory_mem_bytes_at_same >> simp[]) >>
          sym_tac >> irule mem_bytes_at_eq_byte >>
          goal_assum (drule_at Any) >> decide_tac) >>
      `i+1 <= off \/ off+32 <= i` by decide_tac >>
      simp[write_memory_mem_bytes_at_disjoint] >>
      fs[mem_agree_outside_def] >>
      first_x_assum (qspec_then `i` mp_tac) >>
      simp[mstore_mem_bytes_at_disjoint]) >>
  rpt strip_tac >>
  `i+1 <= off \/ off+32 <= i` by decide_tac >>
  simp[write_memory_mem_bytes_at_disjoint]
QED

Theorem assign_base_field_restored_store_window:
  !dirty s off wd mem mix base n.
    mem_agree_outside (dirty DIFF {i | off <= i /\ i < off+32})
      (mstore off wd s).vs_memory mem /\
    (!i. ~(off <= i /\ i < off+32) ==>
      mem_bytes_at i 1 mix = mem_bytes_at i 1 mem) ==>
    mem_bytes_at base n (mstore off wd (s with vs_memory := mix)).vs_memory =
      mem_bytes_at base n mem
Proof
  rpt strip_tac >>
  `!i. mem_bytes_at i 1 (mstore off wd (s with vs_memory := mix)).vs_memory =
       mem_bytes_at i 1 mem` by
    (gen_tac >> Cases_on `off <= i /\ i < off+32`
     >- (`mem_bytes_at off 32 (mstore off wd (s with vs_memory := mix)).vs_memory =
          mem_bytes_at off 32 (mstore off wd s).vs_memory` by
           simp[mem_bytes_at_mstore_same] >>
         `mem_bytes_at i 1 (mstore off wd (s with vs_memory := mix)).vs_memory =
          mem_bytes_at i 1 (mstore off wd s).vs_memory` by
           (irule mem_bytes_at_eq_byte >> goal_assum (drule_at Any) >> decide_tac) >>
         fs[mem_agree_outside_def]) >>
     `i+1 <= off \/ off+32 <= i` by decide_tac >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `EL k (mem_bytes_at addr n mem)` >>
  first_x_assum (qspec_then `addr+k` mp_tac) >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem assign_base_field_update_robust:
  !flds fs vals b s fld ftv v etv dirty.
    fields_layout flds fs /\ struct_has_type fs vals /\
    fields_val_wf vals fs /\ ALOOKUP fs fld = SOME ftv /\
    store_lays_out etv ftv v /\
    (!mem. mem_agree_outside dirty s.vs_memory mem ==>
      val_in_memory (StructTV fs) (StructV vals) b mem) ==>
    !mem. mem_agree_outside
      (dirty DIFF {i | b + struct_field_offset flds fld <= i /\
                      i < b + struct_field_offset flds fld + 32})
      (mstore (b + struct_field_offset flds fld)
        (typed_val_to_w256 etv v) s).vs_memory mem ==>
      val_in_memory (StructTV fs) (StructV (AFUPDKEY fld (K v) vals)) b mem
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule assign_base_field_restore_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory (StructTV fs) (StructV vals) b mix` by metis_tac[] >>
  `val_in_memory (StructTV fs) (StructV (AFUPDKEY fld (K v) vals)) b
    (mstore (b + struct_field_offset flds fld)
      (typed_val_to_w256 etv v) (s with vs_memory := mix)).vs_memory` by
    (rewrite_tac[val_in_memory_struct] >>
     irule fields_in_memory_mstore_field >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[val_in_memory_struct, store_lays_out_def]) >>
  irule val_in_memory_mem_agree >> conj_tac
  >- (simp[val_wf_def] >> irule fields_val_wf_update >>
      goal_assum (drule_at Any) >> gvs[store_lays_out_def]) >>
  qexistsl_tac [`type_memory_size (StructTV fs)`,
    `(mstore (b + struct_field_offset flds fld)
      (typed_val_to_w256 etv v) (s with vs_memory := mix)).vs_memory`] >>
  simp[] >> irule assign_base_field_restored_store_window >>
  goal_assum (drule_at Any) >> qexists_tac `dirty` >> simp[ADD_ASSOC]
QED

Theorem assign_base_field_store_exterior:
  !flds fs fld ftv b n s wd dirty.
    fields_layout flds fs /\ ALOOKUP fs fld = SOME ftv /\
    type_memory_size ftv = 32 /\ type_memory_size (StructTV fs) <= n ==>
    !i. ~(b <= i /\ i < b+n) ==>
      mem_bytes_at i 1
        (mstore (b + struct_field_offset flds fld) wd s).vs_memory =
        mem_bytes_at i 1 s.vs_memory /\
      (i IN (dirty DIFF {j | b + struct_field_offset flds fld <= j /\
                            j < b + struct_field_offset flds fld + 32}) <=>
       i IN dirty)
Proof
  rpt gen_tac >> strip_tac >>
  `struct_field_offset flds fld + 32 <= type_memory_size_fields fs` by
    metis_tac[struct_field_offset_le] >>
  fs[type_memory_size_def] >> gen_tac >> disch_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
