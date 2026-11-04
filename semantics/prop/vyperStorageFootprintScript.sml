(* Finite-region prototype for execution-relative storage preservation. *)
Theory vyperStorageFootprint
Ancestors
  vyperStorageWritePreservation vyperStorageLayoutSafety vyperStorageBackend
  vyperValue vyperTyping vyperLookupStorage vyperStorage vyperStorageFrame
Libs
  wordsLib

(* Physical equality permits the aliases computed by the storage semantics. *)
Definition regions_consistent_def:
  regions_consistent (regions : (bool # bytes32 # type_value) list) <=>
    (!b slot tv. MEM (b,slot,tv) regions ==>
       w2n slot + type_slot_size tv <= dimword(:256)) /\
    (!b slot1 tv1 slot2 tv2.
       MEM (b,slot1,tv1) regions /\ MEM (b,slot2,tv2) regions ==>
       (slot1,tv1) = (slot2,tv2) \/
       ranges_disjoint (w2n slot1) (type_slot_size tv1)
                       (w2n slot2) (type_slot_size tv2))
End

(* The context selects the current contract's storage address. *)
Definition storage_well_formed_on_def:
  storage_well_formed_on cx st regions <=>
    !b slot tv. MEM (b,slot,tv) regions ==>
      slots_in_range (get_storage cx st b) (w2n slot) tv
End

(* Whole-leaf writes cover nested maps and reconstructed struct/array leaves. *)
Theorem typed_write_preserves_storage_well_formed_on:
  regions_consistent regions /\
  storage_well_formed_on cx st regions /\
  MEM (b,slot,tv) regions /\
  value_has_type tv v /\ well_formed_type_value tv /\
  write_storage_slot cx b slot tv v st = (INL (),st') ==>
  storage_well_formed_on cx st' regions
Proof
  rw[storage_well_formed_on_def] >>
  Cases_on `(b,slot,tv) = (b',slot',tv')`
  >- (gvs[] >> irule typed_write_storage_slot_establishes_region >>
      metis_tac[]) >>
  irule typed_write_storage_slot_preserves_disjoint_region >>
  qexistsl [`b`, `slot`, `st`, `tv`, `v`] >>
  fs[regions_consistent_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Structural writes reconstruct their root and frame all other roots. *)
Theorem contained_write_preserves_storage_well_formed_on:
  regions_consistent regions /\
  storage_well_formed_on cx st regions /\
  MEM (b,root_slot,root_tv) regions /\
  value_has_type wr_tv v /\
  write_storage_slot cx b wr_slot wr_tv v st = (INL (),st') /\
  w2n root_slot <= w2n wr_slot /\
  w2n wr_slot + type_slot_size wr_tv <=
    w2n root_slot + type_slot_size root_tv /\
  slots_in_range (get_storage cx st' b) (w2n root_slot) root_tv ==>
  storage_well_formed_on cx st' regions
Proof
  rw[storage_well_formed_on_def] >>
  Cases_on `(b,root_slot,root_tv) = (b',slot,tv)` >- gvs[] >>
  irule typed_write_storage_slot_preserves_disjoint_region >>
  qexistsl [`b`, `wr_slot`, `st`, `wr_tv`, `v`] >>
  fs[regions_consistent_def] >> strip_tac >> gvs[] >>
  `ranges_disjoint (w2n root_slot) (type_slot_size root_tv)
                   (w2n slot) (type_slot_size tv)` by metis_tac[] >>
  fs[ranges_disjoint_def] >> decide_tac
QED

(* Even two logical paths with the same physical leaf satisfy the condition. *)
Theorem uint256_leaf_alias_consistent:
  regions_consistent [(F,slot,BaseTV (UintT 256));
                      (F,slot,BaseTV (UintT 256))]
Proof
  simp[regions_consistent_def, type_slot_size_def] >>
  mp_tac (Q.ISPEC `slot:bytes32` wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def]
QED

Theorem uint256_leaf_well_formed:
  storage_well_formed_on cx st [(b,slot,BaseTV (UintT 256))]
Proof
  simp[storage_well_formed_on_def, slots_in_range_def,
       word_slot_canonical_def, encode_base_to_slot_def,
       decode_base_from_slot_def, truncate_unsigned_def,
       integer_wordTheory.i2w_pos] >>
  mp_tac (Q.ISPEC `read_slot (get_storage cx st b) (w2n slot)`
    wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def, arithmeticTheory.MOD_LESS]
QED

(* The encoding alias behind the global predicate's failure is accepted. *)
Theorem hashmap_encoding_alias_consistent:
  regions_consistent
    [(F,hashmap_slot base_slot (encode_hashmap_key kt (IntV 0)),
        BaseTV (UintT 256));
     (F,hashmap_slot base_slot
          (encode_hashmap_key kt (IntV (&dimword(:256)))),
        BaseTV (UintT 256))]
Proof
  simp[encode_hashmap_key_def, integer_wordTheory.i2w_pos,
       wordsTheory.n2w_dimword, uint256_leaf_alias_consistent]
QED

(* A finite condition still rejects partial overlap and address-space wrap. *)
Theorem partial_overlap_and_wrap_rejected:
  ~regions_consistent [(F,0w,ArrayTV (BaseTV (UintT 256)) (Fixed 2));
                       (F,1w,BaseTV (UintT 256))] /\
  ~regions_consistent [(F,-1w,ArrayTV (BaseTV (UintT 256)) (Fixed 2))]
Proof
  simp[regions_consistent_def, type_slot_size_def, ranges_disjoint_def,
       wordsTheory.dimword_def] >>
  disj2_tac >>
  qexistsl [`F`, `0w`, `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`,
            `1w`, `BaseTV (UintT 256)`] >>
  simp[type_slot_size_def]
QED
