(* Storage contracts over the roots observed by an execution. *)
Theory vyperStorageFootprint
Ancestors
  vyperStorageWritePreservation vyperStorageLayoutSafety vyperStorageBackend
  vyperValue vyperTyping vyperLookupStorage vyperStorage vyperStorageFrame
  vyperRuntimeAccounts vyperState extCallOracle
  list
Libs
  wordsLib

(* Keep natural root offsets until their no-wrap check has been made. *)
Definition storage_trace_regions_def:
  storage_trace_regions observations : (bool # bytes32 # type_value) list =
    FLAT (MAP (\observation. case observation of
      StorageRoot b offset tv => [(b,n2w offset,tv)] | _ => []) observations)
End

Definition storage_trace_locks_def:
  storage_trace_locks observations =
    FLAT (MAP (\observation. case observation of
      StorageLock slot => [slot] | _ => []) observations)
End

(* The lowering relations share one fixed observation horizon. *)
Definition storage_trace_horizon_def:
  storage_trace_horizon observations =
    (storage_trace_regions observations, storage_trace_locks observations)
End

Definition storage_roots_fit_def:
  storage_roots_fit observations <=>
    EVERY (\observation. case observation of
      StorageRoot b offset tv => offset + type_slot_size tv <= dimword(:256)
    | StorageLock slot => slot + 1 <= dimword(:256)
    | _ => T) observations
End

(* A lock word is live even when no typed transient root covers it. *)
Definition storage_locks_separated_def:
  storage_locks_separated regions locks <=>
    !slot tv lock. MEM (T,slot,tv) regions /\ MEM lock locks ==>
      ranges_disjoint (w2n slot) (type_slot_size tv) lock 1
End

Theorem storage_trace_regions_append[simp]:
  storage_trace_regions (xs ++ ys) =
    storage_trace_regions xs ++ storage_trace_regions ys
Proof
  simp[storage_trace_regions_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem storage_trace_locks_append[simp]:
  storage_trace_locks (xs ++ ys) =
    storage_trace_locks xs ++ storage_trace_locks ys
Proof
  simp[storage_trace_locks_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem storage_roots_fit_append[simp]:
  storage_roots_fit (xs ++ ys) <=> storage_roots_fit xs /\ storage_roots_fit ys
Proof
  simp[storage_roots_fit_def, EVERY_APPEND]
QED

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

(* Only backend snapshots actually adopted by the execution need to decode. *)
Definition storage_trace_backends_well_formed_def:
  storage_trace_backends_well_formed cx regions observations <=>
    EVERY (\observation. case observation of
      StorageBackend accounts transient =>
        storage_well_formed_on cx
          (empty_state with <|accounts := accounts; tStorage := transient|>) regions
    | _ => T) observations
End

(* Finite execution obligations are inherited by every observed prefix. *)
Definition storage_observations_ok_def:
  storage_observations_ok cx H observations <=>
    EVERY (\region. MEM region (FST H)) (storage_trace_regions observations) /\
    EVERY (\slot. MEM slot (SND H)) (storage_trace_locks observations) /\
    storage_roots_fit observations /\
    storage_trace_backends_well_formed cx (FST H) observations /\
    EVERY (\observation. case observation of
      StorageOutcome rq outcome =>
        LENGTH outcome.co_returnData < dimword(:256) /\
        (~rq.cr_static /\ (outcome.co_success \/ rq.cr_kind <> MessageCall) ==>
         accounts_runtime_well_typed outcome.co_accounts)
    | StorageBackend accounts transient => accounts_runtime_well_typed accounts
    | _ => T) observations
End

Theorem storage_well_formed_on_backends:
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage ==>
  (storage_well_formed_on cx st' regions <=>
   storage_well_formed_on cx st regions)
Proof
  strip_tac >>
  `!b. get_storage cx st' b = get_storage cx st b` by
    (Cases_on `b` >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

Theorem storage_trace_backends_well_formed_append[simp]:
  storage_trace_backends_well_formed cx regions (xs ++ ys) <=>
    storage_trace_backends_well_formed cx regions xs /\
    storage_trace_backends_well_formed cx regions ys
Proof
  simp[storage_trace_backends_well_formed_def, EVERY_APPEND]
QED

Theorem storage_observations_ok_append[simp]:
  storage_observations_ok cx H (xs ++ ys) <=>
    storage_observations_ok cx H xs /\ storage_observations_ok cx H ys
Proof
  simp[storage_observations_ok_def, EVERY_APPEND,
       AC CONJ_ASSOC CONJ_COMM]
QED

Theorem storage_trace_backends_well_formed_prefix:
  storage_trace_backends_well_formed cx (rs ++ ss) (xs ++ ys) ==>
  storage_trace_backends_well_formed cx rs xs
Proof
  simp[storage_trace_backends_well_formed_append] >> strip_tac >>
  `!st. storage_well_formed_on cx st (rs ++ ss) ==>
         storage_well_formed_on cx st rs` by
    (simp[storage_well_formed_on_def, MEM_APPEND] >> metis_tac[]) >>
  gvs[storage_trace_backends_well_formed_def, EVERY_MEM] >>
  rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `observation` >> simp[]
QED

(* A selected full trace validates the smaller horizons of its prefixes. *)
Theorem storage_observed_horizon_prefix:
  regions_consistent (storage_trace_regions (xs ++ ys)) /\
  storage_locks_separated (storage_trace_regions (xs ++ ys))
    (storage_trace_locks (xs ++ ys)) /\
  storage_well_formed_on cx st (storage_trace_regions (xs ++ ys)) /\
  storage_observations_ok cx (storage_trace_horizon (xs ++ ys)) (xs ++ ys) ==>
  regions_consistent (storage_trace_regions xs) /\
  storage_locks_separated (storage_trace_regions xs) (storage_trace_locks xs) /\
  storage_well_formed_on cx st (storage_trace_regions xs) /\
  storage_observations_ok cx (storage_trace_horizon xs) xs
Proof
  strip_tac >>
  conj_tac
  >- (qpat_x_assum `regions_consistent _` mp_tac >>
      simp[regions_consistent_def, MEM_APPEND] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `storage_locks_separated _ _` mp_tac >>
      simp[storage_locks_separated_def, MEM_APPEND] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
      simp[storage_well_formed_on_def, MEM_APPEND] >> metis_tac[]) >>
  qpat_x_assum `storage_observations_ok _ _ _` mp_tac >>
  simp[storage_observations_ok_def, storage_trace_horizon_def,
       EVERY_APPEND, EVERY_MEM] >>
  strip_tac >>
  irule storage_trace_backends_well_formed_prefix >>
  qexistsl [`storage_trace_regions ys`, `ys`] >> simp[]
QED

(* Intrinsic goodness uses exactly the roots of this observed prefix. *)
Definition storage_trace_domain_def:
  storage_trace_domain cx st observations <=>
    regions_consistent (storage_trace_regions observations) /\
    storage_locks_separated (storage_trace_regions observations)
      (storage_trace_locks observations) /\
    storage_well_formed_on cx st (storage_trace_regions observations) /\
    storage_observations_ok cx (storage_trace_horizon observations) observations
End

Theorem storage_trace_domain_prefix:
  storage_trace_domain cx st (xs ++ ys) ==> storage_trace_domain cx st xs
Proof
  REWRITE_TAC[storage_trace_domain_def] >>
  MATCH_ACCEPT_TAC storage_observed_horizon_prefix
QED

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

(* The interpreter records both encodings as the same physical typed leaf. *)
Theorem hashmap_encoding_alias_trace:
  (SND (extend_place cx
    (HashMapRef F base_slot kt (Type (BaseT (UintT 256))))
    (ValueSubscript (IntV 0)) empty_state)).storage_trace =
      [StorageRoot F
        (w2n (hashmap_slot base_slot (encode_hashmap_key kt (IntV 0))))
        (BaseTV (UintT 256))] /\
  (SND (extend_place cx
    (HashMapRef F base_slot kt (Type (BaseT (UintT 256))))
    (ValueSubscript (IntV (&dimword(:256)))) empty_state)).storage_trace =
      [StorageRoot F
        (w2n (hashmap_slot base_slot (encode_hashmap_key kt (IntV 0))))
        (BaseTV (UintT 256))]
Proof
  simp[extend_place_def, evaluate_type_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, record_storage_event_def,
       empty_state_def, encode_hashmap_key_def, integer_wordTheory.i2w_pos,
       wordsTheory.n2w_dimword]
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

(* Converting a layout offset to a word must not hide its overflow. *)
Theorem natural_root_wrap_rejected:
  ~storage_roots_fit [StorageRoot F (dimword(:256)) (BaseTV (UintT 256))] /\
  storage_trace_regions [StorageRoot F (dimword(:256)) (BaseTV (UintT 256))] =
    [(F,0w,BaseTV (UintT 256))]
Proof
  simp[storage_roots_fit_def, storage_trace_regions_def,
       type_slot_size_def, wordsTheory.n2w_dimword]
QED
