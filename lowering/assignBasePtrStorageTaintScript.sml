(* Robust represented values cannot taint live encoded storage bytes. *)
Theory assignBasePtrStorageTaint
Ancestors fullStoreCopyEndpoint representationCleanPtr storageCopyLive valueEncodingProofs
  bodyPtrDefs compileEnv loweringStateRelDefs valueEncoding vyperValue vyperTyping
  venomState list words arithmetic accountsRelProps vyperStorageFootprint
  assignBasePtrStorageFrame pred_set


(* The unwritten capacity tail of a bytestring is dead based on the actual
   length word. This does not require clearing or copying that tail. *)
Theorem bytestring_storage_tail_dead:
  !tv max final base x b.
    (tv = BaseTV (BytesT (Dynamic max)) \/ tv = BaseTV (StringT max)) /\
    base < x /\ x <= base + word_size max /\ b < 32 /\
    w2n (lookup_storage (n2w base) final) <= 32 * (x - (base + 1)) + b ==>
    dead_bytes final base tv x b
Proof
  rpt strip_tac >> gvs[dead_bytes_def, dyn_bytes_dead_def]
QED

(* The copy may leave old taint in an unwritten destination tail. Such taint
   needs tail deadness, not an unsupported full-capacity overwrite equation. *)
Theorem storage_copy_taint_at_endpoint:
  !cx tr mid n subs k tv v writes st final ta mem off count old new.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    count <= type_slot_size tv /\
    (!i. i < type_slot_size tv ==> MEM i (MAP FST writes)) /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
       ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
       EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
       EL c (word_to_bytes (lookup_storage (n2w i)
         (apply_writes k writes st)) T)) /\
    (!i. i < dimword (:256) /\
         ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
         lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
    (!q b. (q,b) IN old ==> storage_dead H tr st (w2n q) b) /\
    (!q b. (q,b) IN old /\ w2n k + count <= w2n q /\
       w2n q < w2n k + type_slot_size tv ==>
       dead_bytes final (w2n k) tv (w2n q) b) /\
    (!q b. (q,b) IN new ==>
       ((q,b) IN old /\ ~(w2n k <= w2n q /\ w2n q < w2n k + count)) \/
       (?j. w2n q = w2n k+j /\ j < count /\ b < 32 /\
            off + 32*j + b IN ta)) ==>
    !q b. (q,b) IN new ==> storage_dead H tr final (w2n q) b
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q b. (q,b) IN new ==> _` drule >> strip_tac
  >- (Cases_on `w2n k <= w2n q /\ w2n q < w2n k + type_slot_size tv`
      >- (`dead_bytes final (w2n k) tv (w2n q) b` by
            (first_x_assum irule >> simp[] >> decide_tac) >>
          drule_all declared_region_dead_storage_dead >> simp[]) >>
      irule storage_dead_endpoint_outside >>
      qexistsl_tac [`k`, `mid`, `n`, `st`, `subs`, `tv`] >>
      simp[]) >>
  `j < type_slot_size tv` by decide_tac >>
  `MEM j (MAP FST writes)` by
    (qpat_x_assum `!i. i < type_slot_size tv ==> MEM i (MAP FST writes)`
       irule >> decide_tac) >>
  drule_all robust_memory_storage_dead_at_endpoint >> simp[]
QED

