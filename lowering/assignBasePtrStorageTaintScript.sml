(* Robust represented values cannot taint live encoded storage bytes. *)
Theory assignBasePtrStorageTaint
Ancestors representationCleanPtr storageCopyLive valueEncodingProofs
  bodyPtrDefs compileEnv valueEncoding vyperValue vyperTyping
  venomState list words arithmetic accountsRelProps
  assignBasePtrStorageFrame pred_set

Theorem robust_mem_word_byte_clean:
  !ta mem a b c.
    b < 32 /\
    (!m. mem_agree_outside ta mem m ==>
      EL b (word_to_bytes (mem_word_at a m) T) = c) ==>
    a+b NOTIN ta
Proof
  rpt strip_tac >>
  `!m. mem_agree_outside ta mem m ==>
       mem_bytes_at (a+b) 1 m = [c]` by
    (rpt strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
     rpt strip_tac >>
     first_x_assum drule >>
     simp[GSYM mem_bytes_at_word, EL_mem_bytes_at]) >>
  drule robust_mem_bytes_at_clean >> simp[] >>
  qexists_tac `a+b` >> simp[]
QED

Theorem robust_memory_taint_dead:
  !tv v writes k st ta mem off j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    j < type_slot_size tv /\ b < 32 /\ off + 32*j + b IN ta ==>
    dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `!m. mem_agree_outside ta mem m ==>
    EL b (word_to_bytes (mem_word_at (off+32*j) m) T) =
    EL b (word_to_bytes (lookup_storage (n2w (w2n k+j))
      (apply_writes k writes st)) T)` by
    (rpt strip_tac >> sym_tac >> irule encode_value_memory_live >>
     metis_tac[]) >>
  drule_all robust_mem_word_byte_clean >> simp[]
QED

(* Relate deadness to the actual endpoint, not just the canonical encoding. *)
Theorem robust_memory_taint_dead_at_endpoint:
  !tv v writes k st final ta mem off j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
       ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
       EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
       EL c (word_to_bytes (lookup_storage (n2w i)
         (apply_writes k writes st)) T)) /\
    j < type_slot_size tv /\ b < 32 /\ off + 32*j + b IN ta ==>
    dead_bytes final (w2n k) tv (w2n k+j) b
Proof
  rpt strip_tac >>
  `dead_bytes final (w2n k) tv (w2n k+j) b <=>
   dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b` by
    (irule (cj 1 dead_bytes_live_frame) >> simp[]) >>
  metis_tac[robust_memory_taint_dead]
QED

(* A region-local dead byte is globally dead when declared regions separate. *)
Theorem declared_region_dead_storage_dead:
  !cx tr mid n subs k tv final x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (k,tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    dead_bytes final (w2n k) tv x b ==>
    storage_dead cx tr final x b
Proof
  rpt strip_tac >> simp[storage_dead_def] >>
  qexistsl_tac [`mid`, `n`, `subs`, `k`, `tv`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[] >> goal_assum (drule_at Any)
QED

Theorem robust_memory_storage_dead_at_endpoint:
  !cx tr mid n subs tv v writes k st final ta mem off j b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (k,tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
       ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
       EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
       EL c (word_to_bytes (lookup_storage (n2w i)
         (apply_writes k writes st)) T)) /\
    j < type_slot_size tv /\ b < 32 /\ off + 32*j + b IN ta ==>
    storage_dead cx tr final (w2n k+j) b
Proof
  rpt strip_tac >> simp[storage_dead_def] >>
  qexistsl_tac [`mid`, `n`, `subs`, `k`, `tv`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >> first_x_assum irule >>
     simp[] >> goal_assum (drule_at Any)) >>
  once_rewrite_tac[ADD_COMM] >>
  irule robust_memory_taint_dead_at_endpoint >> simp[] >>
  goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
  qexistsl_tac [`mem`, `off`, `st`, `ta`] >>
  pure_asm_rewrite_tac[] >>
  `b + (32*j + off) = off + 32*j + b` by decide_tac >>
  asm_rewrite_tac[] >> metis_tac[ADD_COMM]
QED

(* Also transports retained tail bytes: only canonical live bytes must agree. *)
Theorem declared_region_dead_at_endpoint:
  !cx tr mid n subs k tv canonical final x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (k,tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
       ~dead_bytes canonical (w2n k) tv i c ==>
       EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
       EL c (word_to_bytes (lookup_storage (n2w i) canonical) T)) /\
    dead_bytes canonical (w2n k) tv x b ==>
    storage_dead cx tr final x b
Proof
  rpt strip_tac >>
  `dead_bytes final (w2n k) tv x b <=>
   dead_bytes canonical (w2n k) tv x b` by
    (irule (cj 1 dead_bytes_live_frame) >> simp[]) >>
  `dead_bytes final (w2n k) tv x b` by metis_tac[] >>
  drule_all declared_region_dead_storage_dead >> simp[]
QED

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
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (k,tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    count <= type_slot_size tv /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
       ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
       EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
       EL c (word_to_bytes (lookup_storage (n2w i)
         (apply_writes k writes st)) T)) /\
    (!i. i < dimword (:256) /\
         ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
         lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
    (!q b. (q,b) IN old ==> storage_dead cx tr st (w2n q) b) /\
    (!q b. (q,b) IN old /\ w2n k + count <= w2n q /\
       w2n q < w2n k + type_slot_size tv ==>
       dead_bytes final (w2n k) tv (w2n q) b) /\
    (!q b. (q,b) IN new ==>
       ((q,b) IN old /\ ~(w2n k <= w2n q /\ w2n q < w2n k + count)) \/
       (?j. w2n q = w2n k+j /\ j < count /\ b < 32 /\
            off + 32*j + b IN ta)) ==>
    !q b. (q,b) IN new ==> storage_dead cx tr final (w2n q) b
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
  drule_all robust_memory_storage_dead_at_endpoint >> simp[]
QED

(* Package either selected backend while framing the other backend. The
   copied-byte theorem above supplies the selected-space implication. *)
Theorem stor_taint_ok_selected_space:
  !cx tr tn s tn' s'.
    stor_taint_ok cx tn s /\
    s'.vs_call_ctx.cc_address = cx.txn.target /\
    s'.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    tn'.t_imm = tn.t_imm /\
    (if tr then
       tn'.t_stor = tn.t_stor /\
       (s'.vs_accounts s'.vs_call_ctx.cc_address).storage =
       (s.vs_accounts s.vs_call_ctx.cc_address).storage
     else
       tn'.t_trans = tn.t_trans /\
       s'.vs_transient s'.vs_call_ctx.cc_address =
       s.vs_transient s.vs_call_ctx.cc_address) /\
    (!q b. (q,b) IN (if tr then tn'.t_trans else tn'.t_stor) ==>
       storage_dead cx tr
         (if tr then s'.vs_transient s'.vs_call_ctx.cc_address
          else (s'.vs_accounts s'.vs_call_ctx.cc_address).storage)
         (w2n q) b) ==>
    stor_taint_ok cx tn' s'
Proof
  Cases_on `tr` >>
  simp[stor_taint_ok_def, cx_dead_def, SUBSET_DEF, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> gvs[]
QED
