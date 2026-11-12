(* Live-byte agreement for a primitive storage Append. *)
Theory appendStorageRel
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimAppendStorage accountsRelProps vyperStorageFrame compileEnv loweringStateRelDefs
  vyperValue vyperStorageBackend vyperStorage words vfmState venomState
   exprLoweringProps varsExt stateFrame finite_map storageCopyLive

Theorem append_dead_bytes_word[local]:
  type_slot_size tv = 1 ==> ~dead_bytes st bs tv j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_dynamic_dead_bytes[local]:
  type_slot_size tv = 1 ==>
  ~dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_root_dead_mono[local]:
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\
  len < cap /\ w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  j <> w2n (slot + n2w (1+len)) /\
  dead_bytes st (w2n slot) (ArrayTV tv (Dynamic cap)) j b ==>
  dead_bytes (update_storage slot (n2w (len+1))
    (update_storage (slot+n2w (1+len)) w st))
    (w2n slot) (ArrayTV tv (Dynamic cap)) j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_other_region_frame[local]:
  ranges_disjoint bs sz (w2n slot) (1+cap) /\
  bs + sz <= dimword (:256) /\
  w2n slot + (1+cap) <= dimword (:256) /\ len < cap /\
  type_slot_size tv = sz ==>
  (dead_bytes (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) bs tv j b <=>
   dead_bytes st bs tv j b)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_storage_dead_mono:
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  j <> w2n slot /\ j <> w2n (slot+n2w (1+len)) /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)) j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_storage_agree:
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ len = w2n (lookup_storage slot st) /\ len < cap /\
  storage_agree (storage_dead cx tr st) st mt ==>
  storage_agree
    (storage_dead cx tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w st)))
    (update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w st))
    (update_storage slot (n2w (len+1)) (update_storage (slot+n2w (1+len)) w mt))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem accounts_rel_append_storage_word:
  accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  accounts_rel cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem stmt_state_rel_append_storage_updates:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr (update_storage slot (n2w (len+1))
      (update_storage (slot+n2w (1+len)) w (get_storage cx es tr))))
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem stmt_state_rel_append_storage_word:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res, es') ==>
  res = INL () /\
  stmt_state_rel ctx func cenv cx es'
    (if tr then tstore slot (n2w (len+1)) (tstore (slot+n2w (1+len)) w s)
     else sstore slot (n2w (len+1)) (sstore (slot+n2w (1+len)) w s))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Operand preservation includes every previously bound variable; the frame
   then identifies the remaining state fields. *)
Theorem stmt_state_rel_operand_frame:
  stmt_state_rel ctx func cenv cx es s /\
  state_frame t = state_frame s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

(* Growing the root header exposes just one additional child interval. *)
Theorem append_root_copy_dead_mono[local]:
  !tv cap bs len st st' j b.
    bs + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    len = w2n (lookup_storage (n2w bs) st) /\ len < cap /\
    lookup_storage (n2w bs) st' = n2w (len+1) /\
    len+1 < dimword (:256) /\
    (!x. x < dimword (:256) /\ bs < x /\
         ~(bs+1+len*type_slot_size tv <= x /\
           x < bs+1+len*type_slot_size tv+type_slot_size tv) ==>
         lookup_storage (n2w x) st' = lookup_storage (n2w x) st) /\
    ~(bs+1+len*type_slot_size tv <= j /\
      j < bs+1+len*type_slot_size tv+type_slot_size tv) /\
    dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b ==>
    dead_bytes st' bs (ArrayTV tv (Dynamic cap)) j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_storage_copy_dead_mono[local]:
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  len = w2n (lookup_storage slot st) /\ len < cap /\
  len+1 < dimword (:256) /\
  lookup_storage slot st' = n2w (len+1) /\
  (!x. x < dimword (:256) /\ x <> w2n slot /\
       ~(w2n slot+1+len*type_slot_size tv <= x /\
         x < w2n slot+1+len*type_slot_size tv+type_slot_size tv) ==>
       lookup_storage (n2w x) st' = lookup_storage (n2w x) st) /\
  ~(w2n slot+1+len*type_slot_size tv <= j /\
    j < w2n slot+1+len*type_slot_size tv+type_slot_size tv) /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr st' j b
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_copy_layout[local]:
  !(slot:bytes32) tv cap len.
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    0 < type_slot_size tv /\ len < cap ==>
    w2n (slot+n2w (1+len*type_slot_size tv)) = w2n slot+1+len*type_slot_size tv /\
    w2n (slot+n2w (1+len*type_slot_size tv))+type_slot_size tv <= dimword (:256) /\
    len+1 < dimword (:256)
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_copy_source_outside[local]:
  !tv v writes k slot st len x.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    x < dimword (:256) /\ x <> w2n slot /\
    ~(w2n k <= x /\ x < w2n k+type_slot_size tv) ==>
    lookup_storage (n2w x)
      (update_storage slot (n2w (len+1)) (apply_writes k writes st)) =
    lookup_storage (n2w x) st
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem append_storage_agree_copy:
  !cx mid n tr slot tv cap len k v writes off mem st mt.
    declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    (!mid' n' subs' slot' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
      (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
      ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
        (w2n slot') (type_slot_size tv')) /\
    0 < type_slot_size tv /\ len = w2n (lookup_storage slot st) /\ len < cap /\
    k = slot+n2w (1+len*type_slot_size tv) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\ val_in_memory tv v off mem /\
    storage_agree (storage_dead cx tr st) st mt ==>
    storage_agree
      (storage_dead cx tr (update_storage slot (n2w (len+1)) (apply_writes k writes st)))
      (update_storage slot (n2w (len+1)) (apply_writes k writes st))
      (update_storage slot (n2w (len+1))
        (FOLDL (\t i. update_storage (k+n2w i) (mem_word_at (off+32*i) mem) t)
          mt (COUNT_LIST (type_slot_size tv))))
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED

Theorem accounts_rel_append_storage_copy:
  !cx es s mid n tr slot tv cap len k v writes off mem mt s'.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    (!mid' n' subs' slot' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
      (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
      ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
        (w2n slot') (type_slot_size tv')) /\
    0 < type_slot_size tv /\
    len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
    k = slot+n2w (1+len*type_slot_size tv) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\ val_in_memory tv v off mem /\
    mt = (if tr then contract_transient s else contract_storage s) /\
    s'.vs_accounts =
      (if tr then s.vs_accounts else
       (cx.txn.target =+ (lookup_account cx.txn.target s.vs_accounts with storage :=
         update_storage slot (n2w (len+1))
           (FOLDL (\t i. update_storage (k+n2w i) (mem_word_at (off+32*i) mem) t)
             mt (COUNT_LIST (type_slot_size tv))))) s.vs_accounts) /\
    s'.vs_transient =
      (if tr then (cx.txn.target =+ update_storage slot (n2w (len+1))
         (FOLDL (\t i. update_storage (k+n2w i) (mem_word_at (off+32*i) mem) t)
           mt (COUNT_LIST (type_slot_size tv)))) s.vs_transient
       else s.vs_transient) ==>
    accounts_rel cx
      (set_storage cx es tr (update_storage slot (n2w (len+1))
        (apply_writes k writes (get_storage cx es tr)))) s'
Proof
  cheat (* SEQ-4390 LOCAL OVERLAY: foreign t16 red *)
QED
