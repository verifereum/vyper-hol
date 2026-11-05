(* Live-byte agreement for a primitive storage Append. *)
Theory appendStorageRel
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimAppendStorage accountsRelProps vyperStorageFrame compileEnv
  vyperValue vyperStorageBackend vyperStorage words vfmState venomState
   exprLoweringProps  varsExt stateFrame finite_map

Theorem append_dead_bytes_word[local]:
  type_slot_size tv = 1 ==> ~dead_bytes st bs tv j b
Proof
  cheat
QED

Theorem append_dynamic_dead_bytes[local]:
  type_slot_size tv = 1 ==>
  (dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b <=>
   bs + 1 + w2n (lookup_storage (n2w bs) st) <= j /\
   j < bs + 1 + cap /\ b < 32)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* Operand preservation includes every previously bound variable; the frame
   then identifies the remaining state fields. *)
Theorem stmt_state_rel_operand_frame:
  stmt_state_rel ctx func cenv cx es s /\
  state_frame t = state_frame s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  cheat
QED
