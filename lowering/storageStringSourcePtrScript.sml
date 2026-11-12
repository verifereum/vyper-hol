(* Compiler-independent source resources for storage reason normalization. *)
Theory storageStringSourcePtr
Ancestors
  storageCopyRepresentationPtr storageDecodeMemory vyperStorageBackend
  accountsRelProps loweringPosts vyperStorage vyperValue words arithmetic list
  valueTypingMemoryProps

Theorem storage_holds_string_source_resources:
  storage_holds cx tr ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) ==>
  lookup_storage a (if tr then contract_transient s else contract_storage s) = n2w (LENGTH str) /\
  w2n (lookup_storage a (if tr then contract_transient s else contract_storage s)) = LENGTH str /\
  w2n a + type_slot_size (BaseTV (StringT max)) <= dimword(:256) /\
  0 < type_slot_size (BaseTV (StringT max)) /\
  LENGTH str <= 32*(type_slot_size (BaseTV (StringT max))-1)
Proof
  rpt strip_tac >>
  gvs[storage_holds_def, read_storage_slot_eq, AllCaseEqs()] >>
  qpat_x_assum `decode_value _ _ _ = SOME _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >>
  drule decode_dyn_bytes_observations >> strip_tac >>
  drule storage_range_agree_head >>
  simp[type_slot_size_def] >> strip_tac >>
  gvs[storage_range_agree_def, type_slot_size_def, read_slot_def] >>
  mp_tac (Q.SPEC `max` word_size_capacity) >> decide_tac
QED
