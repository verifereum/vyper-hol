(* Semantic head projections at the selected checked copy endpoint. *)
Theory reasonNormalizeHead
Ancestors
  reasonNormalizePtr stringUnwrapLayout exprSimStorageCopy accountsRelProps
  loweringPosts vyperState vyperStorage vyperValue vyperInterpreter
  vyperTypeStatePreservation venomMemProps venomMemDefs list words arithmetic
  appendStorageGhostPtr exprSimLen vyperTypeSystem vyperStorageBackend venomState
  immutableCopyExecution immutableConstructorRelation valueEncoding valueEncodingDefs

Theorem copy_prefix_head:
  copy_prefix loc a b n sm n t /\ 0 < n ==>
  mem_word_at b t.vs_memory = copy_runtime_word loc sm a
Proof
  simp[copy_prefix_def] >> strip_tac >>
  qpat_x_assum `!i. i < n ==> _` (qspec_then `0` mp_tac) >> simp[WORD_ADD_0]
QED

Theorem string_storage_decode_head:
  evaluate_type tenv (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  decode_value st (w2n a) (BaseTV (StringT max)) = SOME (StringV str) ==>
  lookup_storage a st = n2w (LENGTH str)
Proof
  strip_tac >>
  drule_at (Pat `decode_value _ _ _ = _`)
    (Q.SPECL [`tenv`,`BaseT (StringT max)`] sized_decode_header) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[is_sized_type_def] >>
  disch_then (qspecl_then [`ARB`,`ARB`] mp_tac) >>
  simp[result_array_length_def, read_result_def, bind_def, return_def,
    read_slot_def]
QED

Theorem storage_holds_string_head:
  storage_holds cx tr (BaseT (StringT max)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) ==>
  lookup_storage a (if tr then contract_transient s else contract_storage s) =
    n2w (LENGTH str)
Proof
  simp[storage_holds_def] >> strip_tac >>
  `tvt = BaseTV (StringT max)` by fs[evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `decode_value (get_storage cx es tr) (w2n a) (BaseTV (StringT max)) =
    SOME (StringV str)` by fs[read_storage_slot_eq, AllCaseEqs()] >>
  drule_all string_storage_decode_head >> strip_tac >>
  drule storage_range_agree_head >>
  simp[type_slot_size_def]
QED

Theorem storage_copy_string_head:
  storage_holds cx tr (BaseT (StringT max)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  sm.vs_accounts = s.vs_accounts /\ sm.vs_transient = s.vs_transient /\
  sm.vs_call_ctx = s.vs_call_ctx /\
  copy_prefix (if tr then LocTransient else LocStorage) a b n sm n t /\ 0 < n ==>
  mem_word_at b t.vs_memory = n2w (LENGTH str)
Proof
  strip_tac >> drule_all storage_holds_string_head >> strip_tac >>
  drule_all copy_prefix_head >>
  Cases_on `tr` >>
  fs[copy_runtime_word_def, sload_def, tload_def,
    contract_storage_def, contract_transient_def]
QED

Theorem immutable_runtime_transfers_value:
  val_in_memory tv v (w2n (a:bytes32)) sm.vs_data_section /\ val_wf tv v /\
  0 < n /\ type_memory_size tv = 32*n /\
  w2n a+32*n < dimword(:256) /\ b+32*n < dimword(:256) ==>
  val_in_memory tv v b (immutable_transfers F F a (n2w b) n 0 sm).vs_memory
Proof
  strip_tac >>
  `immutable_transfers F F (a:bytes32) (n2w b) n 0 sm =
    write_memory_with_expansion b (mem_bytes_at (w2n a) (32*n) sm.vs_data_section) sm` by
    (mp_tac (Q.SPECL [`n`,`w2n (a:bytes32)`,`b`,`0`,`sm`]
       immutable_runtime_transfers_snapshot) >>
     simp[mem_bytes_at_def]) >>
  simp[] >> irule immutable_copy_memory_value >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem immutable_runtime_string_head:
  val_in_memory (BaseTV (StringT max)) (StringV str)
    (w2n (a:bytes32)) s.vs_data_section /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  sm.vs_data_section = s.vs_data_section /\
  n = type_slot_size (BaseTV (StringT max)) /\
  w2n a+32*n < dimword(:256) /\ b+32*n < dimword(:256) /\
  t.vs_memory = (immutable_transfers F F a (n2w b) n 0 sm).vs_memory ==>
  mem_word_at b t.vs_memory = n2w (LENGTH str)
Proof
  strip_tac >>
  `0 < n /\ type_memory_size (BaseTV (StringT max)) = 32*n` by
    fs[type_slot_size_def, type_memory_size_def] >>
  `val_in_memory (BaseTV (StringT max)) (StringV str) b
     (immutable_transfers F F a (n2w b) n 0 sm).vs_memory` by
    (irule immutable_runtime_transfers_value >> simp[]) >>
  gvs[val_in_memory_def]
QED
