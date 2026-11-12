(* Located-value boundary for the storage normalization representation proof. *)
Theory storageLocatedResourcesPtr
Ancestors
  storageStringSourcePtr bodyPtrDefs storageCopyRepresentationPtr
  venomState vfmState compileEnv ptrDiscipline vyperValue words arithmetic

Theorem located_storage_dead_bytes:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME a /\
  evaluate_type (get_tenv cx) t = SOME ty ==>
  !k r. w2n a <= w2n k /\ w2n k < w2n a + type_slot_size ty /\
    r < 32 /\ (k,r) IN (if tr then tn.t_trans else tn.t_stor) ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) ty (w2n k) r
Proof
  Cases_on `tr` >>
  simp[ptr_vv_ok_def, contract_storage_def, contract_transient_def,
       lookup_account_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem located_storage_string_source_resources:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME a /\
  storage_holds cx tr t tv a es s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) ==>
  lookup_storage a (if tr then contract_transient s else contract_storage s) = n2w (LENGTH str) /\
  w2n (lookup_storage a (if tr then contract_transient s else contract_storage s)) = LENGTH str /\
  w2n a + type_slot_size (BaseTV (StringT max)) <= dimword(:256) /\
  0 < type_slot_size (BaseTV (StringT max)) /\
  LENGTH str <= 32*(type_slot_size (BaseTV (StringT max))-1) /\
  (!k r. w2n a <= w2n k /\
    w2n k < w2n a + type_slot_size (BaseTV (StringT max)) /\
    r < 32 /\ (k,r) IN (if tr then tn.t_trans else tn.t_stor) ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) (BaseTV (StringT max)) (w2n k) r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all storage_holds_string_source_resources >> strip_tac >>
  drule located_storage_dead_bytes >>
  disch_then (qspecl_then [`BaseTV (StringT max)`, `tr`, `a`] mp_tac) >>
  simp[]
QED
