Theory bodyPtrIfExpBytesResources
Ancestors
  bodyPtrIfExpStoreContract bodyPtrIfExpBytesInputs bodyPtrDefs
  loweringPosts valueCopyBytes venomState venomExecSemantics
  compileEnv words vyperTyping

Theorem ifexp_bytes_source_resources:
  ptr_val_ok cx ty v op G tn s /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME w /\ n <= val_store_size tv v ==>
  ?p. op = Var p /\ lookup_var p s = SOME w /\ ptr_covers G tn p s n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `val_footprint tv v <> 0` by
    (drule_all bytestring_type_value >> strip_tac >> gvs[] >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  drule_all ptr_val_ok_store_read_covers >> strip_tac >>
  qexists_tac `p` >> gvs[eval_operand_def] >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def]
QED

Theorem ifexp_bytes_destination_resources:
  ptr_covers G tn out s capacity /\ lookup_var out s = SOME (n2w addr) /\
  addr+capacity < dimword(:256) /\ n <= capacity ==>
  ptr_covers G tn out s n /\ w2n (n2w addr : bytes32) = addr /\
  addr+n < dimword(:256)
Proof
  strip_tac >> `addr < dimword(:256)` by decide_tac >>
  simp[] >> gvs[ptr_covers_def] >>
  qexistsl_tac [`b`, `sz`] >> simp[] >> decide_tac
QED

Theorem ifexp_bytes_writer_resources:
  ptr_val_ok cx ty v op G tn s /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME w /\
  val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  ptr_covers G tn out s capacity /\ lookup_var out s = SOME (n2w addr) /\
  addr+capacity < dimword(:256) /\
  32 + 32 * ((len+31) DIV 32) <= capacity ==>
  ?p. op = Var p /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s (32 + 32 * ((len+31) DIV 32)) /\
    ptr_covers G tn out s (32 + 32 * ((len+31) DIV 32)) /\
    w2n (n2w addr : bytes32) = addr /\
    addr + (32 + 32 * ((len+31) DIV 32)) < dimword(:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m)
Proof
  strip_tac >>
  `32 + 32 * ((len+31) DIV 32) <= val_store_size tv v` by simp[] >>
  drule_all ifexp_bytes_source_resources >> strip_tac >>
  drule_all ifexp_bytes_destination_resources >> strip_tac >> gvs[]
QED
