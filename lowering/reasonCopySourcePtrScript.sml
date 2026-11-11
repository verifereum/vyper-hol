(* Source controls and copy sizes for string normalization. Payload bytes
   remain arbitrary; only the length/header word is required clean. *)
Theory reasonCopySourcePtr
Ancestors
  reasonRepresentationPtr immutableCopyWordsPtr storageCopyLoopPtr
  bodyPtrDefs ptrDiscipline exprSimProps compileEnv valueEncoding
  venomState venomExecSemantics words arithmetic pred_set vyperStorage vyperValue valueEncodingProps

Theorem ptr_vv_ok_string_storage_key_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT n)) /\
  eval_operand p.ptr_operand s = SOME a /\
  p.ptr_location = (if tr then LocTransient else LocStorage) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {}
Proof
  strip_tac >> simp[key_taint_def, EXTENSION] >> gen_tac >>
  Cases_on `x < 32` >> simp[] >>
  drule_all ptr_vv_ok_string_storage_head_clean >>
  Cases_on `tr` >> gvs[]
QED

Theorem storage_copy_head_taint:
  0 < n /\ key_taint X a = {} /\
  (!i h. i < n /\ h < 32 ==>
    (b + 32*i + h IN M <=> (a + n2w i,h) IN X)) ==>
  mem_word_taint M b = {}
Proof
  strip_tac >> simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
  Cases_on `x < 32` >> simp[] >>
  qpat_x_assum `!i h. _` (qspecl_then [`0`,`x`] mp_tac) >>
  gvs[key_taint_def, EXTENSION, WORD_ADD_0] >> metis_tac[]
QED

Theorem string_store_size_slots:
  val_wf (BaseTV (StringT max)) (StringV str) ==>
  0 < type_slot_size (BaseTV (StringT max)) /\
  val_store_size (BaseTV (StringT max)) (StringV str) =
    32 + 32 * word_size (LENGTH str) /\
  val_store_size (BaseTV (StringT max)) (StringV str) <=
    32 * type_slot_size (BaseTV (StringT max)) /\
  32 * type_slot_size (BaseTV (StringT max)) =
    type_memory_size (BaseTV (StringT max))
Proof
  strip_tac >>
  `val_store_size (BaseTV (StringT max)) (StringV str) <=
   type_memory_size (BaseTV (StringT max))` by
    metis_tac[val_store_size_le] >>
  gvs[val_store_size_def, type_slot_size_def, type_memory_size_def]
QED

Theorem ptr_covers_mono:
  ptr_covers G tn root s cap /\ sz <= cap ==>
  ptr_covers G tn root s sz
Proof
  simp[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_MONO_ADD_EQ]
QED
