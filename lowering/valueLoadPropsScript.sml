(* TOP-LEVEL: type-directed values held in operands and memory.
   A word operand contains the typed encoding; an aggregate operand points to
   its typed memory representation. Fixed bytes retain their left alignment. *)
Theory valueLoadProps
Ancestors
  compileEnv valueEncoding valueEncodingProps memoryValueDefs vyperValue vyperTyping venomState vyperLookup
  vyperInterpreter vyperState

Definition lowered_value_rel_def:
  lowered_value_rel ty tv v op ss <=>
    value_has_type tv v /\
    ?w. eval_operand op ss = SOME w /\
      if is_word_type ty then w = typed_val_to_w256 tv v
      else memory_value_rel tv v (w2n w) ss.vs_memory
End

Theorem val_in_memory_base_word:
  !bt v offset mem.
    is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
    val_in_memory (BaseTV bt) v offset mem ==>
    mem_word_at offset mem = typed_val_to_w256 (BaseTV bt) v
Proof
  rpt gen_tac >> Cases_on `bt` >> Cases_on `v` >>
  gvs[is_word_type_def, value_has_type_def, val_in_memory_def,
    typed_val_to_w256_def, AllCaseEqs()] >>
  rename1 `is_word_type (BaseT (BytesT bound))` >> Cases_on `bound` >>
  simp[is_word_type_def]
QED

Theorem evaluate_type_base_identity:
  !tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt` >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `evaluate_type tenv (BaseT (BytesT bound)) = SOME tv` >>
  Cases_on `bound` >> gvs[evaluate_type_def, AllCaseEqs()]
QED

Theorem val_in_memory_word:
  !tenv ty tv v offset mem.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty /\
    value_has_type tv v /\ val_in_memory tv v offset mem ==>
    mem_word_at offset mem = typed_val_to_w256 tv v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  FIRST [drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      irule val_in_memory_base_word >> simp[],
    Cases_on `v` >>
    gvs[evaluate_type_def, value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def, AllCaseEqs()]]
QED

Theorem vars_rel_memloc_value:
  !cenv scopes ss id entry offset size.
  vars_rel cenv scopes ss /\ lookup_scopes id scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (MemLoc offset size) ==>
  memory_value_rel entry.type entry.value offset ss.vs_memory
Proof
  rw[vars_rel_def] >> first_x_assum drule_all >> simp[]
QED

Theorem memory_value_rel_base_word:
  !bt v offset mem.
    is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
    memory_value_rel (BaseTV bt) v offset mem ==>
    mem_word_at offset mem = typed_val_to_w256 (BaseTV bt) v
Proof
  simp[memory_value_rel_def, val_in_memory_base_word]
QED

Theorem memory_value_rel_word:
  !tenv ty tv v offset mem.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty /\
    value_has_type tv v /\ memory_value_rel tv v offset mem ==>
    mem_word_at offset mem = typed_val_to_w256 tv v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  FIRST [drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      irule memory_value_rel_base_word >> simp[],
    Cases_on `v` >>
    gvs[evaluate_type_def, value_has_type_def, memory_value_rel_def,
      val_in_memory_def, typed_val_to_w256_def, AllCaseEqs()]]
QED

Theorem memory_value_rel_bytestring:
  !tenv ty tv v offset mem.
    evaluate_type tenv ty = SOME tv /\ is_bytestring_type ty /\
    memory_value_rel tv v offset mem ==>
    val_in_memory tv v offset mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[memory_value_rel_def]
QED

Theorem mstore_establishes_memory_value_rel_base_word:
  !bt v offset ss.
    is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v ==>
    memory_value_rel (BaseTV bt) v offset
      (mstore offset (typed_val_to_w256 (BaseTV bt) v) ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt` >> Cases_on `v` >>
  gvs[is_word_type_def, value_has_type_def, memory_value_rel_def,
    val_in_memory_def, typed_val_to_w256_def, mstore_mem_word_at_same, AllCaseEqs()] >>
  rename1 `is_word_type (BaseT (BytesT byte_bound))` >> Cases_on `byte_bound` >>
  gvs[is_word_type_def]
QED

Theorem mstore_establishes_memory_value_rel_word:
  !tenv ty tv v offset ss.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty /\ value_has_type tv v ==>
    memory_value_rel tv v offset (mstore offset (typed_val_to_w256 tv v) ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  FIRST [drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      irule mstore_establishes_memory_value_rel_base_word >> simp[],
    Cases_on `v` >>
    gvs[evaluate_type_def, value_has_type_def, memory_value_rel_def,
      val_in_memory_def, typed_val_to_w256_def, mstore_mem_word_at_same, AllCaseEqs()]]
QED

Theorem store_lowered_word_memory_value_rel:
  !tenv ty tv v arg_op word offset ss.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty /\
    lowered_value_rel ty tv v arg_op ss /\ eval_operand arg_op ss = SOME word ==>
    memory_value_rel tv v offset (mstore offset word ss).vs_memory
Proof
  rpt strip_tac >> gvs[lowered_value_rel_def] >>
  irule mstore_establishes_memory_value_rel_word >> simp[] >>
  qexistsl_tac [`tenv`, `ty`] >> simp[]
QED

Theorem eval_name_lookup_scopes:
  !id es entry cx ann.
  lookup_scopes id es.scopes = SOME entry ==>
  eval_expr cx (Name ann id) es = (INL (Value entry.value),es)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes_val id es.scopes = SOME entry.value` by
    (rewrite_tac[lookup_scopes_val_SOME] >> qexists_tac `entry` >> simp[]) >>
  simp[Once evaluate_def, get_scopes_def, bind_def, return_def]
QED

Theorem lowered_value_rel_frame:
  lowered_value_rel ty tv v op ss /\
  eval_operand op ss' = eval_operand op ss /\
  ss'.vs_memory = ss.vs_memory ==>
  lowered_value_rel ty tv v op ss'
Proof
  simp[lowered_value_rel_def]
QED
