(* Coercing local bytestring stores depend on the value's runtime length,
   not on any ordering between source and destination capacities. *)
Theory assignTuplePtrLocalCompat
Ancestors
  assignTuplePtrBytesResources exprSimBufferStore exprSimProps
  valueEncoding valueEncodingDefs valueEncodingProps vyperTyping vyperValue context compileEnv
  valueTypingMemoryProps valueCopyBytes bodyPtrDefs venomState venomExecSemantics words arithmetic vfmConstants

Theorem bytestring_evaluated_shape_ptr:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  (?n. tv = BaseTV (StringT n)) \/
  (?n. tv = BaseTV (BytesT (Dynamic n)))
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  simp[evaluate_type_def] >> rpt strip_tac >> gvs[]
QED

Theorem bytestring_representation_compat_ptr:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  is_bytestring_type dt /\ evaluate_type denv dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v ==>
  (val_in_memory tv v a mem <=> val_in_memory dtv v a mem) /\
  val_store_size tv v = val_store_size dtv v
Proof
  strip_tac >>
  `(?n. tv = BaseTV (StringT n)) \/
   (?n. tv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  `(?n. dtv = BaseTV (StringT n)) \/
   (?n. dtv = BaseTV (BytesT (Dynamic n)))` by
    metis_tac[bytestring_evaluated_shape_ptr] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def, val_store_size_def]
QED

Theorem compile_store_memory_bytestring_compat_ptr:
  is_bytestring_type dt ==>
  compile_store_memory cenv src dst dt ty = compile_store_bytestring src dst
Proof
  strip_tac >> simp[compile_store_memory_def, is_bytestring_word_type]
QED

Theorem bytestring_robust_representation_compat_ptr:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  is_bytestring_type dt /\ evaluate_type denv dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\
  (!mem. mem_agree_outside tm s.vs_memory mem ==> val_in_memory tv v a mem) ==>
  !mem. mem_agree_outside tm s.vs_memory mem ==> val_in_memory dtv v a mem
Proof
  metis_tac[bytestring_representation_compat_ptr]
QED

Theorem bytestring_compatible_resources_ptr:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  is_bytestring_type dt /\ evaluate_type denv dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\
  type_memory_size dtv + 64 < dimword (:256) /\
  (!mem. mem_agree_outside tm s.vs_memory mem ==> val_in_memory tv v a mem) ==>
  ?len. mload a s = n2w len /\
    len+31 < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) < dimword (:256) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_size tv /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_size dtv /\
    val_footprint dtv v <= 32 + 32 * ((len+31) DIV 32) /\
    (!i. a <= i /\ i < a+32 ==> i NOTIN tm)
Proof
  strip_tac >>
  `val_in_memory tv v a s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_store_size tv v = val_store_size dtv v` by
    metis_tac[bytestring_representation_compat_ptr] >>
  `val_store_size tv v <= type_memory_size tv /\
   val_store_size dtv v <= type_memory_size dtv` by
    metis_tac[value_has_type_memory_wf, val_store_size_le] >>
  `val_footprint dtv v <= val_store_size dtv v` by
    simp[val_footprint_le_store_size] >>
  `!i. a <= i /\ i < a+32 ==> i NOTIN tm` by
    metis_tac[robust_bytestring_header_clean_ptr] >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule buffer_round_no_wrap >> strip_tac >>
  qexists_tac `len` >> fs[word_size_def] >> decide_tac
QED

(* Both capacity orders admit the same short runtime value. *)
Theorem bytestring_capacity_orders_probe_ptr[local]:
  value_has_type (BaseTV (BytesT (Dynamic 1))) (BytesV [0w]) /\
  value_has_type (BaseTV (BytesT (Dynamic 96))) (BytesV [0w]) /\
  val_store_size (BaseTV (BytesT (Dynamic 1))) (BytesV [0w]) = 64 /\
  val_store_size (BaseTV (BytesT (Dynamic 96))) (BytesV [0w]) = 64 /\
  type_memory_size (BaseTV (BytesT (Dynamic 1))) = 64 /\
  type_memory_size (BaseTV (BytesT (Dynamic 96))) = 128
Proof
  EVAL_TAC
QED
