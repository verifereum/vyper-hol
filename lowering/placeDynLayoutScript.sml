Theory placeDynLayout
Ancestors
  typedMemoryCopy exprSimAggregateEncoding vyperTyping vyperValue valueEncoding valueEncodingDefs valueEncodingProps
  words arithmetic list rich_list

Theorem place_dyn_element_layout:
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  evaluate_type tenv et = SOME etv ==>
  type_memory_bytes cenv et = 32 * type_slot_size etv /\
  (type_memory_bytes cenv et + 31) DIV 32 = type_slot_size etv
Proof
  strip_tac >> drule_all typed_copy_memory_size >>
  simp[type_memory_size_slots] >> strip_tac >> simp[]
QED

Theorem place_dyn_memory_header:
  val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem ==>
  mem_word_at off mem = n2w (LENGTH vs)
Proof
  simp[val_in_memory_def]
QED

Theorem place_dyn_memory_element:
  val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
  i < LENGTH vs ==>
  val_in_memory etv (EL i vs) (off + 32 + i * type_memory_size etv) mem
Proof
  simp[val_in_memory_def] >> rpt strip_tac >>
  drule_all elems_in_memory_EL >> simp[]
QED

Theorem place_dyn_header_length:
  well_formed_type_value (ArrayTV etv (Dynamic cap)) /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem ==>
  w2n (mem_word_at off mem) = LENGTH vs
Proof
  simp[well_formed_type_value_def, value_has_type_def, val_in_memory_def] >>
  rpt strip_tac >> `LENGTH vs < dimword (:256)` by decide_tac >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem place_dyn_zero_element_stores:
  type_slot_size etv = 0 ==>
  FOLDL (\st i.
    FOLDL (\t j. store i j t) st (COUNT_LIST (type_slot_size etv))) s indices = s
Proof
  strip_tac >> simp[COUNT_LIST_def] >> Induct_on `indices` >> simp[]
QED

(* Shared arithmetic boundary for memory bytes and storage slots. *)
Theorem place_dyn_index_bound:
  !base header cap stride count i.
    count <= cap /\
    base + header + cap * stride < dimword (:256) /\
    i < count ==>
    base + header + i * stride + stride < dimword (:256)
Proof
  rpt strip_tac >> `i + 1 <= cap` by decide_tac >>
  `(i + 1) * stride <= cap * stride` by simp[LE_MULT_RCANCEL] >>
  fs[RIGHT_ADD_DISTRIB, MULT_CLAUSES, Excl "LE_MULT_RCANCEL"] >> decide_tac
QED
