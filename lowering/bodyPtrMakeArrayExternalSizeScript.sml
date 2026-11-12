(* Actual source size used by aggregate external unwrap, not destination layout. *)
Theory bodyPtrMakeArrayExternalSize
Ancestors
  exprSimHyps valueEncodingProps words arithmetic

Theorem external_unwrap_source_size:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
  (type_memory_bytes cenv (expr_type e) + 31) DIV 32 = type_slot_size tv /\
  32 * ((type_memory_bytes cenv (expr_type e) + 31) DIV 32) =
    type_memory_bytes cenv (expr_type e) /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  type_slot_size tv < dimword (:256)
Proof
  strip_tac >> drule_all expr_body_pre_copy_ok >> strip_tac >>
  gvs[type_memory_size_slots, dimword_def, MULT_DIV] >> decide_tac
QED
