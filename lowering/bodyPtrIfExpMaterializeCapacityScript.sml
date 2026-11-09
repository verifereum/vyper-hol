Theory bodyPtrIfExpMaterializeCapacity
Ancestors
  bodyPtrIfExpBytesInputs valueEncodingProps
  arithmetic

(* Annotation sizes at successful typed arm endpoints are whole words;
   arbitrary natural capacities would not suffice for rounded copying. *)
Theorem ifexp_materialize_annotation_aligned:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
  32 * ((type_memory_bytes ce (expr_type e)+31) DIV 32) =
    type_memory_bytes ce (expr_type e)
Proof
  strip_tac >> drule_all ifexp_arm_annotation_typed >> strip_tac >>
  simp[type_memory_size_slots, MULT_DIV]
QED

Theorem ifexp_materialize_interior_word:
  32 * ((capacity+31) DIV 32) = capacity /\
  k < (capacity+31) DIV 32 ==> 32*k+32 <= capacity
Proof
  strip_tac >>
  `32 * (k+1) <= 32 * ((capacity+31) DIV 32)` by
    (irule LESS_MONO_MULT2 >> decide_tac) >>
  fs[LEFT_ADD_DISTRIB]
QED
