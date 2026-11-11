(* Physical subslots inherit their enclosing region, including zero-sized slots. *)
Theory bodyIntCallSubslotGeometry
Ancestors
  exprSimProps loweringPosts valueEncoding venomExecSemantics venomState words arithmetic

Theorem memory_path_enclosing_region:
  !tv path off ptv (a:num) (base:num) (k:num).
  mem_path_offset tv path = SOME (off,ptv) /\
  a <= base /\ base + type_memory_size tv <= a+k /\
  a+k < dimword (:256) ==>
  a <= base+off /\ base+off+type_memory_size ptv <= a+k /\
  base+off < dimword (:256)
Proof
  rpt strip_tac >> drule mem_path_offset_sound >> strip_tac >> decide_tac
QED

Theorem memory_path_authorized_operand:
  !tv path off ptv (a:num) (base:num) (k:num) lo staged child u.
  mem_path_offset tv path = SOME (off,ptv) /\
  a <= base /\ base + type_memory_size tv <= a+k /\
  a+k < dimword (:256) /\
  (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z) /\
  eval_operand child u = SOME (n2w (base+off)) ==>
  ?w. eval_operand child u = SOME w /\ a <= w2n w /\
    w2n w + type_memory_size ptv <= a+k /\ a+k < dimword (:256) /\
    (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)
Proof
  rpt gen_tac >> strip_tac >> drule_all memory_path_enclosing_region >> strip_tac >>
  simp[] >> metis_tac[]
QED
