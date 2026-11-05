(* Full-capacity boundary for plain convert operands. *)
Theory bodyMemTbConvertSourceMemory
Ancestors
  exprSimMemDefs exprSimMemoryPath exprLowering compileEnv
  vyperValue valueEncoding venomState context

Theorem convert_memory_unwrap_capacity:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  vv_store_bound cx t lt ee tv (LocatedValue t p) s /\
  evaluate_type (get_tenv cx) lt = SOME tvt /\
  eval_operand op s = SOME w ==>
  sb = sm /\ op = p.ptr_operand /\
  (type_memory_size tvt = 0 \/
   w2n w + type_memory_size tvt <= s.vs_alloca_next)
Proof
  strip_tac >>
  drule unwrap_memory_compile >> simp[] >> strip_tac >>
  gvs[comp_return_def, vv_store_bound_def] >>
  metis_tac[]
QED
