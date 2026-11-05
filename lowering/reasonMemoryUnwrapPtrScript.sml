(* Non-word memory normalization is a true no-op: in particular all live
   encoder buffers retain their ghost and allocation bounds unchanged. *)
Theory reasonMemoryUnwrapPtr
Ancestors
  exprLowering context compileEnv fragGasPathPtr venomState ptrSafeRun

Theorem unwrap_memory_nonword_path_ptr:
  ~is_word_type ty /\ p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
  ~s.vs_halted ==>
  op = p.ptr_operand /\ sb = sa /\
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s)
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
