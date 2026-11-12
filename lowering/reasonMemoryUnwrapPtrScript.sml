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

(* Keep the selected checked prefix endpoint, including its cursor and ghosts;
   memory unwrap adds no instructions and therefore no gas observations. *)
Theorem unwrap_memory_nonword_prefix_path_ptr:
  ~is_word_type ty /\ p.ptr_location = LocMemory /\
  unwrap_value cenv (LocatedValue ty p) sa = (op,sb) /\
  ~t.vs_halted /\
  gas_path_ptr D lo ctx fn PG G0 tn0 s n G tn (OK t) ==>
  op = p.ptr_operand /\ sb = sa /\
  gas_path_ptr D lo ctx fn PG G0 tn0 s (n + 0) G tn (OK t)
Proof
  strip_tac >>
  drule_all unwrap_memory_nonword_path_ptr >> strip_tac >>
  rpt conj_tac >- simp[] >- simp[] >>
  irule gas_path_ptr_then >> goal_assum drule >> simp[]
QED
