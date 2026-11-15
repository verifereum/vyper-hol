(* Adapter from loaded tuple words to the immutable store boundary. *)
Theory tupleAssignImmutableDeployWord
Ancestors
  immutableAssignStore

Theorem tuple_immutable_loaded_word_store:
  compile_store_at_loc cenv.ce_imm_alloca dst src (SOME LocCode) sa = ((),sb) /\
  (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME (n2w off) /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  off < dimword (:256) /\
  evaluate_type tenv dty = SOME tv /\ is_word_type dty /\ value_has_type tv v /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory tv v off u.vs_memory /\
    immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) u.vs_memory) /\
    u.vs_memory = (mstore off (typed_val_to_w256 tv v) s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (off,typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `compile_assign_value cenv dst LocCode src T NONE dty dty 0 sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def,
        stmtLoweringTheory.compile_store_at_loc_def,
        compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  drule_all immutable_assign_word_store >> simp[]
QED
