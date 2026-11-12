Theory aggregateStoreSizePath
Ancestors
  placeMemoryPrimitiveForward valueCopy fragGasSeq fragGasMode fragExec
  context exprLoweringProps compileEnv venomState venomInst list rich_list

Theorem compile_store_memory_same_type_size_forward:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (irule compile_store_memory_same_type_no_gas >> goal_assum drule) >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_allocas)`) >>
     simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >>
  simp[] >> metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED
