(* Same-layout stores with their actual checked execution and frame. *)
Theory stmtSimCustomErrorMemSameStore
Ancestors
  aggregateStoreSizePath placeMemoryPrimitiveForward bodyDeclMemoryCore bodyDeclCopyMemory
  exprSimMemUnwrap valueCopy valueCopyBytes fragGasMode
  allocaFootprint context compileEnv exprLoweringProps
  venomState venomInst list rich_list

Theorem compile_store_memory_same_type_size_forward_mem:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  type_memory_size tv + 64 < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type ty /\ val_store_size tv v <> 0 ==>
    w2n sw + val_store_size tv v <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
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
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `is_word_type ty`
     >- (`type_memory_size tv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
         gvs[compile_store_memory_def] >>
         irule emit_mstore_mem_ok >> qexistsl_tac [`dw`, `dst`, `src`] >> simp[]) >>
     Cases_on `val_store_size tv v = 0`
     >- (`type_memory_size tv = 0` by metis_tac[val_store_size_pos, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
         `~is_bytestring_type ty` by
           (strip_tac >> drule_all bytestring_type_value >>
            strip_tac >> gvs[valueEncodingTheory.type_memory_size_def]) >>
         gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
             emitted_insts_def, fragExecMemTheory.run_inst_seq_mem_ok_def]) >>
     irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`dw`, `tenv`, `tv`, `v`, `sw`] >> simp[] >>
     rpt conj_tac >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (irule compile_store_memory_same_type_no_gas >> goal_assum drule) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next)`) >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, lookup_var_def] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >>
  simp[] >> metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED
