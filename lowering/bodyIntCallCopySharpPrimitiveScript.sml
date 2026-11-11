Theory bodyIntCallCopySharpPrimitive
Ancestors
  placeMemoryTypedPrimitive exprSimBufferStore valueCopyBytes
  context exprSimProps venomExecSemantics valueCopy placeMemoryPrimitiveForward
  exprLoweringProps venomState compileEnv

Theorem typed_memory_bytestring_forward_sharp:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, compile_store_memory_def]) >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    (gvs[compile_store_memory_def] >> metis_tac[is_bytestring_word_type]) >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `32 + 32 * word_size len <= type_memory_size dtv` by
    metis_tac[val_store_size_le] >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by gvs[mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  rename1 `run_inst_seq _ s = OK u` >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (irule compile_store_memory_same_type_no_gas >> goal_assum drule) >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `val_in_memory dtv v (w2n dw) u.vs_memory` by
    (simp[] >> irule mcopy_val_in_memory >> simp[] >>
     metis_tac[val_footprint_le_store_size, arithmeticTheory.ADD_COMM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb,z.vs_allocas)`) >>
     simp[]) >>
  `!a k. a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by simp[mcopy_memory_length] >>
  qpat_x_assum `u.vs_memory = _` kall_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s`
    (mp_tac o Q.AP_TERM
      `\z. z with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                    vs_inst_idx := s.vs_inst_idx|>`) >>
  simp[] >>
  `s with <|vs_prev_bb := s.vs_prev_bb;
            vs_current_bb := sa.cs_current_bb|> = s` by
    (qpat_x_assum `s.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  metis_tac[lookup_var_def, arithmeticTheory.ADD_COMM]
QED
