(* Checked paths at the explicit endpoints of primitive typed copies. *)
Theory typedCopyPrimitivePathMem
Ancestors
  placeMemoryTypedPrimitive bodyDeclMemoryCounted allocaFootprint
  context compileEnv exprLoweringProps venomState venomInst fragGasPathMem

Theorem compile_copy_memory_path_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule_all compile_copy_memory_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `n = 0`
     >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def,
            fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     `emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb)` by
       (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
     irule emit_mcopy_mem_ok >>
     goal_assum (drule_at Any) >>
     simp[eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  irule (cj 1 body_decl_cursor_path) >>
  simp[] >> qexists_tac `sa` >> simp[listTheory.EVERY_MEM] >>
  gvs[listTheory.EVERY_MEM]
QED
