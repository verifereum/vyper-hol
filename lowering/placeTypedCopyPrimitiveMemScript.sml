(* Bounded primitive paths used by recursive place copies. *)
Theory placeTypedCopyPrimitiveMem
Ancestors
  placeTypedCopyMem placeMemoryTypedPrimitive placeMemoryCopyEffect
  bodyCopyMemory bodyDeclMemoryCounted fragGasPathMem fragGasMode
  valueEncodingProps venomState venomExecSemantics context compileEnv
  exprLoweringProps fragExec list rich_list

Theorem compile_copy_memory_path_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  drule_all compile_copy_memory_body_mem_ok >> strip_tac >>
  irule body_decl_zero_gas_path >>
  conj_tac >- simp[] >> qexists_tac `sa` >> simp[] >> fs[EVERY_MEM]
QED

Theorem compile_copy_memory_effect_mem:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_effect ctx func sa sb s t (w2n dw) n /\
    mem_bytes_at (w2n dw) n t.vs_memory =
      mem_bytes_at (w2n sw) n s.vs_memory
Proof
  strip_tac >> drule_all compile_copy_memory_path_mem >> strip_tac >>
  qexists_tac `(if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule_all compile_copy_memory_sequence >> simp[same_blocks_def]) >>
  `gas_marked_path F ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_mem_exec, gas_marked_path_def] >>
  simp[typed_copy_effect_def] >> Cases_on `n = 0`
  >- gvs[valueEncodingTheory.mem_bytes_at_def, lookup_var_def,
         venom_state_component_equality] >>
  simp[mcopy_mem_bytes_at_same, mcopy_memory_length] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED
