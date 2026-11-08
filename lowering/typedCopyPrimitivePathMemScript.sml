(* Checked paths at the explicit endpoints of primitive typed copies. *)
Theory typedCopyPrimitivePathMem
Ancestors
  placeMemoryTypedPrimitive bodyDeclMemoryCounted allocaFootprint
  externalReturnNormalizeMem placeMemoryCopyEffect placeMemoryTypedBase
  valueEncodingProps immutableMemoryFrame exprSimProps bodyDeclMemoryCore valueCopy
  valueCopyBytes
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

Theorem typed_memory_word_path_mem:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_mem ctx func s 0
    (OK ((mstore (w2n dw) (mload (w2n sw) s)
      (update_var (STRING #"%" (toString sa.cs_next_var))
        (mload (w2n sw) s) s))
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all typed_memory_word_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_copy_word_mem_ok >> simp[]) >>
  irule (cj 1 body_decl_cursor_path) >> simp[] >>
  qexists_tac `sa` >> gvs[listTheory.EVERY_MEM]
QED

Theorem typed_memory_word_forward_mem:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ type_memory_size tv = 32 /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >> drule_all typed_memory_word_path_mem >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  `val_in_memory tv v (w2n dw) t.vs_memory` by
    (qspecl_then [`tenv`, `dty`, `tv`, `v`] mp_tac val_in_memory_word >>
     simp[] >> disch_then (fn th => rewrite_tac[th]) >>
     `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 tv v` by
       metis_tac[val_in_memory_word] >>
     simp[Abbr `t`, mstore_mem_word_at_same, GSYM mem_word_at_eq_mload]) >>
  qexists_tac `t` >> simp[typed_copy_effect_def] >> rpt conj_tac
  >- metis_tac[fragGasModeTheory.gas_marked_path_from_mem]
  >- simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
          update_var_def, venom_state_component_equality]
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
           update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- simp[Abbr `t`, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (rpt strip_tac >> simp[Abbr `t`] >>
      simp[mstore_mem_bytes_at_disjoint, update_var_def])
  >- simp[Abbr `t`, immutable_mstore_capacity, update_var_def,
          arithmeticTheory.MAX_DEF]
  >- simp[Abbr `t`, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (`!x. dst = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all typed_memory_word_sequence >>
      simp[same_blocks_def, Abbr `t`, mstore_def,
           write_memory_with_expansion_def, update_var_def]) >>
  simp[Abbr `t`]
QED

Theorem compile_store_memory_same_forward_mem:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + val_store_size tv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory tv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size tv) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by simp[] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     simp[] >> qexists_tac `v` >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[compile_store_memory_same_no_gas] >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >>
     qexists_tac `sa` >> gvs[listTheory.EVERY_MEM]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[typed_copy_effect_def] >>
  `t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb` by
    (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _|>) = s` mp_tac >>
     gvs[same_blocks_def, venom_state_component_equality]) >>
  simp[] >> conj_tac
  >- gvs[fragGasModeTheory.gas_marked_path_from_mem] >>
  qpat_x_assum `(t with <|vs_memory := _; vs_vars := _|>) = s` mp_tac >>
  gvs[venom_state_component_equality, lookup_var_def] >> metis_tac[]
QED

Theorem typed_memory_bytestring_forward_mem:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  `val_store_size dtv v = val_store_size stv v` by
    (irule bytestring_val_store_size_eq >>
     metis_tac[]) >>
  `w2n sw + val_store_size dtv v <= s.vs_alloca_next` by
    (qpat_assum `val_wf stv v` (mp_tac o MATCH_MP val_store_size_le) >>
     decide_tac) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, compile_store_memory_def]) >>
  drule_all compile_store_memory_same_forward_mem >> simp[]
QED

Theorem typed_memory_empty_forward_mem:
  acyclic_struct_metadata cenv.ce_struct_fields /\ value_has_type NoneTV v /\
  compile_store_memory_typed cenv dst NoneT src sty sa = ((),sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory NoneTV v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw) 0 /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, type_memory_bytes_def,
       compile_copy_memory_def, comp_return_def] >> strip_tac >>
  Cases_on `sty` >> Cases_on `v` >>
  gvs[comp_return_def, vyperTypingTheory.value_has_type_def] >>
  qexists_tac `s` >>
  simp[valueEncodingTheory.val_in_memory_def, typed_copy_effect_identity,
       gas_path_mem_rules]
QED
