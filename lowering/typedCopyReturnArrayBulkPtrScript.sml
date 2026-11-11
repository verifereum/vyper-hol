(* Counted bulk array copying, retaining all frames on one endpoint. *)
Theory typedCopyReturnArrayBulkPtr
Ancestors assignBasePtrCopyFrame assignBasePtrCopyPath assignTuplePtrLocalFixedCopy
  venomExecSemantics ptrDiscipline
  annAssignPtrCopy exprSimBufferStore typedMemoryCopy valueCopy
  fragGasPathPtr bodyPtrDefs context words venomState venomInst
  emitHelper compileEnv valueEncoding valueEncodingProps finite_map
  exprSimProps vyperTypeSystem vyperTypeABI vyperTypeArgFits

Theorem typed_copy_bulk_fixed_counted[local]:
  n < dimword(:256) /\
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (n <> 0 ==> ptr_covers G tn src s n /\ ptr_covers G tn dst s n) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) n s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b+n <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[gas_path_ptr_rules] >>
      rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`,`0`,`m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >> fs[] >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
        comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def]) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[typed_copy_mcopy_state_frame, annassign_static_mcopy_ghost_ptr] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >-
    (gen_tac >> disch_tac >> conj_tac
     >- (`mem_bytes_at i 1 (mcopy (w2n b) (w2n a) n s).vs_memory =
           mem_bytes_at i 1 s.vs_memory` by
           (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
         pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
         simp[buffer_window_byte]) >>
     eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >-
    simp[step_taint_def, mk_inst_def, imm_taint_def, adopt_reset_def,
         set_var_taint_def] >>
  simp[op_taint_def, annassign_static_mcopy_ghost_ptr] >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_copy_sarray_bulk_counted:
  type_memory_bytes ce de = type_memory_bytes ce se /\
  ~is_abi_dynamic ce.ce_struct_fields de /\
  compile_store_memory_typed ce (Var dst) (ArrayT de (Fixed N))
    (Var src) (ArrayT se (Fixed M)) sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv (ArrayT se (Fixed M)) (ArrayT de (Fixed N)) /\
  evaluate_type tenv (ArrayT se (Fixed M)) = SOME stv /\
  evaluate_type tenv (ArrayT de (Fixed N)) = SOME dtv /\ val_wf stv v /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  w2n a + type_memory_size stv < dimword(:256) /\
  w2n b + type_memory_size dtv < dimword(:256) /\
  (type_memory_size stv <> 0 ==> ptr_covers G tn src s (type_memory_size stv)) /\
  (type_memory_size dtv <> 0 ==> ptr_covers G tn dst s (type_memory_size dtv)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b + type_memory_size dtv <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `~is_abi_dynamic ce.ce_struct_fields (ArrayT de (Fixed N))` by
    simp[is_abi_dynamic_def] >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `type_memory_bytes ce (ArrayT de (Fixed N)) = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `compile_copy_memory (Var dst) (Var src) (type_memory_size dtv) sa = ((),sb)` by
    (gvs[Once compile_store_memory_typed_def, is_word_type_def,
         is_bytestring_type_def, type_memory_bytes_def] >>
     gvs[Once compile_store_memory_typed_def]) >>
  irule typed_copy_bulk_fixed_counted >> simp[] >>
  conj_tac >- metis_tac[exprSimPropsTheory.val_footprint_le] >>
  qexistsl_tac [`a`,`dst`,`src`] >> simp[]
QED
