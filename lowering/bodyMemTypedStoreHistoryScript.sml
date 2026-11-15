(* Static allocation-prefix provenance for typed memory stores. *)
Theory bodyMemTypedStoreHistory
Ancestors
  context compileEnv emitHelper fragExec allocaHistory venomInst rich_list list
  exprOpenCopies

Theorem typed_prefix_trans[local]:
  (!k. k < LENGTH b.cs_current_insts /\
    (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
    b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
    EL k b.cs_current_insts = EL k a.cs_current_insts) /\
  (!k. k < LENGTH c.cs_current_insts /\
    (EL k c.cs_current_insts).inst_opcode = ALLOCA ==>
    c.cs_current_bb = b.cs_current_bb /\ k < LENGTH b.cs_current_insts /\
    EL k c.cs_current_insts = EL k b.cs_current_insts) ==>
  (!k. k < LENGTH c.cs_current_insts /\
    (EL k c.cs_current_insts).inst_opcode = ALLOCA ==>
    c.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
    EL k c.cs_current_insts = EL k a.cs_current_insts)
Proof
  metis_tac[]
QED

Theorem typed_prefix_append[local]:
  b.cs_current_bb = a.cs_current_bb /\
  (?xs. b.cs_current_insts = a.cs_current_insts ++ xs /\
    EVERY (\i. i.inst_opcode <> ALLOCA) xs) ==>
  !k. k < LENGTH b.cs_current_insts /\
    (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
    b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
    EL k b.cs_current_insts = EL k a.cs_current_insts
Proof
  strip_tac >> gen_tac >> Cases_on `k < LENGTH a.cs_current_insts` >>
  simp[EL_APPEND_EQN] >> fs[EVERY_EL] >> strip_tac >>
  first_x_assum (qspec_then `k - LENGTH a.cs_current_insts` mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem typed_prefix_simple[local]:
  (compile_copy_memory dst src n a = (r,b) \/
   compile_with_byte_offset ptr_op off a = (off_op,b) \/
   compile_store_bytestring src dst a = (r,b)) ==>
  !k. k < LENGTH b.cs_current_insts /\
    (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
    b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
    EL k b.cs_current_insts = EL k a.cs_current_insts
Proof
  Cases_on `n` >> Cases_on `off = 0` >>
  strip_tac >> match_mp_tac typed_prefix_append >>
  gvs[compile_copy_memory_def, compile_with_byte_offset_def,
      compile_store_bytestring_def, compile_bytestring_copy_len_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
      mk_inst_def, AllCaseEqs()] >>
  simp[APPEND_ASSOC]
QED

Theorem typed_store_prefix_mutual[local]:
  (!ce dst dt src st a r b.
    compile_store_memory_typed ce dst dt src st a = (r,b) ==>
    !k. k < LENGTH b.cs_current_insts /\
      (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
      b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
      EL k b.cs_current_insts = EL k a.cs_current_insts) /\
  (!ce dst src dts sts doff soff a r b.
    compile_typed_copy_fields ce dst src dts sts doff soff a = (r,b) ==>
    !k. k < LENGTH b.cs_current_insts /\
      (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
      b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
      EL k b.cs_current_insts = EL k a.cs_current_insts) /\
  (!ce dst dt src st n a r b.
    compile_copy_sarray_typed ce dst dt src st n a = (r,b) ==>
    !k. k < LENGTH b.cs_current_insts /\
      (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
      b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
      EL k b.cs_current_insts = EL k a.cs_current_insts) /\
  (!ce dst dt cap src st a r b.
    compile_copy_dynarray_typed ce dst dt cap src st a = (r,b) ==>
    !k. k < LENGTH b.cs_current_insts /\
      (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
      b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
      EL k b.cs_current_insts = EL k a.cs_current_insts) /\
  (!ce dst src dfs sfs doff soff a r b.
    compile_struct_typed_copy ce dst src dfs sfs doff soff a = (r,b) ==>
    !k. k < LENGTH b.cs_current_insts /\
      (EL k b.cs_current_insts).inst_opcode = ALLOCA ==>
      b.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
      EL k b.cs_current_insts = EL k a.cs_current_insts)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, comp_return_def]
  >> suspend "struct"
QED

Resume typed_store_prefix_mutual[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `is_word_type dt`
  >- (pure_once_rewrite_tac[compile_store_memory_typed_def] >> simp[] >>
      simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
           emit_op_def, emit_void_def, fresh_id_def,
           fresh_var_def, emit_def, mk_inst_def] >> strip_tac >>
      match_mp_tac typed_prefix_append >> gvs[APPEND_ASSOC]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (simp[Once compile_store_memory_typed_def] >>
      metis_tac[typed_prefix_simple]) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (strip_tac >> drule_all compile_store_memory_typed_complex_cases >>
      strip_tac
      >- (qpat_x_assum `!dt' dts st' v13 dt'' v37 v43 cap.
            _ ==> !a r b. compile_copy_dynarray_typed _ _ _ _ _ _ _ = _ ==> _`
            mp_tac >>
          ntac 3 (qpat_x_assum `!dt' dts. _` kall_tac) >>
          gvs[is_bytestring_type_def] >>
          disch_then drule >> metis_tac[])
      >- (qpat_x_assum `!dt' dts st' v13 dt'' v37 v42 n.
            _ ==> !a r b. compile_copy_sarray_typed _ _ _ _ _ _ _ = _ ==> _` mp_tac >>
          ntac 3 (qpat_x_assum `!dt' dts. _` kall_tac) >>
          gvs[is_bytestring_type_def] >> disch_then drule >> metis_tac[])
      >- (qpat_x_assum `!dt' dts sts dts'.
            _ ==> !a r b. compile_typed_copy_fields _ _ _ _ _ _ _ _ = _ ==> _` mp_tac >>
          ntac 3 (qpat_x_assum `!dt' dts. _` kall_tac) >>
          gvs[] >> disch_then drule >> metis_tac[])
      >- (qpat_x_assum `!dt' dts src_nsid dst_nsid dfs sfs.
            _ ==> !a r b. compile_struct_typed_copy _ _ _ _ _ _ _ _ = _ ==> _` mp_tac >>
          ntac 3 (qpat_x_assum `!dt' dts. _` kall_tac) >>
          gvs[] >> disch_then drule >> metis_tac[]) >>
      rpt (qpat_x_assum `!dt' dts. _` kall_tac) >>
      metis_tac[typed_prefix_simple]) >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >> simp[] >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def, mk_inst_def] >>
  strip_tac >> match_mp_tac typed_prefix_append >> gvs[]
QED
Resume typed_store_prefix_mutual[fields]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
  rpt (qpat_x_assum `!dst_sz src_sz. _` (mp_tac o Q.SPECL [`type_memory_bytes ce dt`, `type_memory_bytes ce st`])) >>
  simp[] >>
  first_x_assum drule >> disch_tac >>
  first_x_assum drule >> disch_tac >>
  rename1 `compile_with_byte_offset dst doff a = (dp,a1)` >>
  rename1 `compile_with_byte_offset src soff a1 = (sp,a2)` >>
  `!k. k < LENGTH a1.cs_current_insts /\
       (EL k a1.cs_current_insts).inst_opcode = ALLOCA ==>
       a1.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
       EL k a1.cs_current_insts = EL k a.cs_current_insts`
    by metis_tac[typed_prefix_simple] >>
  `!k. k < LENGTH a2.cs_current_insts /\
       (EL k a2.cs_current_insts).inst_opcode = ALLOCA ==>
       a2.cs_current_bb = a1.cs_current_bb /\ k < LENGTH a1.cs_current_insts /\
       EL k a2.cs_current_insts = EL k a1.cs_current_insts`
    by metis_tac[typed_prefix_simple] >>
  metis_tac[typed_prefix_trans]
QED
Resume typed_store_prefix_mutual[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- metis_tac[typed_prefix_simple] >>
  qpat_x_assum `!dst_elem_sz src_elem_sz dst src. _` kall_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, new_block_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED
Resume typed_store_prefix_mutual[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_store_memory_typed_def] >>
  qpat_x_assum `!dst_elem_sz src_elem_sz dst src. _` kall_tac >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st`
  >- (simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
           compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
           fresh_id_def, fresh_var_def, emit_def, mk_inst_def] >>
      strip_tac >> match_mp_tac typed_prefix_append >> gvs[APPEND_ASSOC]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, new_block_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED
Resume typed_store_prefix_mutual[struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  fs[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_tac >>
  first_x_assum drule >> disch_tac >>
  rename1 `compile_with_byte_offset dst doff a = (dp,a1)` >>
  rename1 `compile_with_byte_offset src soff a1 = (sp,a2)` >>
  `!k. k < LENGTH a1.cs_current_insts /\
       (EL k a1.cs_current_insts).inst_opcode = ALLOCA ==>
       a1.cs_current_bb = a.cs_current_bb /\ k < LENGTH a.cs_current_insts /\
       EL k a1.cs_current_insts = EL k a.cs_current_insts`
    by metis_tac[typed_prefix_simple] >>
  `!k. k < LENGTH a2.cs_current_insts /\
       (EL k a2.cs_current_insts).inst_opcode = ALLOCA ==>
       a2.cs_current_bb = a1.cs_current_bb /\ k < LENGTH a1.cs_current_insts /\
       EL k a2.cs_current_insts = EL k a1.cs_current_insts`
    by metis_tac[typed_prefix_simple] >>
  metis_tac[typed_prefix_trans]
QED
Finalise typed_store_prefix_mutual

Theorem typed_store_endpoint_history:
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  fn_has_code sa sb fn /\ alloca_history fn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  t.vs_allocas = s.vs_allocas ==> alloca_history fn t
Proof
  strip_tac >> drule (cj 1 typed_store_prefix_mutual) >> disch_tac >>
  fs[fn_has_code_def, alloca_history_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >>
  strip_tac >> gvs[get_instruction_def, EL_APPEND_EQN] >>
  qpat_x_assum `!k. _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!bb' k'. _` (qspecl_then [`bb`, `k`] mp_tac) >>
  simp[EL_APPEND_EQN] >> gvs[]
QED
