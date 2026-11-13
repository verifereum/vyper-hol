(* The joint typed memory copy of a bytestring: its length word and data. *)
Theory typedCopyOriginPtrBytes
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy
  bodyCopyMemoryBase representationCleanPtr robustCopyTransportPtr
  valueCopy venomInstProofs context emitHelper compileEnv fragExec rich_list
  contextCodegenRel memLocDefs

Theorem compile_store_bytestring_inst_seq_ptr[local]:
  compile_store_bytestring (Var xs) (Var xd) sa = ((),sb) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME a /\ lookup_var xd s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword (:256) /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr
      (<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>) lo ctx func PG G tn
      (emitted_insts sa sb) s Gf tnf /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
       (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >>
  `!p k. not_fresh_at sa p ==>
     p <> STRING #"%" (toString (sa.cs_next_var + k))` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  `!id tmp. ptr_inst_ok
      (<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>) lo 0 ctx func G tn
      (mk_inst id MLOAD [Var xs] [tmp]) s` by
    (rpt gen_tac >>
     gvs[ptr_covers_def] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, venomStateTheory.eval_operand_def] >>
     conj_tac
     >- (rpt strip_tac >> gvs[mem_read_ops_def] >>
         goal_assum (drule_at Any) >> decide_tac) >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_read1_def,
          venomStateTheory.eval_operand_def,
          venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def, LET_THM] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND1] >>
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
       venomStateTheory.eval_operand_def] >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
     gen_tac >> Cases_on `x < 32` >> simp[] >>
     first_x_assum irule >> decide_tac) >>
  `!tmp w. new_site_bytes s (update_var tmp w s) = {}` by
    simp[new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def,
       venomStateTheory.update_var_def] >>
  suspend "rounding_not"
QED

(* Each arithmetic instruction checks its operands, then normalizes its ghosts. *)
Resume compile_store_bytestring_inst_seq_ptr[rounding_not]:
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure1_def,
       venomStateTheory.eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func G1 tn1 i1 s1` >>
  `ptr_inst_ok D lo fuel ctx func G1 tn1 i1 s1` by
    (simp[Abbr `i1`, Abbr `s1`, Abbr `tn1`,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, allocas_from_def,
          venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_pure1_def,
          venomStateTheory.eval_operand_def, venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[allocas_from_def, Abbr `fuel`] >>
     metis_tac[]) >>
  simp[] >>
  `!tmp w. new_site_bytes s1 (update_var tmp w s1) = {}` by
    simp[new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `i1`, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def] >>
  simp[Abbr `s1`, Abbr `tn1`, Abbr `G1`, venomStateTheory.update_var_def] >>
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "rounding_add_length"
QED

Resume compile_store_bytestring_inst_seq_ptr[rounding_add_length]:
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func G2 tn2 i2 s2` >>
  `ptr_inst_ok D lo fuel ctx func G2 tn2 i2 s2` by
    (simp[Abbr `i2`, Abbr `s2`, Abbr `tn2`,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, allocas_from_def,
          venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_pure2_def,
          venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[allocas_from_def, Abbr `fuel`]
     >~ [`op <> Var _`] >- (Cases_on `op` >> simp[SF DISJ_ss]) >>
     metis_tac[]) >>
  simp[] >>
  `!tmp w. new_site_bytes s2 (update_var tmp w s2) = {}` by
    simp[new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `i2`, Abbr `G2`, Abbr `tn2`, Abbr `s2`,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.update_var_def] >>
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "rounding_mask"
QED

Resume compile_store_bytestring_inst_seq_ptr[rounding_mask]:
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func G3 tn3 i3 s3` >>
  `ptr_inst_ok D lo fuel ctx func G3 tn3 i3 s3` by
    (simp[Abbr `i3`, Abbr `s3`, Abbr `tn3`,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, allocas_from_def,
          venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_pure2_def,
          venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[allocas_from_def, Abbr `fuel`]
     >~ [`op <> Var _`] >-
       (Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> gvs[]) >>
     metis_tac[]) >>
  simp[] >>
  `!tmp w. new_site_bytes s3 (update_var tmp w s3) = {}` by
    simp[new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `i3`, Abbr `G3`, Abbr `tn3`, Abbr `s3`,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.update_var_def] >>
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "rounding_add_header"
QED

Resume compile_store_bytestring_inst_seq_ptr[rounding_add_header]:
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func G4 tn4 i4 s4` >>
  `ptr_inst_ok D lo fuel ctx func G4 tn4 i4 s4` by
    (simp[Abbr `i4`, Abbr `s4`, Abbr `tn4`,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, allocas_from_def,
          venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.exec_pure2_def,
          venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[allocas_from_def, Abbr `fuel`]
     >~ [`op <> Var _`] >-
       (Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> gvs[]) >>
     metis_tac[]) >>
  simp[] >>
  `!tmp w. new_site_bytes s4 (update_var tmp w s4) = {}` by
    simp[new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `i4`, Abbr `G4`, Abbr `tn4`, Abbr `s4`,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.update_var_def] >>
  `w2n (((n2w len:bytes32) + 31w && ~31w) + 32w) =
    32 * ((len + 31) DIV 32) + 32` by
    (qspec_then `len` mp_tac bytestring_copy_len_word_exact >>
     pure_rewrite_tac[vfmConstantsTheory.word_size_def] >>
     (impl_tac >- decide_tac) >> simp[]) >>
  `!k. sa.cs_next_var <= k ==>
       STRING #"%" (toString k) <> xs /\ STRING #"%" (toString k) <> xd` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  `STRING #"%" (toString sa.cs_next_var) <> xs /\
   STRING #"%" (toString sa.cs_next_var) <> xd` by simp[] >>
  simp[Once inst_seq_ptr_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  suspend "copy_check"
QED

Resume compile_store_bytestring_inst_seq_ptr[copy_check]:
  qmatch_goalsub_abbrev_tac `ptr_inst_ok D lo fuel ctx func G5 tn5 i5 s5` >>
  `ptr_inst_ok D lo fuel ctx func G5 tn5 i5 s5` by
    (simp[Abbr `i5`, Abbr `s5`, Abbr `tn5`, Abbr `G5`,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, mem_read_ops_def, mem_write_ops_def,
          venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
     gvs[ptr_covers_def, op_taint_def, venomStateTheory.lookup_var_def] >>
     simp[codegenRelTheory.sized_source_write_range_def,
          venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, op_prov_def,
          finite_mapTheory.FLOOKUP_DRESTRICT,
          venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomExecSemanticsTheory.mcopy_def, allocas_from_def]
     >-
       (conj_tac >-
          (gen_tac >> Cases_on `op` >> simp[] >>
           rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
        gvs[allocas_from_def]) >>
     simp[]) >>
  suspend "final_ghosts"
QED

Resume compile_store_bytestring_inst_seq_ptr[final_ghosts]:
  simp[venomStateTheory.lookup_var_def, inst_seq_ptr_def] >>
  simp[Abbr `i5`, Abbr `G5`, Abbr `tn5`, Abbr `s5`,
       step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def,
       imm_taint_def, adopt_reset_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[venomStateTheory.lookup_var_def,
      codegenRelTheory.sized_source_write_range_def,
      venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[new_site_bytes_def, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.expand_memory_def] >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_DEF, SF CONJ_ss] >>
  rpt strip_tac >>
  `!k. sa.cs_next_var <= k ==> STRING #"%" (toString k) <> p` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
       op_taint_def]
QED

Finalise compile_store_bytestring_inst_seq_ptr

Theorem typed_copy_origin_ptr_bytestring_entry:
  !cenv tenv ctx dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_bytestring_type dty /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v ==>
    typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_copy_bytestring_source >> strip_tac >>
  `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
     (?cap. tv = BaseTV (BytesT (Dynamic cap))) \/
     (?cap. tv = BaseTV (StringT cap))` by
    (Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> rw[is_bytestring_type_def, vyperValueTheory.evaluate_type_def]) >>
     rw[vyperValueTheory.evaluate_type_def]) >>
  `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. stv = BaseTV (StringT cap))` by metis_tac[] >>
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[] >>
  `~is_word_type dty` by
    (Cases_on `dty` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  simp[typed_copy_origin_ptr_entry_def, valueEncodingTheory.type_memory_size_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  qmatch_asmsub_rename_tac `allocas_from lo state` >>
  FIRST [rename1 `BytesV bs` >> qabbrev_tac `len = LENGTH bs`,
         rename1 `StringV str` >> qabbrev_tac `len = STRLEN str`] >>
  `word_size len <= word_size cap /\ word_size len <= word_size cap'` by
    (conj_tac >> irule exprSimPropsTheory.word_size_monotone >> simp[Abbr `len`]) >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= state.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= state.vs_alloca_next` by decide_tac >>
  `mem_word_at (w2n sw) state.vs_memory = n2w len` by
    (qpat_x_assum `!mem. _` (qspec_then `state.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def,
          valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
  `!mem. mem_agree_outside tn.t_mem state.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w len` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
     simp[valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
  drule representationCleanPtrTheory.robust_mem_word_at_clean >> strip_tac >>
  `mload (w2n sw) state = n2w len` by
    gvs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `ptr_covers G tn xs state (32 + 32 * word_size len) /\
   ptr_covers G tn xd state (32 + 32 * word_size len)` by
    (gvs[ptr_covers_def] >> conj_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  `len + 31 < dimword (:256)` by
    (`len + 31 < ((len + 31) DIV 32 + 1) * 32` by
       simp[GSYM arithmeticTheory.DIV_LE_X] >>
     qpat_x_assum `32 + 32 * word_size len < _` mp_tac >>
     pure_rewrite_tac[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `?Gf tnf.
     inst_seq_ptr
       (<|d_stor := K (K {}); d_trans := K (K {});
          d_imm := K {}; d_ret := K {}|>) lo ctx func PG G tn
       (emitted_insts sa sb) state Gf tnf /\
     tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
     tnf.t_trans = tn.t_trans /\
     (!i. i < 32 + 32 * word_size len ==>
       (w2n dw + i IN tnf.t_mem <=> w2n sw + i IN tn.t_mem)) /\
     (!i. ~(w2n dw <= i /\ i < w2n dw + (32 + 32 * word_size len)) ==>
       (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
     (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p))` by
    (irule compile_store_bytestring_inst_seq_ptr >>
     simp[vfmConstantsTheory.word_size_def] >> conj_tac
     >- (qexists_tac `len` >> `len < dimword (:256)` by decide_tac >> simp[]) >>
     qexistsl_tac [`xd`, `xs`] >>
     gvs[vfmConstantsTheory.word_size_def]) >>
  drule store_bytestring_run_exact >>
  disch_then (qspecl_then [`state`, `sw`, `dw`, `len`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) state` by
    (irule compile_store_bytestring_body_mem_ok >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`dw`, `Var xd`, `Var xs`] >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `?bb. lookup_block state.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP state.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, exprLoweringPropsTheory.same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND1,
                     venomInstTheory.mk_inst_def]) >>
  qexistsl_tac [`t with vs_inst_idx := state.vs_inst_idx + LENGTH (emitted_insts sa sb)`,
                `Gf`, `tnf`] >>
  simp[] >>
  (conj_tac
   >- (qpat_x_assum `!explicit. gas_origin_ptr_path _ _ _ _`
         (qspec_then `explicit` mp_tac) >> simp[]) >>
   conj_tac
   >- (irule valueCopyTheory.mcopy_val_in_memory >>
       simp[loweringPostsTheory.val_footprint_def, Abbr `len`,
            exprSimPropsTheory.le_word_size_mul] >>
       qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _`
         (qspec_then `state.vs_memory` mp_tac) >>
       simp[mem_agree_outside_def, valueEncodingDefsTheory.val_in_memory_def]) >>
   conj_tac
   >- (simp[typed_copy_state_frame_def] >> conj_tac
       >- gvs[venomStateTheory.venom_state_component_equality] >>
       conj_tac >- gvs[venomStateTheory.lookup_var_def] >>
       simp[typed_copy_frame_def] >> conj_tac
       >- (rpt gen_tac >> strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
           decide_tac) >>
       simp[venomExecSemanticsTheory.mcopy_def,
            immutableMemoryFrameTheory.immutable_write_memory_capacity, arithmeticTheory.MAX_DEF]) >>
   conj_tac
   >- gvs[venomStateTheory.venom_state_component_equality] >>
   conj_tac
   >- gvs[venomStateTheory.venom_state_component_equality,
          exprLoweringPropsTheory.same_blocks_def] >>
   rpt strip_tac >>
   irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
   simp[] >> goal_assum (drule_at Any) >>
   qexistsl_tac [`state.vs_memory`, `32 + 32 * word_size len`, `w2n sw`, `tn.t_mem`] >>
   conj_tac
   >- (rpt strip_tac >>
       qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
       simp[valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
   conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
   conj_tac
   >- simp[loweringPostsTheory.val_footprint_def, Abbr `len`,
           exprSimPropsTheory.le_word_size_mul] >>
   POP_ASSUM_LIST (K all_tac) >>
   `32 + 32 * word_size len = 32 * word_size len + 32` by decide_tac >>
   asm_rewrite_tac[] >>
   pure_rewrite_tac[valueEncodingDefsTheory.mem_bytes_at_def,
                    venomMemPropsTheory.mcopy_padded_read] >> REFL_TAC)
QED
