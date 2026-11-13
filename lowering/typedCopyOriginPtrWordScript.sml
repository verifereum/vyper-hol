(* The joint typed memory copy of a word: one load, one store. *)
Theory typedCopyOriginPtrWord
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy
  compileEnv vyperValue valueEncoding representationCleanPtr

Theorem typed_copy_origin_ptr_word_entry:
  !cenv tenv ctx dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    is_word_type dty /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v ==>
    typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v
Proof
  rpt strip_tac >>
  drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
  simp[typed_copy_origin_ptr_entry_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size dtv = 32` by
    (qpat_x_assum `is_word_type dty` mp_tac >>
     qpat_x_assum `evaluate_type tenv dty = SOME dtv` mp_tac >>
     Cases_on `dty` >> simp[is_word_type_def]
     >~ [`FlagT`]
     >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
         gvs[type_memory_size_def]) >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_word_type_def, evaluate_type_def, type_memory_size_def] >>
     rpt strip_tac >> gvs[type_memory_size_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_word_type_def, evaluate_type_def, type_memory_size_def,
         AllCaseEqs()]) >>
  gnvs[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = typed_val_to_w256 dtv v` by
    (rpt strip_tac >> first_x_assum drule >>
     metis_tac[exprSimPropsTheory.val_in_memory_word]) >>
  `!i. w2n sw <= i /\ i < w2n sw + 32 ==> i NOTIN tn.t_mem` by
    (drule representationCleanPtrTheory.robust_mem_word_at_clean >> simp[]) >>
  `!p. not_fresh_at sa p ==> STRING #"%" (toString sa.cs_next_var) <> p` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw` by
    simp[venomStateTheory.eval_operand_def] >>
  drule typed_copy_word_run_seq >> simp[] >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [Var xs] [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [Var xd; Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once contextTheory.compile_store_memory_typed_def] >>
     simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, compileEnvTheory.comp_return_def] >>
     strip_tac >> gvs[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK raw` >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [ld;st]` >>
  qabbrev_tac `tmp = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var tmp (mload (w2n sw) s) s` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G ld u` >>
  qabbrev_tac `tn1 = step_taint ld s u tn` >>
  qabbrev_tac `r = mstore (w2n dw) (mload (w2n sw) s) q` >>
  qabbrev_tac `G2 = step_prov PG G1 st r` >>
  qabbrev_tac `tn2 = step_taint st q r tn1` >>
  `step_inst_base ld s = OK u /\ step_inst_base st q = OK r` by
    (simp[Abbr `ld`, Abbr `st`, Abbr `u`, Abbr `q`, Abbr `r`, Abbr `tmp`,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read1_def,
      venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def,
      emitHelperPropsTheory.lookup_var_update_var] >> metis_tac[]) >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_imm = tn.t_imm /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `ld`, Abbr `u`,
      step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      venomInstTheory.mk_inst_def, mem_word_taint_def, mem_taint_def,
      new_site_bytes_def, step_writes_def, written_taint_def,
      codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
      venomStateTheory.update_var_def, store_taint_def, adopt_reset_def,
      finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DEF,
      pred_setTheory.EXTENSION, imm_taint_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `(x:num) < 32` >> simp[] >>
         first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
  `ptr_covers G1 tn1 xd q 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `ld`, Abbr `u`, Abbr `q`,
      ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
      step_taint_def, set_var_taint_def, op_taint_def,
      venomInstTheory.mk_inst_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT,
      finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[ptr_covers_def, venomStateTheory.lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `inst_seq_ptr
    (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>)
    lo ctx func PG G tn [ld;st] s G2 tn2` by
    (qpat_x_assum `_ \/ _` kall_tac >>
     qpat_x_assum `s.vs_inst_idx = _` kall_tac >>
     simp[inst_seq_ptr_def, Abbr `G2`, Abbr `tn2`, Abbr `G1`, Abbr `tn1`,
          Abbr `q`] >>
     conj_tac
     >- (gvs[ptr_covers_def] >>
         simp[Abbr `ld`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           venomStateTheory.eval_operand_def] >>
         conj_tac >- (rpt strip_tac >> gvs[] >>
           gvs[memLocDefsTheory.mem_read_ops_def] >> metis_tac[]) >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
         asm_simp_tac bool_ss [venomExecSemanticsTheory.step_inst_base_opcode_eqs,
           venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds,
           venomInstTheory.opcode_case_def, combinTheory.K_THM] >>
         simp[venomExecSemanticsTheory.exec_read1_def, venomStateTheory.eval_operand_def,
           AllCaseEqs(), venomStateTheory.mload_def, venomStateTheory.update_var_def] >>
         rpt strip_tac >> gvs[memLocDefsTheory.mem_read_ops_def] >> metis_tac[]) >>
     gvs[ptr_covers_def] >>
     simp[Abbr `st`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def] >>
     conj_tac
     >- (Cases_on `lookup_var tmp u` >>
         simp[venomStateTheory.lookup_var_def] >>
         rpt strip_tac >> gvs[venomStateTheory.lookup_var_def] >>
         gvs[memLocDefsTheory.mem_write_ops_def] >> metis_tac[]) >>
     conj_tac >- (rpt strip_tac >> gvs[]) >>
     conj_tac
     >- (gvs[Abbr `u`, ptrDisciplineTheory.allocas_from_def,
              venomStateTheory.update_var_def] >> metis_tac[]) >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_write2_def,
       venomStateTheory.eval_operand_def, AllCaseEqs(), venomStateTheory.mstore_def] >>
     rpt strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok [ld;st] s` by
    (qpat_x_assum `_ \/ _` kall_tac >>
     `tmp <> xd` by metis_tac[] >>
     gvs[venomStateTheory.lookup_var_def] >>
     Cases_on `step_inst_base st u` >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     simp[Abbr `ld`, Abbr `st`, Abbr `u`,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       venomStateTheory.eval_operand_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `_ \/ _` kall_tac >>
     fs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `gas_origin_ptr_path
    (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
      lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (raw with vs_inst_idx := s.vs_inst_idx + 2),G2,tn2)` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_origin_ptr_path >>
     simp[Abbr `ld`, Abbr `st`, venomInstTheory.mk_inst_def] >>
     disch_then irule >>
     gnvs[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  qexistsl_tac [`raw with vs_inst_idx := s.vs_inst_idx + 2`, `G2`, `tn2`] >>
  simp[] >>
  conj_tac
  >- (drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
      simp[Abbr `raw`, Abbr `u`, valueEncodingPropsTheory.mstore_mem_word_at_same,
        GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, venomStateTheory.mstore_def,
        venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def] >>
      first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac >- simp[Abbr `raw`, Abbr `u`, Abbr `tmp`, typed_copy_word_state_frame] >>
  conj_tac >- simp[Abbr `raw`, Abbr `u`, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def] >>
  conj_tac >- (gvs[Abbr `raw`, Abbr `u`, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def,
    exprLoweringPropsTheory.same_blocks_def]) >>
  conj_tac >- simp[Abbr `tn2`, Abbr `st`, step_taint_def,
    venomInstTheory.mk_inst_def, imm_taint_def] >>
  conj_tac >- simp[Abbr `tn2`, Abbr `st`, step_taint_def,
    venomInstTheory.mk_inst_def, store_taint_def, adopt_reset_def] >>
  conj_tac >- simp[Abbr `tn2`, Abbr `st`, step_taint_def,
    venomInstTheory.mk_inst_def, store_taint_def, adopt_reset_def] >>
  `tn2.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (qpat_x_assum `_ \/ _` kall_tac >>
     `tmp <> xd` by metis_tac[] >>
     gvs[venomStateTheory.lookup_var_def] >>
     simp[Abbr `tn2`, Abbr `st`, step_taint_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
       venomInstTheory.mk_inst_def, Abbr `q`, Abbr `r`, Abbr `u`,
       venomStateTheory.mstore_def, venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       pred_setTheory.EXTENSION] >>
     gvs[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at (w2n dw) 32 raw.vs_memory = mem_bytes_at (w2n dw) 32 mem` by
        (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
         rpt strip_tac >> fs[mem_agree_outside_def]) >>
      `mem_word_at (w2n dw) mem = mem_word_at (w2n dw) raw.vs_memory` by
        metis_tac[memoryValueFrameTheory.memory_word_agree, arithmeticTheory.LESS_EQ_REFL] >>
      drule_all exprSimPropsTheory.val_in_memory_word >> strip_tac >>
      simp[Abbr `raw`, valueEncodingPropsTheory.mstore_mem_word_at_same,
        GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      first_x_assum irule >> simp[mem_agree_outside_def]) >>
  rpt strip_tac >>
  `tmp <> p` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`, Abbr `st`, Abbr `ld`,
    step_prov_def, set_prov_def, out_prov_def, step_taint_def, set_var_taint_def,
    op_taint_def, venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT,
    finite_mapTheory.FLOOKUP_UPDATE]
QED
