Theory bodyFullBuiltinUint2StrBlocks
Ancestors
  bodyPtrDefs bodyPtrBytestringBuiltinsCalldataCopy
  immutableMemoryFrame valueEncodingProps loweringStateRelDefs
  ptrDiscipline venomState finite_map words list pred_set byte
  localPtrsProps exprSimProps exprSimUint2Str fragGasSeqPtr
  bodyPtrBytestringBuiltinsUintGhost ptrSafeRun venomExecSemantics venomInst
  exprLoweringProps emitHelperProps codegenRel contextCodegenRel bodyFullUnwrapRun

Theorem u2s_clean_store_ghost_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  lo <= b /\ b <= at /\ at+32 <= b+sz ==>
  ghost_inv_at D lo d cenv cx es G
    (tn with t_mem := tn.t_mem DIFF {j | at <= j /\ j < at+32})
    (mstore at w s)
Proof
  strip_tac >>
  `LENGTH (word_to_bytes w T) = 32` by
    simp[LENGTH_word_to_bytes, dimword_def,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `mem_bytes_at 0 lo (mstore at w s).vs_memory =
   mem_bytes_at 0 lo s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_covers G tn p s sz'` by metis_tac[] >>
      conj_tac
      >- gvs[ptr_covers_def, op_taint_def, mstore_def,
             write_memory_with_expansion_def, lookup_var_def] >>
      rpt strip_tac >>
      `lookup_var p s = SOME w'` by
        gvs[lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
      `local_region cenv es.scopes s name (w2n w') sz'` by
        (simp[local_region_def] >> metis_tac[]) >>
      drule_all local_ptrs_rel_alloca_disjoint >> disch_tac >>
      `val_wf entry.type entry.value /\
       val_footprint entry.type entry.value <= sz'` by
        (fs[local_ptrs_rel_def] >>
         qpat_x_assum `!name' entry' p' sz''. _` drule_all >> strip_tac >>
         drule val_footprint_le >> simp[]) >>
      `w2n w' + val_footprint entry.type entry.value <= at \/
       at + 32 <= w2n w'` by (fs[regions_disjoint_def] >> decide_tac) >>
      gvs[immutable_mstore_as_write] >>
      irule write_memory_robust_exterior >> simp[] >>
      qexistsl_tac [`word_to_bytes w T`, `at`, `s`, `tn.t_mem`] >>
      simp[LENGTH_word_to_bytes, dimword_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
          mstore_def, write_memory_with_expansion_def, lookup_var_def])
  >> gvs[op_taint_def, stor_taint_ok_at_def, allocas_from_def,
         mstore_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem u2s_clean_scalar_seq_cons:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id opc ops [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule uint_scalar_ghost >> simp[update_var_def] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (`!v. MEM (Var v) ops ==> FLOOKUP G v = NONE` by
       (rpt strip_tac >> first_x_assum drule >> simp[op_prov_def]) >>
     gvs[] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     gvs[update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >>
  gvs[mk_inst_def]
QED

Theorem u2s_clean_assign_seq_cons:
  op_prov G op = NONE /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id ASSIGN [op] [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule uint_assign_ghost >> simp[update_var_def]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id ASSIGN [op] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >> gvs[mk_inst_def]
QED

