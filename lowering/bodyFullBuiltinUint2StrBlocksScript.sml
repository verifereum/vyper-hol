Theory bodyFullBuiltinUint2StrBlocks
Ancestors
  bodyPtrDefs bodyPtrBytestringBuiltinsCalldataCopy
  immutableMemoryFrame valueEncodingProps loweringStateRelDefs
  ptrDiscipline venomState finite_map words list pred_set byte
  localPtrsProps exprSimProps

Theorem u2s_clean_store_kept_at:
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es a G0 tn0 s0 G
    (tn with t_mem := tn.t_mem DIFF {j | at <= j /\ j < at+32})
Proof
  simp[ghost_kept_at_def, op_taint_def] >> metis_tac[]
QED

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
