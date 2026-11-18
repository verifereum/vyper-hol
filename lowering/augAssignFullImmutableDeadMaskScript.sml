Theory augAssignFullImmutableDeadMask
Ancestors
  bodySim exprSimHypsDefs ctorDeployDeadSectionFrame abiCallerTypeEnv
  typedMemoryCopy structFieldsProps valueEncodingProps valueEncodingProofs
  immSectionDead ctorDeployDeadSection
  abiCanonicalHeadSize vyperContext finite_map list

Theorem augassign_immutable_word_dead_mask:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\ cx_tops cx = tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  off = compute_immutables_len
    (get_struct_fields (make_struct_fields_map tops)) pre /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv /\ off + 32 <= lo /\
  (!q. q < lo /\ q IN tm ==>
    imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) q) ==>
  !q. q < lo /\ q IN (tm DIFF {j | off <= j /\ j < off + 32}) ==>
    imm_section_dead (cx_tops cx)
      (mem_bytes_at 0 lo (mstore off w s).vs_memory) q
Proof
  strip_tac >>
  `type_env tops SUBMAP get_tenv cx` by
    (`ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
       fs[body_inv_def] >>
     simp[get_tenv_def, type_env_all_modules_def, type_env_def,
          finite_mapTheory.SUBMAP_FUNION]) >>
  rpt gen_tac >> strip_tac >>
  `imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) q` by
    (first_x_assum irule >> fs[]) >>
  pop_assum mp_tac >> pure_rewrite_tac[imm_section_dead_def] >>
  disch_then (qx_choosel_then
    [`pre2`,`vis2`,`name2`,`ty2`,`slot2`,`post2`,`tv2`] strip_assume_tac) >>
  `evaluate_type (get_tenv cx) ty2 = SOME tv2` by
    metis_tac[abi_caller_type_submap] >>
  `type_memory_bytes cenv ty2 = type_memory_size tv2` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty2 =
    type_memory_size tv2` by
    (fs[body_inv_def] >> metis_tac[type_mem_bytes_type_memory_bytes]) >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
   pre2 ++ VariableDecl vis2 Immutable name2 ty2 slot2 :: post2` by
    metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac
  >- (`type_memory_size tv = 32` by metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
      gvs[] >>
      rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
      drule (cj 1 mem_dead_bytes_range) >> strip_tac >> fs[] >> decide_tac) >>
  `type_memory_size tv = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
  qmatch_asmsub_abbrev_tac `mem_dead_bytes _ off2 tv2 q` >>
  `off2 + type_memory_size tv2 <= off \/ off + 32 <= off2` by
    (ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
     fs[Abbr `off2`] >> decide_tac) >>
  `mem_dead_bytes (mem_bytes_at 0 lo (mstore off w s).vs_memory) off2 tv2 =
   mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off2 tv2` by
    (irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
     rpt gen_tac >> strip_tac >>
     `j < lo` by metis_tac[LENGTH_mem_bytes_at] >>
     `mem_bytes_at j 1 (mstore off w s).vs_memory =
      mem_bytes_at j 1 s.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[EL_mem_bytes_at, IgnAsm `off = _`, IgnAsm `tops = _`]) >>
  qexistsl_tac [`pre2`,`vis2`,`name2`,`ty2`,`slot2`,`post2`,`tv2`] >>
  unabbrev_all_tac >> metis_tac[]
QED
