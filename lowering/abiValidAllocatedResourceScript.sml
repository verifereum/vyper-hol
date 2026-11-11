(* Owned allocation-free decoder writes preserve executable resources. *)
Theory abiValidAllocatedResource
Ancestors
  abiValidAllocatedObservations abiValidAllocatedContract abiDecoderFrame
  ctorAbiActualWorld abiDecoderReentry abiDecoderContract
  abiMalformedRecursiveInterface venomMemDefs
  localPtrsProps loweringSlice exprLoweringProps compileEnv venomState
  finite_map words list arithmetic

Theorem abi_valid_allocated_scratch_free_resource:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  fn_inst_ids_distinct func /\
  abi_malformed_destination func cenv es.scopes dstid d n s /\
  abi_decode_frame d n s t /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA) code /\
  run_inst_seq code s = OK t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code` by fs[EVERY_MEM] >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_no_alloca >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >> qpat_x_assum `!op w. _ ==> _` (qspec_then `Var x` mp_tac) >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def,
       eval_operand_def]) >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     `?w. lookup_var p s = SOME w` by (fs[local_ptrs_rel_def] >> metis_tac[]) >>
     `not_fresh_at st p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes t name b sz ==>
     local_region cenv es.scopes s name b sz` by
    (fs[local_region_def] >> metis_tac[]) >>
  qhdtm_assum `abi_malformed_destination`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_destination_def]) >>
  `!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     regions_disjoint b sz lb lsz` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     reverse conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >> gvs[]) >>
     rpt strip_tac >> sym_tac >>
     qhdtm_assum `abi_decode_frame`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     first_x_assum match_mp_tac >>
     qpat_x_assum `!name lb lsz. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     reverse conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
     fs[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac >>
     `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
     qhdtm_assum `abi_decode_frame`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     first_x_assum match_mp_tac >> fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule stmt_state_rel_allocas_frame >> conj_tac
     >- (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
         reverse conj_tac >- fs[stmt_state_rel_def] >> rpt strip_tac >>
         `not_fresh_at st x` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         `lookup_var x s = SOME 0w` by
           (fs[stmt_state_rel_def, immutable_base_zero_alt, lookup_var_def] >> metis_tac[]) >>
         metis_tac[]) >>
     conj_tac
     >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >> simp[] >>
         reverse conj_tac >- fs[stmt_state_rel_def] >> metis_tac[]) >>
     reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
     irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >>
     simp[] >> fs[stmt_state_rel_def]) >>
  simp[abi_malformed_resource_post_def] >> rpt strip_tac >>
  qhdtm_assum `abi_decode_frame`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  first_x_assum match_mp_tac >>
  `B+cap <= b \/ b+sz <= B` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >> decide_tac
QED
