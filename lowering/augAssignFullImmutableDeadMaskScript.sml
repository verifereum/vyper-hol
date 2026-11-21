Theory augAssignFullImmutableDeadMask
Ancestors
  bodySim exprSimHypsDefs ctorDeployDeadSectionFrame abiCallerTypeEnv
  typedMemoryCopy structFieldsProps valueEncodingProps valueEncodingProofs
  immSectionDead ctorDeployDeadSection
  abiCanonicalHeadSize vyperContext finite_map list
  bodyInvSplit bodySimModsProps bodyInvCodeProps bodyInvMetadataProps
  immutableRegionTypingProps immutableRegionDeadProps compileUnit alist

Theorem augassign_immutable_word_dead_mask_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods src name off 32 /\ off + 32 <= lo /\
  (!q. q < lo /\ q IN tm ==>
    imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) q) ==>
  !q. q < lo /\ q IN (tm DIFF {j | off <= j /\ j < off + 32}) ==>
    imm_section_dead_mods cenv (mem_bytes_at 0 lo (mstore off w s).vs_memory) q
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
  `?src' id off' ity tv.
    immutable_region_mods mods src' id off' (type_memory_size tv) /\
    FLOOKUP env.bare_globals (src',id) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME tv /\
    mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off' tv q` by
    (first_x_assum irule >> fs[pred_setTheory.IN_DIFF]) >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `regions_disjoint off' (type_memory_size tv) off 32` by
    (Cases_on `(src',id) = (src,name)`
     >- (gvs[] >>
         drule_all_then strip_assume_tac
           (Q.INST [`bytes` |-> `32`] immutable_region_mods_type) >>
         `off' = off` by
           metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
         `type_memory_size tv = 32` by metis_tac[optionTheory.SOME_11] >>
         fs[pred_setTheory.IN_DIFF] >>
         drule (cj 1 mem_dead_bytes_range) >> strip_tac >> fs[] >> decide_tac) >>
     metis_tac[]) >>
  `mem_dead_bytes (mem_bytes_at 0 lo (mstore off w s).vs_memory) off' tv =
   mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off' tv` by
    (irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
     rpt gen_tac >> strip_tac >>
     `j < lo` by metis_tac[LENGTH_mem_bytes_at] >>
     `mem_bytes_at j 1 (mstore off w s).vs_memory =
      mem_bytes_at j 1 s.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  qexistsl_tac [`src'`,`id`,`off'`,`ity`,`tv`] >> fs[]
QED

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
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `type_memory_size tv = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_memory_size] >>
  `immutable_region_mods [(NONE,tops)] NONE name off 32` by
    (simp[singleton_immutable_region] >> metis_tac[]) >>
  `cenv.ce_modules = [(NONE,tops)]` by metis_tac[] >>
  qpat_assum `cx_tops cx = tops` (fn main_code =>
    qpat_assum `expr_sim_inv cenv cx env es`
      (strip_assume_tac o REWRITE_RULE [expr_sim_inv_split_def, main_code]) >>
    PURE_REWRITE_TAC [main_code]) >>
  qpat_assum `cenv.ce_modules = [(NONE,tops)]` (fn th =>
    let val dead = GSYM (MATCH_MP imm_section_dead_mods_singleton th) in
      qpat_assum `!q. _ ==> imm_section_dead tops _ q`
        (assume_tac o REWRITE_RULE [dead]) >>
      PURE_REWRITE_TAC [dead]
    end) >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `src` |-> `NONE`]
    augassign_immutable_word_dead_mask_mods) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
