Theory augAssignFullImmutableDeadMask
Ancestors
  bodySim exprSimHypsDefs ctorDeployDeadSectionFrame abiCallerTypeEnv
  typedMemoryCopy structFieldsProps valueEncodingProps valueEncodingProofs
  immSectionDead ctorDeployDeadSection
  abiCanonicalHeadSize vyperContext finite_map list
  bodyInvSplit bodySimModsProps bodyInvCodeProps bodyInvMetadataProps
  immutableRegionTypingProps compileUnit alist

Theorem imm_section_dead_mods_other[local]:
  (!ts. cenv.ce_modules <> [(NONE,ts)]) ==>
  (imm_section_dead_mods cenv sec q <=>
   ?src ts vis id ty slot off tv.
     ALOOKUP cenv.ce_modules src = SOME ts /\
     MEM (VariableDecl vis Immutable id ty slot) ts /\
     FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     evaluate_type (type_env_all_modules cenv.ce_modules) ty = SOME tv /\
     mem_dead_bytes sec off tv q)
Proof
  Cases_on `cenv.ce_modules` >>
  simp[imm_section_dead_mods_def, ALOOKUP_def] >>
  PairCases_on `h` >> Cases_on `t` >> Cases_on `h0` >>
  simp[imm_section_dead_mods_def]
QED

Theorem immutable_region_eval_size[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  ALOOKUP mods src = SOME tops /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  immutable_region_mods mods src name off bytes ==>
  FLOOKUP env.bare_globals (src,name) = SOME ty /\ bytes = type_memory_size tv
Proof
  strip_tac >>
  drule_all_then assume_tac immutable_decl_bare_global_mods >>
  drule_all_then strip_assume_tac immutable_region_mods_type >> gvs[]
QED

Theorem imm_section_dead_mods_regions[local]:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es ==>
  (imm_section_dead_mods cenv sec q <=>
   ?src id off ty tv.
     immutable_region_mods mods src id off (type_memory_size tv) /\
     FLOOKUP env.bare_globals (src,id) = SOME ty /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     mem_dead_bytes sec off tv q)
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then assume_tac contract_inv_struct_fields >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  Cases_on `?ts. mods = [(NONE,ts)]`
  >- (gvs[] >>
      qpat_assum `cenv.ce_modules = [(NONE,ts)]`
        (fn th => REWRITE_TAC [MATCH_MP imm_section_dead_mods_singleton th,
                              imm_section_dead_def]) >>
      eq_tac
      >- (disch_then (qx_choosel_then [`pre`,`vis`,`name`,`ty`,`slot`,`post`,`tv`]
                       strip_assume_tac) >>
          `evaluate_type (get_tenv cx) ty = SOME tv` by
            (qpat_x_assum `ts = _` SUBST_ALL_TAC >>
             fs[vyperContextTheory.type_env_def, type_env_all_modules_def]) >>
          `type_memory_bytes cenv ty = type_memory_size tv` by
            (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
             fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
          `type_mem_bytes (get_struct_fields (make_struct_fields_map ts)) ty =
             type_memory_size tv` by
            (qpat_assum `type_memory_bytes cenv ty = _`
               (assume_tac o REWRITE_RULE [GSYM type_mem_bytes_type_memory_bytes]) >>
             fs[make_struct_fields_map_mods_singleton] >> metis_tac[]) >>
          `immutable_region_mods [(NONE,ts)] NONE name
             (compute_immutables_len (get_struct_fields (make_struct_fields_map ts)) pre)
             (type_memory_size tv)` by
            (simp[singleton_immutable_region] >>
             qexistsl_tac [`pre`,`post`,`vis`,`ty`,`slot`] >>
             simp[] >> metis_tac[]) >>
          `FLOOKUP env.bare_globals (NONE,name) = SOME ty` by
            (irule immutable_decl_bare_global_mods >>
             qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`[(NONE,ts)]`,`slot`,`ts`,`vis`] >>
             fs[ALOOKUP_def] >> simp[]) >>
          qexistsl_tac [`NONE`,`name`,
            `compute_immutables_len (get_struct_fields (make_struct_fields_map ts)) pre`,
            `ty`,`tv`] >>
          metis_tac[]) >>
      disch_then (qx_choosel_then [`src`,`name`,`off`,`ty`,`tv`] strip_assume_tac) >>
      fs[singleton_immutable_region] >>
      `FLOOKUP env.bare_globals (NONE,name) = SOME ty'` by
        (irule immutable_decl_bare_global_mods >>
         qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`[(NONE,ts)]`,`slot`,`ts`,`vis`] >>
         fs[ALOOKUP_def] >> simp[]) >>
      qexistsl_tac [`pre`,`vis`,`name`,`ty'`,`slot`,`post`,`tv`] >>
      gvs[vyperContextTheory.type_env_def, type_env_all_modules_def]) >>
  `!ts. cenv.ce_modules <> [(NONE,ts)]` by (fs[] >> metis_tac[]) >>
  qpat_assum `!ts. cenv.ce_modules <> [(NONE,ts)]` (fn th =>
    qpat_assum `cenv.ce_modules = mods` (fn modules =>
      REWRITE_TAC [REWRITE_RULE [modules] (MATCH_MP imm_section_dead_mods_other th)])) >>
  eq_tac >> strip_tac
  >- (`?bytes. immutable_region_mods mods src id off bytes` by metis_tac[] >>
      `evaluate_type (get_tenv cx) ty = SOME tv` by
        (qpat_assum `get_tenv cx = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >>
      drule_all_then strip_assume_tac immutable_region_eval_size >>
      qexistsl_tac [`src`,`id`,`off`,`ty`,`tv`] >> gvs[]) >>
  qpat_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty'` by
    (irule immutable_decl_bare_global_mods >>
     qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`mods`,`slot`,`tops`,`vis`] >>
     fs[] >> simp[]) >>
  qexistsl_tac [`src`,`tops`,`vis`,`id`,`ty'`,`slot`,`off`,`tv`] >>
  gvs[] >> metis_tac[]
QED

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
