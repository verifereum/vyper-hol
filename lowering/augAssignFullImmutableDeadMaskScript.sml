Theory augAssignFullImmutableDeadMask
Ancestors
  bodySim exprSimHypsDefs ctorDeployDeadSectionFrame abiCallerTypeEnv
  typedMemoryCopy structFieldsProps valueEncodingProps valueEncodingProofs
  immSectionDead ctorDeployDeadSection
  abiCanonicalHeadSize vyperContext finite_map list
  bodyInvSplit bodySimModsProps bodyInvCodeProps bodyInvMetadataProps
  immutableRegionTypingProps immutableRegionDeadProps compileUnit alist
  placeMemoryPathRebuild mstoreRestorePtr assignTuplePtrStoreWord
  immutablePrefixDead valueMemoryTransport
  valueTypingMemoryProps stmtSimDeclStore exprSimProps

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

(* Reconstruct a permitted pre-store memory by restoring the old word. *)
Theorem augassign_immutable_path_robust_write:
  value_has_type itv old /\ well_formed_type_value itv /\
  mem_path_offset itv path = SOME (k,ptv) /\
  value_has_type ptv v /\ store_lays_out ptv ptv v /\
  assign_subscripts itv old path (Replace v) = INL new /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory itv old off m) ==>
  !mem. mem_agree_outside (dirty DIFF {i | off+k <= i /\ i < off+k+32})
    (mstore (off+k) (typed_val_to_w256 ptv v) s).vs_memory mem ==>
  val_in_memory itv new off mem
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule clean_mstore_restore_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory itv old off mix` by metis_tac[] >>
  qabbrev_tac `stored =
    (mstore (off+k) (typed_val_to_w256 ptv v) (s with vs_memory := mix)).vs_memory` >>
  `!b n. mem_bytes_at b n stored = mem_bytes_at b n mem` by
    (irule memory_byte_agree_window >> simp[Abbr `stored`]) >>
  `val_in_memory ptv v (off+k) mem` by
    (drule store_lays_out_robust_ptr >> disch_then irule >>
     qexistsl_tac [`dirty`,`s`] >> first_assum ACCEPT_TAC) >>
  `val_in_memory ptv v (off+k) stored` by
    metis_tac[val_in_memory_transport,value_has_type_memory_wf] >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  `!b n. b+n <= off+k \/ off+k+type_memory_size ptv <= b ==>
    mem_bytes_at b n stored = mem_bytes_at b n mix` by
    (rpt gen_tac >>
     qpat_assum `type_memory_size ptv = 32` (fn sz => rewrite_tac[sz]) >>
     disch_tac >>
     drule_then (qspecl_then [`typed_val_to_w256 ptv v`,`s with vs_memory := mix`] mp_tac)
       mstore_mem_bytes_at_disjoint >>
     simp_tac bool_ss [Abbr `stored`,venomStateTheory.venom_state_accfupds,combinTheory.K_THM]) >>
  `val_in_memory itv new off stored` by
    (irule typed_memory_replace_path_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`old`,`k`,`mix`,`path`,`ptv`,`v`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!b n. mem_bytes_at b n stored = mem_bytes_at b n mem`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     qpat_assum `!b n. _ ==> mem_bytes_at b n stored = mem_bytes_at b n mix`
       (qspecl_then [`b`,`n`] match_mp_tac) >> decide_tac) >>
  `value_has_type itv new` by
    (drule mem_path_offset_sound >> strip_tac >>
     metis_tac[assign_subscripts_type_path_preserves_type]) >>
  metis_tac[val_in_memory_transport,value_has_type_memory_wf]
QED

Theorem augassign_immutable_path_dead_mask:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods src id off (type_memory_size itv) /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME itv /\
  off + type_memory_size itv <= lo /\
  mem_path_offset itv path = SOME (k,ptv) /\ type_memory_size ptv = 32 /\
  well_formed_type_value itv /\ value_has_type itv new /\
  (!m. mem_agree_outside (dirty DIFF {j | off+k <= j /\ j < off+k+32})
     (mstore (off+k) w s).vs_memory m ==> val_in_memory itv new off m) /\
  (!i. i < lo /\ i IN dirty ==>
    imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) i) ==>
  !i. i < lo /\ i IN (dirty DIFF {j | off+k <= j /\ j < off+k+32}) ==>
    imm_section_dead_mods cenv (mem_bytes_at 0 lo (mstore (off+k) w s).vs_memory) i
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
  drule mem_path_offset_sound >> strip_tac >>
  `?src1 id1 off1 ty1 tv.
    immutable_region_mods mods src1 id1 off1 (type_memory_size tv) /\
    FLOOKUP env.bare_globals (src1,id1) = SOME ty1 /\
    evaluate_type (get_tenv cx) ty1 = SOME tv /\
    mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off1 tv i` by
    (first_x_assum irule >> fs[pred_setTheory.IN_DIFF]) >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  (Cases_on `(src1,id1) = (src,id)`
   >- (gvs[] >>
       `off1 = off` by
         metis_tac[optionTheory.SOME_11,compileEnvTheory.var_location_11] >>
       gvs[] >>
       drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
       qexistsl_tac [`src`,`id`,`off`,`ty`,`itv`] >> simp[] >>
       irule immutable_prefix_interior_dead >> simp[] >>
       qexistsl_tac [`dirty DIFF {j | k+off <= j /\ j < k+(off+32)}`,`new`] >>
       simp[pred_setTheory.IN_DIFF] >> decide_tac) >>
   `regions_disjoint off1 (type_memory_size tv) off (type_memory_size itv)` by
     metis_tac[] >>
   `mem_dead_bytes (mem_bytes_at 0 lo (mstore (off+k) w s).vs_memory) off1 tv =
    mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off1 tv` by
     (irule mem_dead_bytes_frame >> reverse conj_tac >- simp[] >>
      rpt gen_tac >> strip_tac >>
      `j < lo` by metis_tac[LENGTH_mem_bytes_at] >>
      `mem_bytes_at j 1 (mstore (off+k) w s).vs_memory =
       mem_bytes_at j 1 s.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
   qexistsl_tac [`src1`,`id1`,`off1`,`ty1`,`tv`] >> fs[])
QED
