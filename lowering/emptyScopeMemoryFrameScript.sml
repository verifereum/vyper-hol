(* Empty-scope state framing needs byte agreement, not physical memory growth. *)
Theory emptyScopeMemoryFrame
Ancestors
  loweringSlice localPtrsProps exprSimCopy intCallResult
  exprSimProps exprLoweringProps loweringStateRelDefs
  finite_map context compileEnv venomState valueEncodingProps
  exprSimStorageCopy vyperState stmtSimReturn

Theorem immutables_rel_byte_agree[local]:
  !cenv addr src ctor es s t.
    immutables_rel cenv addr src ctor es s /\
    t.vs_data_section = s.vs_data_section /\
    (ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables addr of NONE => FEMPTY
        | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      mem_bytes_at off (type_memory_size tv) t.vs_memory =
        mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
    immutables_rel cenv addr src ctor es t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ctor`
  >- (fs[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name tv v byte_offset. _ ==> _ /\ _` drule_all >> strip_tac >>
      `mem_bytes_at byte_offset (type_memory_size tv) t.vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by metis_tac[] >>
      simp[] >> irule val_in_memory_mem_agree >>
      conj_tac >- metis_tac[immutable_admissible_val_wf] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[]) >>
  fs[immutables_rel_def] >> metis_tac[]
QED

Theorem empty_scope_memory_frame:
  stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
  copy_static t = copy_static s /\
  (!off len. off + len <= b \/ b + sz <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b sz) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
    lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx (es with scopes := []) t
Proof
  rpt strip_tac >> drule copy_static_fields >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) t` by
    (irule immutables_rel_byte_agree >> qexists_tac `s` >>
     simp[] >> reverse conj_tac
     >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def]) >>
  rewrite_tac[stmt_state_rel_def] >> conj_tac
  >- (irule state_rel_frame >> conj_tac
      >- simp[local_ptrs_rel_def, local_region_def, lookup_scopes_def] >>
      qexistsl_tac [`es with scopes := []`, `s`] >>
      gvs[stmt_state_rel_def, state_rel_def, copy_static_def,
          venom_state_component_equality, local_ptrs_rel_def,
          local_region_def, lookup_scopes_def]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  conj_tac >- (irule fmp_room_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def] >>
               qpat_x_assum `copy_static t = copy_static s` mp_tac >>
               simp[copy_static_def, venom_state_component_equality]) >>
  conj_tac >- (irule immutable_alloca_sep_fields >>
               qexistsl_tac [`s`, `es with scopes := []`] >>
               gvs[stmt_state_rel_def, local_region_def, lookup_scopes_def]) >>
  conj_tac >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
      local_region_def, lookup_scopes_def] >> first_assum ACCEPT_TAC
QED

Theorem empty_scope_unlock_memory_frame:
  stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
  copy_static t = copy_static (return_unlock_state cenv s) /\
  (!off len. off + len <= b \/ b + sz <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b sz) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
    lookup_var x t = lookup_var x s) ==>
  ?pre. t = (return_unlock_state cenv pre with vs_inst_idx := t.vs_inst_idx) /\
    stmt_state_rel ctx func cenv cx (es with scopes := []) pre
Proof
  strip_tac >>
  qabbrev_tac `pre = t with
    <|vs_accounts := s.vs_accounts; vs_transient := s.vs_transient|>` >>
  `copy_static pre = copy_static s /\
   t = (return_unlock_state cenv pre with vs_inst_idx := t.vs_inst_idx)` by
    (qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     fs[copy_static_def, return_unlock_state_def, Abbr `pre`,
        tstore_def, sstore_def, venom_state_component_equality]) >>
  qexists_tac `pre` >> simp[] >>
  irule empty_scope_memory_frame >> qexistsl_tac [`b`, `s`, `sz`] >>
  fs[Abbr `pre`, lookup_var_def, arithmeticTheory.ADD_COMM] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
