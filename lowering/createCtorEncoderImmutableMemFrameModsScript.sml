Theory createCtorEncoderImmutableMemFrameMods
Ancestors
  bodyInvSplit bodyInvCodeProps bodyFullShadowBodyInv exprBodyPreProps
  immutableRegionTypingProps immutableRegionDeadProps ctorDeployDeadSectionRel abiCanonicalHeadSize
  valueEncodingProps valueEncodingProofs loweringSlice vyperTypeInvariants
  loweringStateRelDefs stateRelProj vyperContext bodyPtrDefs finite_map

(* Export the immutable-region frame argument for the linked encoder. *)
Theorem immutable_region_mem_frame_linked_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  immutable_region_mods mods src id off (type_memory_size rt) /\
  off + type_memory_size rt <= lo /\
  well_formed_type_value rt /\ immutable_value_admissible rt v /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  val_in_memory rt v off s.vs_memory /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem
Proof
  strip_tac >>
  `val_wf rt v` by metis_tac[immutable_admissible_val_wf] >>
  `!m. mem_bytes_at off (type_memory_size rt) (mem_bytes_at 0 lo m) =
       mem_bytes_at off (type_memory_size rt) m` by
    simp[valueEncodingDefsTheory.mem_bytes_at_bounded,
         abiCanonicalHeadSizeTheory.mem_bytes_at_window] >>
  `val_in_memory rt v off (mem_bytes_at 0 lo s.vs_memory)` by
    (irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `s.vs_memory`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `val_in_memory rt v off (mem_bytes_at 0 lo mem)` suffices_by
    (strip_tac >> irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size rt`, `mem_bytes_at 0 lo mem`] >> simp[]) >>
  irule section_value_memory_frame >> simp[] >>
  qexists_tac `mem_bytes_at 0 lo s.vs_memory` >> simp[] >>
  rpt strip_tac >>
  `j < lo` by decide_tac >>
  Cases_on `j IN tn.t_mem`
  >- (CCONTR_TAC >>
      `imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j` by
        fs[ghost_inv_at_mods_def] >>
      drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
      rename1 `immutable_region_mods mods src' name' off' (type_memory_size tv)` >>
      drule (cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >> strip_tac >>
      drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
        contract_inv_immutable_section_layout >>
      Cases_on `(src',name') = (src,id)`
      >- (gvs[] >>
          `FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
           FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off')` by metis_tac[] >>
          `off' = off` by metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
          gvs[]) >>
      `regions_disjoint off (type_memory_size rt) off' (type_memory_size tv)` by metis_tac[] >>
      fs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at j 1 s.vs_memory = mem_bytes_at j 1 mem` by fs[mem_agree_outside_def] >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED
