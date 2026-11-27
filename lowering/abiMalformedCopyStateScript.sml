(* Untyped writes within a recorded allocation preserve the executable state. *)
Theory abiMalformedCopyState
Ancestors
  exprLoweringProps localPtrsProps loweringSlice typedMemoryCopy valueCopy
  compileEnv loweringStateRelDefs venomExecSemantics venomState venomMemDefs immutableMemoryFrame
  finite_map list arithmetic stateRelProj

Theorem abi_malformed_mcopy_state_rel:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= dst /\ dst + n <= b + sz /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) ==>
  stmt_state_rel H ctx func cenv cx es (mcopy dst src n s)
Proof
  strip_tac >>
  drule_then assume_tac stmt_state_rel_state_rel >>
  drule_then assume_tac state_rel_local_ptrs_rel >>
  `(mcopy dst src n s).vs_vars = s.vs_vars /\
   (mcopy dst src n s).vs_allocas = s.vs_allocas /\
   (mcopy dst src n s).vs_alloca_next = s.vs_alloca_next` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  `(mcopy dst src n s).vs_initial_fmp = s.vs_initial_fmp /\
   LENGTH s.vs_memory <= LENGTH (mcopy dst src n s).vs_memory` by
    (conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     simp[mcopy_def, venomMemPropsTheory.write_memory_with_expansion_nondecreasing]) >>
  `!a len. a + len <= b \/ b + sz <= a ==>
       mem_bytes_at a len (mcopy dst src n s).vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  `local_ptrs_rel func cenv es.scopes (mcopy dst src n s)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     simp[lookup_var_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!md. md = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules md) ==>
       immutable_alloca_sep func (cenv with ce_module := md) cx es s` by
    (rpt gen_tac >> strip_tac >> gvs[stmt_state_rel_def, optionTheory.IS_SOME_EXISTS]) >>
  `!md. md = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules md) ==>
       immutable_alloca_sep func (cenv with ce_module := md) cx es (mcopy dst src n s)` by
    (rpt strip_tac >> irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> rpt strip_tac >> qexists_tac `id` >> gvs[local_region_def, lookup_var_def]) >>
  `!md. md = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules md) ==>
       immutables_rel cenv cx.txn.target md cenv.ce_is_ctor es (mcopy dst src n s)` by
    (rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     simp[] >> reverse conj_tac
     >- gvs[state_rel_def, optionTheory.IS_SOME_EXISTS] >>
     rpt strip_tac >>
     `immutable_alloca_sep func (cenv with ce_module := md) cx es s` by
       (qpat_assum `!m. _ ==> immutable_alloca_sep _ _ _ _ s`
          (qspec_then `md` mp_tac) >> simp[]) >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
       (mp_tac o REWRITE_RULE [immutable_alloca_sep_def]) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `immutable_base_zero cenv (mcopy dst src n s)` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
     drule_then ACCEPT_TAC stmt_state_rel_immutable_base_zero) >>
  `state_rel H func cenv cx es (mcopy dst src n s)` by
    (irule state_rel_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`es`, `s`] >> simp[] >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  reverse (rpt conj_tac)
  >- (qexistsl_tac [`es`, `s`] >> simp[mcopy_def, write_memory_with_expansion_def])
  >- (`(cenv with ce_module := cenv.ce_module) = cenv` by
        simp[compile_env_component_equality] >>
      qpat_x_assum `!md. _ ==> immutable_alloca_sep _ _ _ _ (mcopy _ _ _ _)`
        (qspec_then `cenv.ce_module` mp_tac) >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!md. _ ==> immutable_alloca_sep _ _ _ _ (mcopy _ _ _ _)` irule >> simp[]
QED
