(* Untyped writes within a recorded allocation preserve the executable state. *)
Theory abiMalformedCopyState
Ancestors
  exprLoweringProps localPtrsProps loweringSlice typedMemoryCopy valueCopy
  compileEnv loweringStateRelDefs venomExecSemantics venomState venomMemDefs immutableMemoryFrame
  finite_map list arithmetic

Theorem abi_malformed_mcopy_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= dst /\ dst + n <= b + sz /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) ==>
  stmt_state_rel ctx func cenv cx es (mcopy dst src n s)
Proof
  strip_tac >>
  `(mcopy dst src n s).vs_vars = s.vs_vars /\
   (mcopy dst src n s).vs_allocas = s.vs_allocas /\
   (mcopy dst src n s).vs_alloca_next = s.vs_alloca_next` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func cenv es.scopes (mcopy dst src n s)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     simp[lookup_var_def] >>
     rpt strip_tac >> gvs[] >> sym_tac >> irule mem_bytes_at_mcopy_disjoint >>
     qpat_x_assum `!name lb lsz. _ ==> _` drule >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mcopy dst src n s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- (simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF] >>
         IF_CASES_TAC >> simp[]) >>
     conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     fs[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
     irule mem_bytes_at_mcopy_disjoint >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule stmt_state_rel_allocas_frame >> conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
      gvs[stmt_state_rel_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[] >> reverse conj_tac >- gvs[stmt_state_rel_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      gvs[local_region_def, lookup_var_def]) >>
  reverse conj_tac
  >- (qexistsl_tac [`es`, `s`] >>
      simp[mcopy_def, write_memory_with_expansion_def]) >>
  irule state_rel_frame >> conj_tac
  >- gvs[stmt_state_rel_def] >>
  qexistsl_tac [`es`, `s`] >> simp[] >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  gvs[stmt_state_rel_def]
QED
