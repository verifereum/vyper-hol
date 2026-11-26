(* Physical frame of the output allocation and non-allocating Slice writes. *)
Theory bodySliceWindowPhysicalMods
Ancestors
  bodyPtrBytestringBuiltinsCalldataFrame exprSimSliceData
  exprSimPtrLiteralBuffer revertReasonPrefixPtr moduleLoweringProps
  bodyMemoryDefs exprLoweringProps exprSimProps exprSimCalldataSlice
  loweringPosts venomMemProps ptrDiscipline venomState venomInst
  loweringStateRelDefs finite_map pred_set

Theorem slice_window_written_fields[local]:
  t = (mstore p (n2w (LENGTH bytes))
        (write_memory_with_expansion (p + 32) bytes u) with vs_inst_idx := j) ==>
  t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
  t.vs_data_section = u.vs_data_section /\
  (!x. lookup_var x t = lookup_var x u) /\
  t.vs_memory = (mstore p (n2w (LENGTH bytes))
      (write_memory_with_expansion (p + 32) bytes u)).vs_memory
Proof
  disch_then SUBST1_TAC >>
  simp_tac bool_ss [venom_state_accfupds, combinTheory.K_THM] >>
  simp_tac bool_ss [mstore_def, write_memory_with_expansion_def, LET_THM,
    lookup_var_def, venom_state_accfupds, combinTheory.K_THM]
QED

Theorem slice_window_written_memory[local]:
  u.vs_memory = s.vs_memory ==>
  (mstore p (n2w (LENGTH bytes))
      (write_memory_with_expansion (p + 32) bytes u)).vs_memory =
  (mstore p (n2w (LENGTH bytes))
      (write_memory_with_expansion (p + 32) bytes s)).vs_memory
Proof
  disch_tac >>
  asm_simp_tac bool_ss [mstore_def, write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, combinTheory.K_THM]
QED

Theorem slice_window_physical_frame_mods:
  stmt_state_rel H0 ctx func cenv cx es s /\
  (!H : (bool # 256 word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==>
       stmt_state_rel H ctx func cenv cx es v) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sd.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
  v.vs_memory = s.vs_memory /\ v.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= v.vs_alloca_next /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
           FLOOKUP v.vs_allocas aid = SOME e) /\
  (!aid b len. FLOOKUP v.vs_allocas aid = SOME (b,len) ==>
               FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\ FLOOKUP v.vs_allocas inst.inst_id = SOME (p,N) /\
  (!aid b len. aid < inst.inst_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
               regions_disjoint p N b len) /\
  (!name b len. local_region cenv es.scopes v name b len ==>
                regions_disjoint p N b len) /\
  32 + LENGTH bytes <= N /\
  za = update_var (STRING #"%" (toString sd.cs_next_var)) value v /\
  target = (mstore p (n2w (LENGTH bytes))
             (write_memory_with_expansion (p + 32) bytes za) with vs_inst_idx := j) /\
  (!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem) ==>
  (!H : (bool # 256 word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==>
       stmt_state_rel H ctx func cenv cx es target) /\
  wb_frame cenv es es sa s target /\ pure_frame cenv func es sa s target /\
  (!name b len. local_region cenv es.scopes target name b len ==>
                regions_disjoint p N b len) /\
  (!b len. regions_disjoint p N b len ==>
           mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b + len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
  target.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH target.vs_memory /\
  target.vs_allocas = v.vs_allocas /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
           FLOOKUP target.vs_allocas aid = SOME e) /\
  (!aid b len. FLOOKUP target.vs_allocas aid = SOME (b,len) ==>
               FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b) /\
  target.vs_alloca_next = v.vs_alloca_next /\ s.vs_alloca_next <= target.vs_alloca_next
Proof
  DISCH_THEN (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "landing") strip_assume_tac)) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sd.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  drule_then strip_assume_tac slice_window_written_fields >>
  `za.vs_allocas = v.vs_allocas /\ za.vs_alloca_next = v.vs_alloca_next /\
   za.vs_memory = s.vs_memory /\ za.vs_data_section = s.vs_data_section` by
    (qpat_assum `za = _` SUBST1_TAC >> simp[update_var_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x target = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. lookup_var x target = _` (qspec_then `x` SUBST1_TAC) >>
     irule EQ_TRANS >> qexists_tac `lookup_var x v` >> conj_tac
     >- (qpat_assum `za = _` SUBST1_TAC >>
         irule lookup_var_update_not_fresh >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _` irule >> simp[]) >>
  `!name b len. local_region cenv es.scopes v name b len <=>
                local_region cenv es.scopes s name b len` by
    (irule literal_ptr_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `!name b len. local_region cenv es.scopes za name b len <=>
                local_region cenv es.scopes v name b len` by
    (qpat_assum `za = _` SUBST1_TAC >> simp[local_region_update_nonlocal]) >>
  `!name b len. local_region cenv es.scopes target name b len <=>
                local_region cenv es.scopes s name b len` by
    (irule literal_ptr_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `target.vs_memory = (mstore p (n2w (LENGTH bytes))
       (write_memory_with_expansion (p + 32) bytes s)).vs_memory` by
    (qpat_assum `target.vs_memory = _` SUBST1_TAC >>
     irule slice_window_written_memory >> first_assum ACCEPT_TAC) >>
  `!b len. regions_disjoint p N b len ==>
           mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule bytes_buffer_write_frame >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
                regions_disjoint p N b len` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes v name b len ==> _` irule >>
     qexists_tac `name` >> simp[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
       mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b len. regions_disjoint p N b len ==> _` irule >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> regions_disjoint _ _ _ _` irule >>
     qexists_tac `name` >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sa s target` by suspend "wb_frame" >>
  `pure_frame cenv func es sa s target` by suspend "pure_frame" >>
  `!H : (bool # 256 word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s ==>
       stmt_state_rel H ctx func cenv cx es target` by suspend "state_rel" >>
  suspend "finish"
QED

Resume slice_window_physical_frame_mods[wb_frame]:
  rewrite_tac[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[])
  >- (rpt strip_tac >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `!b len. regions_disjoint p N b len ==> _` irule >>
      qpat_assum `!aid b len. _ /\ _ ==> regions_disjoint p N b len`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >> decide_tac)
  >> irule locals_kept_regions >> first_assum ACCEPT_TAC
QED

Resume slice_window_physical_frame_mods[pure_frame]:
  irule slice_allocated_bytes_pure_frame >> conj_tac
  >- (rpt strip_tac >> simp[]) >>
  qexistsl_tac [`bytes`,`inst`,`p`,`N`] >> simp[] >> first_assum ACCEPT_TAC
QED

Resume slice_window_physical_frame_mods[state_rel]:
  qx_gen_tac `hz` >> disch_tac >> qpat_assum `target = _` SUBST1_TAC >>
  pure_rewrite_tac[stmt_state_rel_inst_idx] >>
  irule allocated_bytes_write_state_rel >> simp[] >> conj_tac
  >- (qexistsl_tac [`N`,`inst`] >> simp[] >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `!name b len. local_region cenv es.scopes v name b len ==> _` irule >>
      qexists_tac `name` >> gvs[]) >>
  qpat_assum `za = _` SUBST1_TAC >>
  irule stmt_state_rel_update_var >> simp[] >>
  asm "landing" irule >> first_assum ACCEPT_TAC
QED

Resume slice_window_physical_frame_mods[finish]:
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> regions_disjoint _ _ _ _` irule >>
      qexists_tac `name` >> gvs[])
  >- (rpt gen_tac >> disch_tac >> conj_tac
      >- (qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> mem_bytes_at _ _ _ = _`
            (drule_then mp_tac) >> simp[]) >>
      rpt strip_tac >>
      `b + len <= s.vs_alloca_next` by
        (drule_all body_local_region_frontier >> simp[]) >>
      qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >> decide_tac)
  >> simp[LENGTH_write_memory_with_expansion,LENGTH_mstore_eq]
QED

Finalise slice_window_physical_frame_mods
