(* Select only the explicit argument buffers, not every staging instruction. *)
Theory bodyIntCallStagingAllocationSelection
Ancestors
  bodyIntCallCodeChargeBound exprLowering exprLoweringProps loweringHalt context emitHelper
  loweringShapeDefs compileEnv venomInst list words rich_list

Theorem staging_added_insts_trans:
  !a b c. cs_extends a b /\ cs_extends b c ==>
    added_insts a c = added_insts a b ++ added_insts b c
Proof
  rpt strip_tac >>
  qpat_assum `cs_extends b c`
    (assume_tac o MATCH_MP state_insts_cs_extends) >>
  qpat_assum `cs_extends a b`
    (assume_tac o MATCH_MP state_insts_cs_extends) >>
  once_rewrite_tac[added_insts_def] >>
  qpat_x_assum `state_insts c = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `state_insts b = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac std_ss [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem staging_buffer_selected_instruction:
  compile_alloc_buffer n sa = (buf,sb) /\ n < dimword (:256) ==>
  ?i. added_insts sa sb = [i] /\ i.inst_id = sa.cs_next_id /\
      sb.cs_next_id = sa.cs_next_id + 1 /\
      i.inst_opcode = ALLOCA /\ alloca_lit_size i = n
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  fs[added_insts_def, state_insts_def, all_blocks_def] >>
  simp_tac std_ss [DROP_APPEND2, DROP_LENGTH_APPEND] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       fresh_var_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, comp_get_def,
       fresh_id_def, emit_def, mk_inst_def, alloca_lit_size_def] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM LENGTH_APPEND, GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem staging_explicit_allocations:
  !vals flags tys ce sa ops sb.
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
    LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
    EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys ==>
    ?ais. LENGTH ais = LENGTH (FILTER (\b. ~b) flags) /\
      ALL_DISTINCT (MAP (\i. i.inst_id) ais) /\
      EVERY (\i. MEM i (added_insts sa sb) /\
        sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
        i.inst_opcode = ALLOCA /\ 32 <= alloca_lit_size i) ais
Proof
  Induct >- (Cases >> simp[compile_stage_intcall_args_def, comp_return_def]) >>
  rpt gen_tac >>
  Cases_on `flags` >- simp[] >> Cases_on `tys` >- simp[] >>
  rename1 `compile_stage_intcall_args ce (vv::vals) (flag::flags) (ty::tys)` >>
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac
  >- (gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
      rename1 `unwrap_value ce vv sa = (op,su)` >>
      `ci_mono sa su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
      rename1 `compile_stage_intcall_args ce vals flags tys su = (rest,last)` >>
      `ci_mono su last` by
        metis_tac[ci_mono_compile_stage_intcall_args, pairTheory.SND] >>
      fs[ci_mono_def] >>
      drule_all staging_added_insts_trans >> strip_tac >>
      qexists_tac `ais` >> fs[EVERY_MEM, MEM_APPEND] >>
      rpt strip_tac >> res_tac >> decide_tac) >>
  suspend "memory"
QED

Resume staging_explicit_allocations[memory]:
  gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
  rename1 `unwrap_value ce vv sa = (op,su)` >>
  rename1 `compile_alloc_buffer _ su = (buf,sm)` >>
  rename1 `compile_stage_intcall_args ce vals flags tys sn = (rest,last)` >>
  `ci_mono sa su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sn` by
    (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     rpt IF_CASES_TAC >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     metis_tac[ci_mono_emit_void, ci_mono_compile_store_bytestring,
               ci_mono_compile_store_memory, pairTheory.SND]) >>
  `ci_mono sn last` by
    metis_tac[ci_mono_compile_stage_intcall_args, pairTheory.SND] >>
  `MAX 32 (type_memory_bytes ce ty) < dimword (:256)` by simp[] >>
  drule_all staging_buffer_selected_instruction >> strip_tac >>
  fs[ci_mono_def] >>
  `added_insts sa last = added_insts sa su ++ added_insts su sm ++
      added_insts sm sn ++ added_insts sn last` by
    metis_tac[staging_added_insts_trans, cs_extends_trans, APPEND_ASSOC] >>
  qexists_tac `i::ais` >>
  fs[EVERY_MEM, ALL_DISTINCT, MEM_MAP, MEM_APPEND] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac
QED

Finalise staging_explicit_allocations
