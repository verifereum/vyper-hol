(* TOP-LEVEL: actual buffer allocation preserves source/local relations and
   produces a private write region. Cached slots use their real instruction
   identity; fresh slots use the old frontier. Helpers shrink write windows. *)
Theory sourceBufferFrames
Ancestors
  sourceMemorySeparation sourceMemoryFrames sourceValueFrames sourceAbiFrames materializeSeparation
  allocationPathGrowth allocationGrowth abiBufferAllocationCode abiBufferAllocationPath
  abiAllocationFrame abiAllocatedWindows abiStateFrame abiFieldOperands abiStaticLoopCode
  memoryValueSnapshot context compileEnv valueEncoding fragExec fragBlockPath
  venomExecProps venomMemDefs venomState venomInst list words arithmetic

Theorem source_memory_separated_allocation:
  !func cenv scopes ss inst q capacity.
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    abi_alloca_request_ok inst.inst_id capacity ss /\ ss.vs_alloca_next < dimword(:256) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr inst.inst_id ss)) ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr inst.inst_id ss)) capacity
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ss.vs_allocas inst.inst_id`
  >- (`w2n (memory_snapshot_addr inst.inst_id ss) = ss.vs_alloca_next` by
        (asm_simp_tac (srw_ss()) [memory_snapshot_addr_def, w2n_n2w] >>
         irule LESS_MOD >> first_assum MATCH_ACCEPT_TAC) >>
      `!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
        offset + type_memory_size entry.type <= ss.vs_alloca_next` by
        (qpat_x_assum `!name entry offset region_size. _ ==> offset + _ <= _` mp_tac >>
         asm_simp_tac bool_ss []) >>
      mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`, `inst.inst_id`, `capacity`]
        source_memory_separated_fresh_snapshot) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  rename1 `FLOOKUP ss.vs_allocas inst.inst_id = SOME allocation` >> Cases_on `allocation` >>
  rename1 `FLOOKUP ss.vs_allocas inst.inst_id = SOME (region_base,recorded_size)` >>
  `region_base + recorded_size <= ss.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `region_base < dimword(:256)` by decide_tac >>
  `w2n (memory_snapshot_addr inst.inst_id ss) = region_base` by
    (asm_simp_tac (srw_ss()) [memory_snapshot_addr_def, w2n_n2w] >>
     irule LESS_MOD >> first_assum MATCH_ACCEPT_TAC) >>
  `!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
    offset + type_memory_size entry.type <= region_base` by
    (qpat_x_assum `!name entry offset region_size. _ ==> offset + _ <= _` mp_tac >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`, `inst`, `q`, `region_base`, `recorded_size`, `capacity`]
    source_memory_separated_cached_snapshot) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem compile_buffer_allocation_member:
  !capacity cs buf cut func.
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_has_code cs cut func ==>
    MEM (mk_inst cs.cs_next_id ALLOCA [Lit (n2w capacity)] [compiler_var_name cs.cs_next_var 0]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  irule fn_has_code_current_instruction >> qexistsl_tac [`cs`, `cut`] >> simp[compiler_var_name_def]
QED

Theorem compile_buffer_source_separated:
  !func cenv scopes ss capacity cs buf cut.
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_has_code cs cut func /\
    abi_alloca_request_ok cs.cs_next_id capacity ss /\ ss.vs_alloca_next < dimword(:256) /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)) ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity
Proof
  rpt gen_tac >> strip_tac >>
  `not_local_ptr cenv scopes (compiler_var_name cs.cs_next_var 0)` by
    (irule source_pointer_operands_not_local >> qexists_tac `cs.cs_next_var` >>
     rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  drule_all compile_buffer_allocation_member >> DISCH_TAC >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`,
    `mk_inst cs.cs_next_id ALLOCA [Lit (n2w capacity)] [compiler_var_name cs.cs_next_var 0]`,
    `compiler_var_name cs.cs_next_var 0`, `capacity`] source_memory_separated_allocation) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    simp[mk_inst_def] >> first_assum MATCH_ACCEPT_TAC]) >> simp[mk_inst_def]
QED

Theorem source_memory_separated_subrange:
  !cenv scopes before outer_base outer_count inner_base inner_count.
    source_memory_separated cenv scopes before outer_base outer_count /\
    outer_base <= inner_base /\ inner_base + inner_count <= outer_base + outer_count ==>
    source_memory_separated cenv scopes before inner_base inner_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_memory_separated _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_memory_separated_def]) >>
  simp_tac bool_ss [source_memory_separated_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
      qpat_x_assum `!name entry offset region_size. _`
        (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
      impl_tac >- simp[] >> simp_tac bool_ss [compileEnvTheory.regions_disjoint_def] >> strip_tac >> decide_tac) >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  qpat_x_assum `!name entry p region_size ptr_addr. _`
    (qspecl_then [`name`, `entry`, `p`, `region_size`, `ptr_addr`] mp_tac) >>
  impl_tac >- simp[] >> simp_tac bool_ss [compileEnvTheory.regions_disjoint_def] >> strip_tac >> decide_tac
QED

Theorem source_writes_separated_prefix:
  !cenv scopes before region_base capacity byte_count.
    source_memory_separated cenv scopes before region_base capacity /\ byte_count <= capacity ==>
    source_writes_separated cenv scopes before [(region_base,byte_count)]
Proof
  rpt gen_tac >> strip_tac >> simp[source_writes_separated_def] >> disj2_tac >>
  mp_tac (Q.SPECL [`cenv`, `scopes`, `before`, `region_base`, `capacity`, `region_base`, `byte_count`]
    source_memory_separated_subrange) >> simp[]
QED

Theorem compile_buffer_source_state:
  !ctx func cenv cx es ss capacity cs buf cut.
    state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\ alloca_inv ss /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_has_code cs cut func /\
    abi_alloca_request_ok cs.cs_next_id capacity ss /\ ss.vs_alloca_next + capacity < dimword(:256) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (!name entry offset region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cut.cs_current_bb /\ out.vs_inst_idx = LENGTH cut.cs_current_insts /\ ~out.vs_halted /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_operand_before cut.cs_next_var buf.buf_operand /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity /\
      alloca_inv out /\ out.vs_memory = ss.vs_memory /\ abi_state_frame ss out /\ allocation_growth ss out /\
      source_memory_separated cenv es.scopes out (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity /\
      cs.cs_next_var <= cut.cs_next_var /\
      (!arg. abi_operand_before cs.cs_next_var arg ==> eval_operand arg out = eval_operand arg ss) /\
      (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cut.cs_next_var (Var p))
Proof
  rpt gen_tac >> strip_tac >> `ss.vs_alloca_next < dimword(:256)` by decide_tac >>
  drule compile_alloc_buffer_code >> strip_tac >> `cs.cs_next_var <= cut.cs_next_var` by simp[] >>
  drule_all compile_buffer_source_separated >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `capacity`, `cs`, `buf`, `cut`, `ss`] compile_alloc_buffer_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all fragment_path_allocation_growth >> DISCH_TAC >>
  mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `ss`, `out`, `cs.cs_next_var`] source_relations_memory_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cenv`, `es.scopes`, `ss`, `out`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `ss`, `out`, `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `capacity`]
    source_memory_separated_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `cs.cs_next_var`, `cut.cs_next_var`] source_pointer_lifetimes_mono) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `!name entry p region_size. _ ==> abi_operand_before cut.cs_next_var (Var p)` mp_tac >>
  asm_simp_tac bool_ss []
QED
