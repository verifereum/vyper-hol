(* TOP-LEVEL: fresh and cached allocations miss live source memory.
   Pointer-backed locals use their frontier bound or allocation ownership;
   fixed memory locations use the compiler's static-memory bound. *)
Theory sourceMemorySeparation
Ancestors
  loweringStateRelDefs sourceMemoryFrames nameLoweringProps localPtrsProps memoryValueSnapshot
  abiFieldOperands abiStaticLoopCode abiAllocationFrame
  compileEnv valueEncoding venomMemDefs venomState venomInst finite_map words arithmetic

Theorem source_pointer_operands_not_local:
  !cenv scopes var_base next_var.
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before var_base (Var p)) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> abi_operand_before var_base (Var x)) /\
    var_base <= next_var ==>
    not_local_ptr cenv scopes (compiler_var_name next_var 0)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [not_local_ptr_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `region_size`] >> DISCH_TAC >> strip_tac >>
      qpat_x_assum `!name entry p region_size. _`
        (qspecl_then [`name`, `entry`, `compiler_var_name next_var 0`, `region_size`] mp_tac) >>
      simp[] >> simp_tac bool_ss [abi_operand_before_def] >>
      qexists_tac `next_var` >> simp[]) >>
  strip_tac >>
  qpat_x_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _`
    (qspec_then `compiler_var_name next_var 0` mp_tac) >>
  simp[] >> simp_tac bool_ss [abi_operand_before_def] >>
  qexists_tac `next_var` >> simp[]
QED

Theorem source_pointer_cached_allocation_disjoint:
  !func cenv scopes ss inst q region_base recorded_size byte_count name entry p region_size ptr_addr.
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (region_base,recorded_size) /\ byte_count <= recorded_size /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\ lookup_var p ss = SOME ptr_addr ==>
    loweringStateRelDefs$regions_disjoint (w2n ptr_addr) (type_memory_size entry.type) region_base byte_count
Proof
  rpt gen_tac >> strip_tac >>
  `local_region cenv scopes ss name (w2n ptr_addr) region_size` by
    (simp_tac bool_ss [local_region_def] >> qexistsl_tac [`entry`, `p`, `ptr_addr`] >> simp[]) >>
  drule_all local_ptrs_rel_alloca_disjoint >> DISCH_TAC >>
  drule_all local_ptrs_rel_value >> strip_tac >>
  gvs[eval_operand_def, loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem source_pointer_below_frontier:
  !func cenv scopes ss name entry p region_size ptr_addr.
    local_ptrs_rel func cenv scopes ss /\ lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) /\ lookup_var p ss = SOME ptr_addr ==>
    w2n ptr_addr + type_memory_size entry.type <= ss.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> drule_all local_ptrs_rel_value >> strip_tac >>
  gvs[eval_operand_def] >> decide_tac
QED

Theorem source_memory_separated_above_frontier:
  !func cenv scopes ss dst byte_count.
    local_ptrs_rel func cenv scopes ss /\ ss.vs_alloca_next <= dst /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= ss.vs_alloca_next) ==>
    source_memory_separated cenv scopes ss dst byte_count
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_memory_separated_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
      qpat_x_assum `!name entry offset region_size. _`
        (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
      impl_tac >- simp[] >> simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  drule_all source_pointer_below_frontier >> DISCH_TAC >>
  simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem source_memory_separated_fresh_snapshot:
  !func cenv scopes ss id byte_count.
    local_ptrs_rel func cenv scopes ss /\ FLOOKUP ss.vs_allocas id = NONE /\
    ss.vs_alloca_next < dimword(:256) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= ss.vs_alloca_next) ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`, `ss.vs_alloca_next`, `byte_count`]
    source_memory_separated_above_frontier) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  simp[memory_snapshot_addr_def]
QED

Theorem source_memory_separated_cached_snapshot:
  !func cenv scopes ss inst q region_base recorded_size byte_count.
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (region_base,recorded_size) /\
    abi_alloca_request_ok inst.inst_id byte_count ss /\ ss.vs_alloca_next < dimword(:256) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= region_base) ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr inst.inst_id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >>
  `region_base + recorded_size <= ss.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `region_base < dimword(:256)` by decide_tac >>
  `byte_count <= recorded_size` by (fs[abi_alloca_request_ok_def] >> first_x_assum drule >> simp[]) >>
  simp[memory_snapshot_addr_def, source_memory_separated_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
      qpat_x_assum `!name entry offset region_size. _`
        (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
      impl_tac >- simp[] >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  drule_all source_pointer_cached_allocation_disjoint >> simp[]
QED
