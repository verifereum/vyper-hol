(* TOP-LEVEL: allocation growth transports the backing of live locals
   independently of writes to RAM. A nonlocal allocation instruction's
   recorded region remains disjoint from those original live locals.
   Helpers bound static MemLocs below fresh and cached profile slots. *)
Theory sourceAllocationPrivacy
Ancestors
  sourceMemoryFrames sourceAbiFrames sourceBufferFrames allocationGrowth localPtrsProps nameLoweringProps
  abiAllocationWindows abiAllocatedWindows abiAllocationFrame memoryValueSnapshot
  compileEnv venomState venomMemDefs finite_map list pair words arithmetic

Theorem local_ptrs_rel_growing_alloca_disjoint:
  !func cenv scopes before after inst q region_base capacity name local_base local_size.
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    FLOOKUP after.vs_allocas inst.inst_id = SOME (region_base,capacity) /\
    local_region cenv scopes before name local_base local_size ==>
    regions_disjoint region_base capacity local_base local_size
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `backing = before with <|vs_allocas := after.vs_allocas; vs_alloca_next := after.vs_alloca_next|>` >>
  `allocation_growth before backing` by
    (qpat_x_assum `allocation_growth before after` mp_tac >> simp[Abbr`backing`, allocation_growth_def] >>
     strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `local_ptrs_rel func cenv scopes backing` by
    (irule local_ptrs_rel_memory_frame >> qexists_tac `before` >> simp[Abbr`backing`, lookup_var_def]) >>
  `alloca_inv backing` by
    (fs[Abbr`backing`, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `local_region cenv scopes backing name local_base local_size` by
    fs[Abbr`backing`, local_region_def, lookup_var_def] >>
  qspecl_then [`func`, `cenv`, `scopes`, `backing`, `inst`, `q`, `region_base`, `capacity`, `name`, `local_base`, `local_size`]
    mp_tac local_ptrs_rel_alloca_disjoint >> simp[Abbr`backing`]
QED

Definition source_alloca_floor_def:
  source_alloca_floor cenv scopes ids ss <=>
    !name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= ss.vs_alloca_next /\
      (!id region_base capacity. MEM id ids /\ FLOOKUP ss.vs_allocas id = SOME (region_base,capacity) ==>
        offset + type_memory_size entry.type <= region_base)
End

Theorem source_alloca_floor_growing_record:
  !cenv scopes ids before after id region_base capacity name entry offset region_size.
    source_alloca_floor cenv scopes ids before /\ allocation_growth before after /\
    MEM id ids /\ FLOOKUP after.vs_allocas id = SOME (region_base,capacity) /\
    lookup_scopes name scopes = SOME entry /\ FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
    offset + type_memory_size entry.type <= region_base
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_alloca_floor _ _ _ _` (mp_tac o REWRITE_RULE [source_alloca_floor_def]) >>
  disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> Cases_on `FLOOKUP before.vs_allocas id`
  >- (drule_all allocation_growth_new >> decide_tac) >>
  rename1 `FLOOKUP before.vs_allocas id = SOME old_region` >>
  `FLOOKUP after.vs_allocas id = SOME old_region` by (drule_all allocation_growth_old >> simp[]) >>
  `old_region = (region_base,capacity)` by fs[] >> gvs[] >> first_x_assum irule >>
  qexistsl_tac [`capacity`, `id`] >> simp[]
QED

Theorem source_alloca_floor_subprofile:
  !cenv scopes small large ss.
    source_alloca_floor cenv scopes large ss /\ (!id. MEM id small ==> MEM id large) ==>
    source_alloca_floor cenv scopes small ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_alloca_floor_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  qpat_x_assum `source_alloca_floor _ _ _ _` (mp_tac o REWRITE_RULE [source_alloca_floor_def]) >>
  disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  MAP_EVERY qx_gen_tac [`id`, `region_base`, `capacity`] >> strip_tac >>
  `MEM id large` by (qpat_x_assum `!id. MEM id small ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!id region_base capacity. _` (qspecl_then [`id`, `region_base`, `capacity`] mp_tac) >> simp[]
QED

Theorem source_alloca_floor_growth:
  !cenv scopes ids before after.
    source_alloca_floor cenv scopes ids before /\ allocation_growth before after ==>
    source_alloca_floor cenv scopes ids after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_alloca_floor_def] >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  `offset + type_memory_size entry.type <= before.vs_alloca_next` by
    (qpat_x_assum `source_alloca_floor _ _ _ _` (mp_tac o REWRITE_RULE [source_alloca_floor_def]) >>
     disch_then (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
     impl_tac >- simp[] >> strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (qspecl_then [`before`, `after`] mp_tac allocation_growth_next >> impl_tac >- simp[] >> decide_tac) >>
  MAP_EVERY qx_gen_tac [`id`, `region_base`, `capacity`] >> strip_tac >>
  qspecl_then [`cenv`, `scopes`, `ids`, `before`, `after`, `id`, `region_base`, `capacity`,
    `name`, `entry`, `offset`, `region_size`] mp_tac source_alloca_floor_growing_record >> simp[]
QED

Theorem source_alloca_floor_snapshot:
  !cenv scopes ids ss id.
    source_alloca_floor cenv scopes ids ss /\ MEM id ids /\ alloca_inv ss /\ ss.vs_alloca_next < dimword(:256) ==>
    !name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr id ss)
Proof
  rpt gen_tac >> strip_tac >> MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
  qspecl_then [`id`, `0`, `ss`] mp_tac abi_allocation_frame_record >>
  impl_tac >- simp[abi_alloca_request_ok_def] >>
  disch_then (qx_choose_then `snapshot_base` (qx_choose_then `snapshot_capacity` strip_assume_tac)) >>
  `allocation_growth ss (memory_snapshot_alloc_frame id 0 ss)` by
    MATCH_ACCEPT_TAC (Q.SPECL [`id`, `0`, `ss`] allocation_growth_snapshot) >>
  qspecl_then [`cenv`, `scopes`, `ids`, `ss`, `memory_snapshot_alloc_frame id 0 ss`, `id`, `snapshot_base`, `snapshot_capacity`,
    `name`, `entry`, `offset`, `region_size`] mp_tac source_alloca_floor_growing_record >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> asm_simp_tac bool_ss []
QED

Theorem compile_buffer_payload_private:
  !func cenv scopes ss capacity cs buf cut byte_count ids.
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_has_code cs cut func /\
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    ss.vs_alloca_next < dimword(:256) /\ source_alloca_floor cenv scopes ids ss /\
    MEM cs.cs_next_id ids /\ byte_count <= capacity /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    abi_alloca_request_ok cs.cs_next_id capacity ss ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cenv`, `scopes`, `ids`, `ss`, `cs.cs_next_id`] mp_tac source_alloca_floor_snapshot >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`func`, `cenv`, `scopes`, `ss`, `capacity`, `cs`, `buf`, `cut`] mp_tac compile_buffer_source_separated >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`cenv`, `scopes`, `ss`, `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `capacity`,
    `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `byte_count`] mp_tac source_memory_separated_subrange >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED

Theorem source_growing_allocation_private:
  !func cenv scopes before after inst q region_base capacity.
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    FLOOKUP after.vs_allocas inst.inst_id = SOME (region_base,capacity) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= region_base) ==>
    source_memory_separated cenv scopes before region_base capacity
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [source_memory_separated_def] >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`name`, `entry`, `offset`, `region_size`] >> strip_tac >>
      qpat_x_assum `!name entry offset region_size. _`
        (qspecl_then [`name`, `entry`, `offset`, `region_size`] mp_tac) >>
      impl_tac >- simp[] >> simp[compileEnvTheory.regions_disjoint_def]) >>
  MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`, `ptr_addr`] >> strip_tac >>
  `local_region cenv scopes before name (w2n ptr_addr) region_size` by
    (simp_tac bool_ss [local_region_def] >> qexistsl_tac [`entry`, `p`, `ptr_addr`] >> simp[]) >>
  qspecl_then [`func`, `cenv`, `scopes`, `before`, `after`, `inst`, `q`, `region_base`, `capacity`,
    `name`, `w2n ptr_addr`, `region_size`] mp_tac local_ptrs_rel_growing_alloca_disjoint >>
  impl_tac >- simp[] >> DISCH_TAC >> drule_all local_ptrs_rel_value >> strip_tac >>
  gvs[eval_operand_def, compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem source_owned_allocation_private:
  !func cenv scopes ids before after inst q offset byte_count.
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    MEM inst.inst_id ids /\ source_alloca_floor cenv scopes ids before /\
    abi_allocated_window after inst.inst_id offset byte_count ==>
    source_memory_separated cenv scopes before offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_allocated_window _ _ _ _` (mp_tac o REWRITE_RULE [abi_allocated_window_def]) >>
  disch_then (qx_choose_then `region_base` (qx_choose_then `capacity` strip_assume_tac)) >>
  `!name entry static_offset region_size. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc static_offset region_size) ==>
    static_offset + type_memory_size entry.type <= region_base` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`, `scopes`, `ids`, `before`, `after`, `inst.inst_id`, `region_base`, `capacity`,
       `name`, `entry`, `static_offset`, `region_size`] mp_tac source_alloca_floor_growing_record >> simp[]) >>
  drule_all source_growing_allocation_private >> DISCH_TAC >>
  qspecl_then [`cenv`, `scopes`, `before`, `region_base`, `capacity`, `offset`, `byte_count`]
    mp_tac source_memory_separated_subrange >> simp[]
QED

Theorem source_profile_writes_private:
  !func cenv scopes ids before after.
    allocation_growth before after /\ alloca_inv after /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes before /\ source_alloca_floor cenv scopes ids before /\
    (!id. MEM id ids ==> ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q) ==>
    source_writes_separated cenv scopes before (abi_allocation_windows ids after)
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [source_writes_separated_def, EVERY_MEM, FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`offset`, `byte_count`] >> DISCH_TAC >> disj2_tac >>
  drule abi_allocation_windows_owned >> disch_then (qx_choose_then `id` strip_assume_tac) >>
  qpat_x_assum `!id. MEM id ids ==> _` (qspec_then `id` mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `inst` (qx_choose_then `q` strip_assume_tac)) >>
  qspecl_then [`func`, `cenv`, `scopes`, `ids`, `before`, `after`, `inst`, `q`, `offset`, `byte_count`]
    mp_tac source_owned_allocation_private >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed growing source allocation privacy: " ^ name)
  end) (DB.thms "sourceAllocationPrivacy")
