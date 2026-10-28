(* TOP-LEVEL: allocation growth retains existing records, places new records
   above the old frontier and never moves that frontier backwards. This is
   the allocator frame required to preserve live local backing. *)
Theory allocationGrowth
Ancestors
  memoryValueSnapshot abiAllocationFrame typedCopyStateFrame
  compileEnv venomState finite_map pair arithmetic

Definition allocation_growth_def:
  allocation_growth before after <=>
    (!id allocation. FLOOKUP before.vs_allocas id = SOME allocation ==>
      FLOOKUP after.vs_allocas id = SOME allocation) /\
    (!id region_base region_size. FLOOKUP after.vs_allocas id = SOME (region_base,region_size) /\
      FLOOKUP before.vs_allocas id = NONE ==> before.vs_alloca_next <= region_base) /\
    before.vs_alloca_next <= after.vs_alloca_next
End

Theorem allocation_growth_refl[simp]:
  !ss. allocation_growth ss ss
Proof
  simp[allocation_growth_def] >> rpt strip_tac >> gvs[]
QED

Theorem allocation_growth_old:
  !before after id allocation.
    allocation_growth before after /\ FLOOKUP before.vs_allocas id = SOME allocation ==>
    FLOOKUP after.vs_allocas id = SOME allocation
Proof
  simp[allocation_growth_def] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem allocation_growth_new:
  !before after id region_base region_size.
    allocation_growth before after /\ FLOOKUP after.vs_allocas id = SOME (region_base,region_size) /\
    FLOOKUP before.vs_allocas id = NONE ==> before.vs_alloca_next <= region_base
Proof
  simp[allocation_growth_def] >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem allocation_growth_next:
  !before after. allocation_growth before after ==> before.vs_alloca_next <= after.vs_alloca_next
Proof
  simp[allocation_growth_def]
QED

Theorem allocation_growth_copy_frame:
  !before after. copy_state_frame before after ==> allocation_growth before after
Proof
  rpt gen_tac >> strip_tac >> drule copy_state_frame_allocator >> strip_tac >>
  simp[allocation_growth_def] >> rpt strip_tac >> gvs[]
QED

Theorem allocation_growth_snapshot:
  !id capacity ss. allocation_growth ss (memory_snapshot_alloc_frame id capacity ss)
Proof
  rpt gen_tac >> simp_tac bool_ss [allocation_growth_def] >> rpt conj_tac
  >- (MAP_EVERY qx_gen_tac [`other`, `allocation`] >> DISCH_TAC >> Cases_on `allocation` >>
      drule_all abi_allocation_frame_lookup_old >> simp[])
  >- (rpt gen_tac >> rw[memory_snapshot_alloc_frame_def, FLOOKUP_UPDATE] >> gvs[FLOOKUP_UPDATE]) >>
  MATCH_ACCEPT_TAC (CONJUNCT1 (Q.SPECL [`id`, `capacity`, `ss`] abi_allocation_frame_next))
QED

Theorem allocation_growth_snapshot_fields:
  !before after id capacity.
    after.vs_allocas = (memory_snapshot_alloc_frame id capacity before).vs_allocas /\
    after.vs_alloca_next = (memory_snapshot_alloc_frame id capacity before).vs_alloca_next ==>
    allocation_growth before after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `capacity`, `before`] allocation_growth_snapshot) >>
  asm_simp_tac bool_ss [allocation_growth_def] >> strip_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem allocation_growth_trans:
  !before middle after.
    allocation_growth before middle /\ allocation_growth middle after ==> allocation_growth before after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [allocation_growth_def] >> rpt conj_tac
  >- (rpt gen_tac >> DISCH_TAC >> irule allocation_growth_old >> qexists_tac `middle` >> simp[] >>
      irule allocation_growth_old >> qexists_tac `before` >> simp[])
  >- (MAP_EVERY qx_gen_tac [`id`, `region_base`, `region_size`] >> strip_tac >>
      Cases_on `FLOOKUP middle.vs_allocas id`
      >- (drule_all allocation_growth_new >> DISCH_TAC >>
          mp_tac (Q.SPECL [`before`, `middle`] allocation_growth_next) >> impl_tac >- simp[] >> decide_tac) >>
      rename1 `FLOOKUP middle.vs_allocas id = SOME allocation` >>
      `FLOOKUP after.vs_allocas id = SOME allocation` by (drule_all allocation_growth_old >> simp[]) >>
      `allocation = (region_base,region_size)` by fs[] >> gvs[] >>
      drule_all allocation_growth_new >> simp[]) >>
  mp_tac (Q.SPECL [`before`, `middle`] allocation_growth_next) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`middle`, `after`] allocation_growth_next) >> impl_tac >- simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed snapshot allocation growth: " ^ name)
  end) (DB.thms "allocationGrowth")
