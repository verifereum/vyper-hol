Theory concretizeAnalysisCollection
Ancestors venomWfProps concretizeMemLocDefs staticLayoutAllocatorProofs venomWf
  o1PassContract concretizeAnalysisOwnership removeUnusedSsaProofs venomInst list combin

Theorem collect_static_allocas_total:
  !insts. EVERY inst_wf insts /\ ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
  ?items. collect_static_allocas insts = SOME items
Proof
  Induct >> simp[collect_static_allocas_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `h.inst_opcode = ALLOCA` >> simp[collect_static_allocas_def] >>
  `?sz out. h.inst_operands = [Lit sz] /\ h.inst_outputs = [out]` by
    (gvs[inst_wf_def] >> Cases_on `h.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  simp[exact_static_alloca_def, exact_static_alloca_size_def] >>
  `~MEM (Allocation h.inst_id) (MAP FST items)` suffices_by simp[] >>
  strip_tac >> gvs[MEM_MAP] >>
  drule collect_static_allocas_MEM >> strip_tac >>
  first_x_assum (drule o iffLR) >> strip_tac >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
  metis_tac[MEM_MAP]
QED

Theorem static_alloca_items_total:
  fn_inst_wf fn /\ fn_inst_ids_distinct fn ==>
  ?items. static_alloca_items fn = SOME items
Proof
  strip_tac >> simp[static_alloca_items_def] >>
  irule collect_static_allocas_total >>
  gvs[fn_inst_wf_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, o_DEF, EVERY_MEM,
      MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem source_static_alloca_items_total:
  o1_ctx_shape C /\ ctx_inst_ids_distinct C /\ MEM fn C.ctx_functions ==>
  ?items. static_alloca_items fn = SOME items
Proof
  strip_tac >> irule static_alloca_items_total >>
  metis_tac[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
            source_member_ids_distinct]
QED
