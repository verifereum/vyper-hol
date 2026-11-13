(* Actual decoder allocation rows discharge the existing caller memory frames. *)
Theory abiDecodeMemBuiltinFrame
Ancestors
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeImmutableFrame
  abiDecoderFrame allocationGrowth exprLoweringProps loweringStateRelDefs
  valueEncodingProps compileEnv venomState venomInst finite_map list arithmetic

Theorem abi_decode_mem_window_frame:
  abi_decode_footprint_frame fp s t /\
  (!b sz. MEM (b,sz) fp ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      start.cs_next_id <= inst.inst_id /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME(b,sz)) ==>
  abi_decode_window_frame func start s t
Proof
  strip_tac >> rw[abi_decode_window_frame_def] >>
  irule abi_decode_footprint_frame_slice >> goal_assum (drule_at Any) >>
  rw[abi_footprint_disjoint_def] >>
  qpat_x_assum `!b sz. MEM (b,sz) fp ==> _` drule >> strip_tac >>
  qpat_x_assum `!i b sz. MEM i (fn_insts func) /\ _ ==> _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem abi_decode_mem_immutable_memory:
  immutable_alloca_sep func ce cx es s /\ allocation_growth s t /\
  abi_decode_footprint_frame fp s t /\
  (!b sz. MEM (b,sz) fp ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME(b,sz)) ==>
  abi_decode_immutable_memory ce cx es s t
Proof
  strip_tac >> rw[abi_decode_immutable_memory_def] >>
  `off + type_memory_size tv <= s.vs_alloca_next /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME(b,sz) ==>
      loweringStateRelDefs$regions_disjoint off (type_memory_size tv) b sz)` by
    (qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [immutable_alloca_sep_def] >>
     disch_then (drule_all o CONJUNCT2) >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule abi_decode_footprint_frame_slice >> goal_assum (drule_at Any) >>
  rw[abi_footprint_disjoint_def] >>
  qpat_x_assum `!b sz. MEM (b,sz) fp ==> _` drule >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (`s.vs_alloca_next <= d` by metis_tac[allocation_growth_new] >> decide_tac) >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME x` by metis_tac[allocation_growth_old] >>
  gvs[] >>
  qpat_x_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED
