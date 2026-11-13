Theory ctorDeployLoweringEntrySeparation
Ancestors
  loweringStateRelDefs
  ctorAbiActualFrame abiEncoderRegisteredEffect compileEnv exprLoweringProps
  venomMemDefs venomState venomInst finite_map pred_set words list arithmetic

Theorem deploy_ctor_alloca_lower_bound_frame:
  q <= s.vs_alloca_next /\
  ctor_actual_scratch func ids 0 s.vs_alloca_next t /\
  abi_encoder_registered_effect ids outs s t /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) ==>
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id IN ids`
  >- (fs[ctor_actual_scratch_def] >>
      first_x_assum drule_all >> strip_tac >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem deploy_ctor_alloca_lower_bound_update:
  t.vs_allocas = s.vs_allocas |+ (aid,(s.vs_alloca_next,cap)) /\
  q <= s.vs_alloca_next /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) ==>
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id = aid` >> gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem deploy_ctor_alloca_literal_sizes_frame:
  ctor_actual_scratch func ids 0 s.vs_alloca_next t /\
  abi_encoder_registered_effect ids outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
  (!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN ids /\ inst.inst_operands = [Lit n] ==> w2n n = 32) ==>
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id IN ids`
  >- (fs[ctor_actual_scratch_def] >> metis_tac[]) >>
  fs[abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem deploy_ctor_local_lower_bound_frame:
  (!name b sz. local_region ce scopes s name b sz ==> q <= b) /\
  (!name entry p sz w.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w ==> lookup_var p s = SOME w) ==>
  (!name b sz. local_region ce scopes t name b sz ==> q <= b)
Proof
  simp_tac bool_ss [local_region_def] >> metis_tac[]
QED

Theorem deploy_ctor_local_lower_bound_bind:
  !ce' ce name p cap scopes t q base.
  ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var p) cap) /\
  (!id b sz. local_region ce scopes t id b sz ==> q <= b) /\
  lookup_var p t = SOME (n2w base) /\ q <= base /\ base < dimword (:256) ==>
  (!id b sz. local_region ce' scopes t id b sz ==> q <= b)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `id = name`
  >- (gvs[local_region_def, FLOOKUP_UPDATE, w2n_n2w]) >>
  first_x_assum irule >>
  gvs[local_region_def, FLOOKUP_UPDATE] >> metis_tac[]
QED
