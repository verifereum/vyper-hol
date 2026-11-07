Theory bodyPtrStructLitOwnershipReservation
Ancestors bodyPtrStructLitCompilerOwnership bodyPtrStructLitOwnershipSteps
  loweringShapeRules loweringShapeDefs compileEnv venomInst list stmtLowering
  finite_map arithmetic

Theorem alloc_writers_unique_alloca_commit:
  alloc_writers_unique st /\
  (!i. MEM i (state_insts st) ==> ~MEM x i.inst_outputs) /\
  emit_inst ALLOCA ops [x] st = (u,st') ==>
  alloc_writers_unique st'
Proof
  rw[emit_inst_eq] >>
  gvs[alloc_writers_unique_def, state_insts_def, all_blocks_def,
      mk_inst_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem alloca_commit_other_nonowned:
  emit_inst ALLOCA ops [x] st = (u,st') /\
  y <> x /\ ~alloc_owned st y ==> ~alloc_owned st' y
Proof
  rw[emit_inst_eq] >>
  gvs[alloc_owned_def, opaque_out_def, state_insts_def, all_blocks_def,
      mk_inst_def] >> rpt strip_tac >>
  Cases_on `inst = mk_inst st.cs_next_id ALLOCA ops [x]` >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem declare_local_alloca_fresh_commit:
  cenv.ce_alloca_locals /\ shape_base_state st /\ alloc_writers_unique st /\
  declare_local cenv id ty st = (cenv',st1) /\
  emit_local_alloca cenv' id st1 = (u,st2) ==>
  alloc_writers_unique st2 /\ alloc_frame st st2
Proof
  simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def] >>
  strip_tac >>
  gvs[fresh_var_def, comp_bind_def, comp_return_def] >>
  gvs[emit_local_alloca_def, FLOOKUP_UPDATE, emit_inst_eq] >>
  conj_tac
  >- (gvs[alloc_writers_unique_def, shape_base_state_def,
          state_insts_def, all_blocks_def, mk_inst_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_def, LESS_EQ_REFL]) >>
  simp[alloc_frame_def, not_fresh_at_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by metis_tac[LESS_EQ_REFL] >>
  gvs[alloc_owned_def, opaque_out_def, state_insts_def, all_blocks_def,
      mk_inst_def] >> metis_tac[]
QED

Theorem declare_local_nonalloca_commit_noop:
  ~cenv.ce_alloca_locals /\
  (!x n. FLOOKUP cenv.ce_vars id <> SOME (PtrVar (Var x) n)) /\
  declare_local cenv id ty st = (cenv',st1) /\
  emit_local_alloca cenv' id st1 = (u,st2) ==> st2 = st
Proof
  simp[declare_local_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[emit_local_alloca_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> gvs[comp_return_def] >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME loc` >>
  Cases_on `loc` >> gvs[comp_return_def] >>
  rename1 `PtrVar op n` >> Cases_on `op` >> gvs[comp_return_def]
QED

Theorem declare_local_alloca_conditional_commit:
  (cenv.ce_alloca_locals \/
   (!x n. FLOOKUP cenv.ce_vars id <> SOME (PtrVar (Var x) n))) /\
  shape_base_state st /\ alloc_writers_unique st /\
  declare_local cenv id ty st = (cenv',st1) /\
  emit_local_alloca cenv' id st1 = (u,st2) ==>
  alloc_writers_unique st2 /\ alloc_frame st st2
Proof
  Cases_on `cenv.ce_alloca_locals` >> simp[] >> strip_tac
  >- (irule declare_local_alloca_fresh_commit >> metis_tac[]) >>
  drule_all declare_local_nonalloca_commit_noop >> strip_tac >>
  gvs[alloc_frame_refl]
QED
