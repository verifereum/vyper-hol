Theory concretizePtrBPReverse
Ancestors venomWfProps
  concretizePtrClosure concretizePtrBPOrigins basePtrProps ptrDiscipline
  venomWf venomInst pointerConfinedDefs pointerClosure basePtrDefs list pred_set
  removeUnusedSsaProofs

Theorem ptr_reverse_roots_finite[local]:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE_I >>
  qexists `IMAGE THE (IMAGE inst_output (set (fn_insts fn)))` >>
  simp[ptr_roots_def, alloca_roots_def, SUBSET_DEF] >>
  metis_tac[optionTheory.THE_DEF]
QED

Theorem ptr_reverse_alloc_subset[local]:
  pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET fn_pv P fn
Proof
  simp[fn_pv_def] >> irule ptr_derived_mono >>
  simp[ptr_bp_alloc_roots_finite, ptr_reverse_roots_finite] >>
  simp[ptr_bp_alloc_roots_def, ptr_roots_def, alloca_roots_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ptr_reverse_nonptr_empty[local]:
  ptr_bp_origins fn bp /\ v NOTIN fn_pv P fn ==> bp_get_ptrs bp v = []
Proof
  strip_tac >> Cases_on `bp_get_ptrs bp v` >> simp[] >>
  rename1 `bp_get_ptrs bp v = p::ps` >>
  Cases_on `p` >> rename1 `Ptr alloc off` >> Cases_on `alloc` >>
  gvs[ptr_bp_origins_def] >>
  `v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn n)` by
    (first_x_assum irule >> qexists `off` >> simp[]) >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn n) SUBSET fn_pv P fn` by
    irule ptr_reverse_alloc_subset >>
  fs[SUBSET_DEF]
QED

Theorem ptr_reverse_phi_member[local]:
  !ops. phi_well_formed ops /\ MEM (Var v) ops ==>
    MEM v (MAP SND (phi_pairs ops))
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def, phi_pairs_def] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_reverse_output[local]:
  LENGTH inst.inst_outputs = 1 /\ MEM out inst.inst_outputs ==>
  inst_output inst = SOME out
Proof
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[inst_output_def] >> metis_tac[]
QED

Theorem ptr_reverse_affine[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [op1; op2] ==>
  ~(?v1 v2. op1 = Var v1 /\ op2 = Var v2 /\
             v1 IN fn_pv P fn /\ v2 IN fn_pv P fn) /\
  (inst.inst_opcode = SUB ==> !v. op2 = Var v ==> v NOTIN fn_pv P fn)
Proof
  simp[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def,
       fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ptr_reverse_no_labels[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn ==>
  !l. ~MEM (Label l) inst.inst_operands
Proof
  simp[fn_ptr_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!inst. MEM inst _ ==> _` (qspec_then `inst` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ptr_reverse_step[local]:
  fn_ptr_ok P fn /\ ptr_bp_origins fn bp /\
  MEM inst (fn_insts fn) /\ inst_wf inst /\
  is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn /\
  MEM out inst.inst_outputs /\
  bp_derives bp (\i. MEM i (fn_insts fn)) v (Allocation aid) ==>
  bp_derives bp (\i. MEM i (fn_insts fn)) out (Allocation aid)
Proof
  strip_tac >>
  `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
   inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI` by
    (Cases_on `inst.inst_opcode` >> fs[is_pointer_preserving_op_def]) >>
  gvs[inst_wf_def] >>
  `inst_output inst = SOME out` by metis_tac[ptr_reverse_output]
  >- (
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      drule ptr_reverse_affine >> strip_tac >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (irule ptr_reverse_no_labels >> simp[] >>
         qexistsl [`P`, `fn`, `v`] >> simp[]) >>
      (namedCases_on `h` ["n", "w", "lbl"]
       >- (irule bp_derives_add_lit >> goal_assum (drule_at Any) >>
           simp[] >> metis_tac[])
       >- (
           `w NOTIN fn_pv P fn` by
             (qpat_x_assum `!op2 op1 inst. _` 
               (qspecl_then [`EL 1 inst.inst_operands`,
                             `EL 0 inst.inst_operands`, `inst`] mp_tac) >>
              simp[]) >>
           `bp_get_ptrs bp w = []` by metis_tac[ptr_reverse_nonptr_empty] >>
           irule bp_derives_add_var >> goal_assum (drule_at Any) >>
           simp[] >> metis_tac[])
       >> gvs[]))
  >- (
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      drule ptr_reverse_affine >> strip_tac >>
      qpat_x_assum `!op2 op1 inst. _`
        (qspecl_then [`EL 1 inst.inst_operands`,
                      `EL 0 inst.inst_operands`, `inst`] mp_tac) >>
      simp[] >> strip_tac >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (irule ptr_reverse_no_labels >> simp[] >>
         qexistsl [`P`, `fn`, `v`] >> simp[]) >>
      (namedCases_on `h` ["n", "w", "lbl"]
       >- (irule bp_derives_sub_lit >> goal_assum (drule_at Any) >>
           simp[] >> metis_tac[])
       >- (`bp_get_ptrs bp w = []` by metis_tac[ptr_reverse_nonptr_empty] >>
           irule bp_derives_sub_var >> goal_assum (drule_at Any) >>
           simp[] >> metis_tac[])
       >> gvs[]))
  >- (
      Cases_on `inst.inst_operands` >> gvs[] >>
      irule bp_derives_assign >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >> irule bp_derives_phi >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[ptr_reverse_phi_member]
QED

Theorem ptr_bp_derived_reverse:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\ ptr_bp_origins fn bp /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  bp_derives bp (\i. MEM i (fn_insts fn)) v (Allocation aid)
Proof
  strip_tac >>
  `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) SUBSET
     {u | u IN fn_pv P fn /\
          bp_derives bp (\i. MEM i (fn_insts fn)) u (Allocation aid)}` suffices_by
    simp[SUBSET_DEF] >>
  irule ptr_derived_least >> simp[ptr_bp_alloc_roots_finite] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (simp[fn_pv_def] >> irule pointer_derived_vars_closed >>
          simp[ptr_reverse_roots_finite] >> goal_assum (drule_at Any) >>
          gvs[fn_pv_def] >> metis_tac[])
      >> irule ptr_reverse_step >> goal_assum (drule_at Any) >>
      gvs[EVERY_MEM] >> metis_tac[])
  >> simp[SUBSET_DEF, ptr_bp_alloc_roots_def] >> rpt strip_tac
  >- (rename1 `inst_output inst = SOME out` >> simp[fn_pv_def] >>
      `out IN ptr_roots P fn` by
        (simp[ptr_roots_def, alloca_roots_def] >> metis_tac[]) >>
      metis_tac[pointer_derived_vars_roots, ptr_reverse_roots_finite, SUBSET_DEF])
  >> qpat_x_assum `inst.inst_id = aid` (SUBST_ALL_TAC o SYM) >>
  irule bp_derives_alloca >> simp[]
QED

Theorem ptr_bp_stable_coverage:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\ ptr_bp_origins fn bp /\
  (!inst. MEM inst (fn_insts fn) ==> FST (bp_handle_inst bp inst) = F) /\
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  ?off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v)
Proof
  strip_tac >> drule_all ptr_bp_derived_reverse >>
  strip_tac >> drule bp_derives_complete >> disch_then irule >> simp[]
QED

Theorem ptr_bp_stable_support_iff:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\ ptr_bp_origins fn bp /\
  (!inst. MEM inst (fn_insts fn) ==> FST (bp_handle_inst bp inst) = F) ==>
  ((?off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v)) <=>
   v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid))
Proof
  strip_tac >> eq_tac
  >- (gvs[ptr_bp_origins_def] >> metis_tac[])
  >> strip_tac >> irule ptr_bp_stable_coverage >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ptr_bp_analyze_stable_support_iff:
  fn_ptr_ok P fn /\ EVERY inst_wf (fn_insts fn) /\
  (!inst. MEM inst (fn_insts fn) ==>
    FST (bp_handle_inst (bp_analyze_fuel fuel cfg fn) inst) = F) ==>
  ((?off. MEM (Ptr (Allocation aid) off)
              (bp_get_ptrs (bp_analyze_fuel fuel cfg fn) v)) <=>
   v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid))
Proof
  strip_tac >> irule ptr_bp_stable_support_iff >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[ptr_bp_origins_def] >> metis_tac[ptr_bp_analyze_origins]
QED
