Theory concretizePtrOwnedAffinePrefix
Ancestors concretizePtrOwnedAssignPrefix concretizePtrTaggedSupport
  concretizePtrSourceOwnership concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrParamSupport
  ptrDiscipline pointerConfinedDefs o1PassLift contextCodegenRel
  venomInst finite_map list pred_set

Theorem ptr_tagged_affine_conditions[local]:
  affine_pointer_ops fn (ptr_roots P fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_operands = [x;y] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) ==>
  (inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG y = NONE)
Proof
  strip_tac >>
  `~(?v1 v2. x = Var v1 /\ y = Var v2 /\
      v1 IN fn_pv P fn /\ v2 IN fn_pv P fn) /\
    (inst.inst_opcode = SUB ==> !v. y = Var v ==> v NOTIN fn_pv P fn)` by
    (gvs[affine_pointer_ops_def, fn_pv_def] >> metis_tac[]) >>
  Cases_on `x` >> Cases_on `y` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP TG s` >> gvs[] >>
  Cases_on `FLOOKUP TG s'` >> gvs[] >> metis_tac[]
QED

Theorem ptr_owned_affine_conditions:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  ~ctx_has_dalloca C /\
  (!stk PG G tn fn inst s. frame_reachable vs0 C stk PG G tn fn inst s ==>
    taint_ok fn tn inst s) /\
  a.po_inst.inst_operands = [x;y] /\
  (a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
  op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
  (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)
Proof
  strip_tac >>
  `frame_reachable vs0 C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by metis_tac[] >>
  `op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>

  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions`
    by (qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
        simp[ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P a.po_fn` by gvs[EVERY_MEM] >>
  `!vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
    (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by metis_tac[] >>
  gvs[active_inst_def] >>
  `MEM a.po_inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `affine_pointer_ops a.po_fn (ptr_roots P a.po_fn)` by gvs[fn_ptr_ok_def] >>
  metis_tac[ptr_tagged_affine_conditions]
QED
