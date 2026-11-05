Theory lowerDloadCompareProducer
Ancestors
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  pointerConfinedDefs contextCodegenRel memLocDefs venomInst
  finite_map list pred_set words o1PassContract

Theorem ld_annotated_compare_shape[local]:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [EQ;LT;GT] /\ i.inst_operands = [a;b] /\
  (ld_op_prov AG a <> NONE \/ ld_op_prov AG b <> NONE) ==>
  ?u v. a = Var u /\ b = Var v /\ u IN fn_pv P fn /\ v IN fn_pv P fn
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `(?v. a = Var v /\ v IN fn_pv P fn) \/
    (?v. b = Var v /\ v IN fn_pv P fn)` by
    (spose_not_then assume_tac >>
     `ld_op_prov AG a = NONE /\ ld_op_prov AG b = NONE` by
       (conj_tac >> irule ld_annotated_scalar_prov >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  metis_tac[]
QED

Theorem ld_annotated_compare_cases:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [EQ;LT;GT] /\ i.inst_operands = [a;b] ==>
  op_taint tn a = {} /\ op_taint tn b = {} /\
  ((ld_op_prov AG a = NONE /\ ld_op_prov AG b = NONE) \/
   ?owner bs sz x y.
     ld_op_prov AG a = SOME(owner,(bs,sz)) /\
     ld_op_prov AG b = SOME(owner,(bs,sz)) /\ 0 < sz /\
     eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
     bs <= w2n x /\ w2n x <= bs+sz /\
     bs <= w2n y /\ w2n y <= bs+sz)
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     qexistsl [`fn`, `i`, `s`] >> simp[] >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> simp[]) >>
  `op_taint tn a = {} /\ op_taint tn b = {}` by metis_tac[MEM] >> simp[] >>
  Cases_on `ld_op_prov AG a = NONE /\ ld_op_prov AG b = NONE` >> simp[] >>
  `?u v. a = Var u /\ b = Var v /\ u IN fn_pv P fn /\ v IN fn_pv P fn` by
    metis_tac[ld_annotated_compare_shape] >> gvs[] >>
  `access_ok lo (ld_erase AG) fn i s` by metis_tac[ld_annotated_access_ok] >>
  `?bs sz x y. FLOOKUP (ld_erase AG) u = SOME(bs,sz) /\
     FLOOKUP (ld_erase AG) v = SOME(bs,sz) /\ 0 < sz /\
     eval_operand (Var u) s = SOME x /\ eval_operand (Var v) s = SOME y /\
     bs <= w2n x /\ w2n x <= bs+sz /\
     bs <= w2n y /\ w2n y <= bs+sz` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >> strip_tac >>
     `u IN FDOM (ld_erase AG) \/ v IN FDOM (ld_erase AG)` by
       (gvs[ld_op_prov_def, FLOOKUP_DEF, ld_erase_def, FDOM_o_f] >>
        metis_tac[]) >> metis_tac[]) >>
  `?oa. FLOOKUP AG u = SOME (oa,(bs,sz))` by
    (fs[ld_erase_lookup, AllCaseEqs()] >> PairCases_on `z` >> gvs[]) >>
  `?ob. FLOOKUP AG v = SOME (ob,(bs,sz))` by
    (fs[ld_erase_lookup, AllCaseEqs()] >> PairCases_on `z` >> gvs[]) >>
  `ld_live astk L AP AG (oa,(bs,sz)) /\
   ld_live astk L AP AG (ob,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  `oa = ob` by
    (drule ld_annotated_owner_separation >>
     disch_then (qspecl_then [`(oa,(bs,sz))`, `(ob,(bs,sz))`] mp_tac) >>
     simp[] >> decide_tac) >>
  simp[ld_op_prov_def] >> metis_tac[]
QED
