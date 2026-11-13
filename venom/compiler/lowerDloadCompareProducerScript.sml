Theory lowerDloadCompareProducer
Ancestors
  lowerDloadPureEffects lowerDloadVariableTransport lowerDloadMaskBounds
  lowerDloadParamProducer lowerDloadOpaqueExecution venomState
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  pointerConfinedDefs contextCodegenRel memLocDefs venomInst
  finite_map list pred_set words o1PassContract
  lowerDloadObservationBounds lowerDloadOrdinaryExecution
  lowerDloadTargetGeometry lowerDloadAllocation lowerDloadDefs unitMemInv

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

Theorem ld_annotated_compare_backward:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  MEM i.inst_opcode [EQ;LT;GT] /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `op_taint tn a = {} /\ op_taint tn b = {} /\
   ((ld_op_prov AG a = NONE /\ ld_op_prov AG b = NONE) \/
    ?owner bs sz x y.
      ld_op_prov AG a = SOME(owner,(bs,sz)) /\
      ld_op_prov AG b = SOME(owner,(bs,sz)) /\ 0 < sz /\
      eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
      bs <= w2n x /\ w2n x <= bs+sz /\
      bs <= w2n y /\ w2n y <= bs+sz)` by
    (drule_all ld_annotated_compare_cases >> simp[])
  >- (irule ld_owned_pure_scalar_backward >> simp[MEM] >>
      fs[MEM] >> metis_tac[]) >>
  `ld_owned_selection E (ld_op_prov AG a) (ld_op_prov BH a)` by
    metis_tac[ld_owned_op_selection] >>
  `?bt. ld_site_entry E owner bs bt sz` by
    (gvs[ld_owned_selection_def] >> metis_tac[]) >>
  `ld_live astk L AP AG (owner,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[ld_op_prov_selected]) >>
  `owner IN live` by metis_tac[] >>
  `bs+sz < dimword(:256) /\ bt+sz < dimword(:256)` by
    (drule_all ld_observed_site_endpoints >> simp[]) >>
  irule ld_owned_compare_backward >> simp[] >> metis_tac[]
QED

Theorem ld_compare_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  MEM i.inst_opcode [EQ;LT;GT] /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_frame_embedding E L H s' t' /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    ld_alloc_account keys d A s' t' /\ d = 32 * SUM (MAP CARD suspended) /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_step_prov BP BH H i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\
      bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params)) /\
    (s' with vs_vars := s.vs_vars) = s /\
    (t' with vs_vars := t.vs_vars) = t
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. a = Var v \/ b = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[] >> metis_tac[MEM]) >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (`!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN live` by
       metis_tac[] >>
     `!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
       bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next` by metis_tac[] >>
     drule_all ld_annotated_compare_backward >> simp[]) >>
  qexists_tac `s'` >>
  `MEM i.inst_opcode [ADD;SUB;EQ;LT;GT;MUL;Div;Mod;SDIV;SMOD;Exp;
    ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT]` by fs[MEM] >>
  `?w. s' = update_var out w s` by metis_tac[ld_pure_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_pure_update] >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       (qpat_x_assum `MEM i.inst_opcode [EQ;LT;GT]` mp_tac >>
        simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]) >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  `s' with vs_vars := s.vs_vars = s` by simp[ld_update_var_restore] >>
  `t' with vs_vars := t.vs_vars = t` by simp[ld_update_var_restore] >>
  `ld_frame_embedding E L H s' t'` by metis_tac[ld_frame_embedding_vars_transport] >>
  `ld_alloc_account keys d A s' t'` by metis_tac[ld_alloc_account_vars_transport] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t')` by
    metis_tac[ld_byte_rel_vars_transport] >>
  `(step_taint i s s' tn).t_mem = tn.t_mem /\
   (step_taint i s s' tn).t_stor = tn.t_stor /\
   (step_taint i s s' tn).t_trans = tn.t_trans /\
   (step_taint i s s' tn).t_imm = tn.t_imm /\
   (step_taint i t t' un).t_mem = un.t_mem /\
   (step_taint i t t' un).t_stor = un.t_stor /\
   (step_taint i t t' un).t_trans = un.t_trans /\
   (step_taint i t t' un).t_imm = un.t_imm` by
    metis_tac[ld_pure_taint_nonvar] >>
  qpat_x_assum `s' = update_var out w s` kall_tac >>
  qpat_x_assum `t' = update_var out w' t` kall_tac >>
  simp[ld_step_taint_bound] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[]
QED
