Theory lowerDloadStoreProducer
Ancestors
  lowerDloadLifetime arithmetic finite_map pred_set
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadAccessClassification lowerDloadStoreExecution
  lowerDloadPairedBoundary ptrDiscipline memLocDefs venomExecSemantics
  list words pointerConfinedDefs venomInst o1PassContract contextCodegenRel
  lowerDloadOwnership codegenRel

(* Length-parametric footprint: the store consumer instantiates n = 32.
   Separation is required only among currently live owners. *)
Theorem ld_fixed_live_write_footprint:
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\
  ((p = q /\ p+n <= lo) \/
   (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
     bs <= p /\ p+n <= bs+sz /\ q = bt+(p-bs))) ==>
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
    ((p<=a /\ a<p+n) <=> (q<=b /\ b<q+n))) /\
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
    p<=a /\ a<p+n ==> a-p=b-q)
Proof
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  simp[ld_site_bytes_def] >> strip_tac >>
  gvs[] >>
  qpat_assum `!owner bs bt sz. _ ==> lo <= bs /\ lo <= bt`
    (fn th => imp_res_tac th)
  >- decide_tac
  >- decide_tac
  >- decide_tac
  >- (Cases_on `owner = owner'`
      >- (gvs[ld_site_entry_def] >> decide_tac) >>
      qpat_x_assum `!owner other bs bt sz cs ct cz. _` drule_all >>
      decide_tac)
  >- decide_tac >>
  Cases_on `owner = owner'`
  >- (gvs[ld_site_entry_def] >> decide_tac) >>
  qpat_x_assum `!owner other bs bt sz cs ct cz. _` drule_all >> decide_tac
QED

Theorem ld_mstore_value_not_pointer[local]:
  ptr_use_ok P pv i /\ i.inst_opcode = MSTORE /\
  i.inst_operands = [dst;value] ==>
  !v. value = Var v ==> v NOTIN pv
Proof
  simp[ptr_use_ok_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  Cases_on `dst = Var v` >> simp[]
QED

Theorem ld_reachable_mstore_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst;value] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN V) /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\
    bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  step_inst fuel CT i t = OK t' ==>
  ?s' x v y w.
    step_inst fuel CS i s = OK s' /\
    s' = mstore (w2n x) v s /\ t' = mstore (w2n y) w t /\
    eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
    eval_operand value s = SOME v /\ eval_operand value t = SOME w /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `?y w. eval_operand dst t = SOME y /\ eval_operand value t = SOME w /\
    t' = mstore (w2n y) w t` by
    (qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MSTORE` (fn th => pure_rewrite_tac[th]) >>
     simp[exec_write2_def, AllCaseEqs()] >> metis_tac[]) >>
  `?x v. eval_operand dst s = SOME x /\ eval_operand value s = SOME v` by
    suspend "source_operands" >>
  `MEM fn CS.ctx_functions` by
    (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `ld_op_prov AG value = NONE` by
    (irule ld_annotated_scalar_prov >> goal_assum (drule_at Any) >>
     metis_tac[ld_mstore_value_not_pointer]) >>
  `ld_mask_word (op_taint tn value) (op_taint un value) v w` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`w`,`v`,`value`] mp_tac) >>
     simp[ld_owned_value_def]) >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `op_taint tn dst = {}` by
    (irule ld_taint_store_address_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM (w2n x,32) (source_memory_write_ranges i s)` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def] >>
  `((w2n x = w2n y /\ w2n x+32 <= lo) \/
    (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
      bs <= w2n x /\ w2n x+32 <= bs+sz /\
      w2n y = bt+(w2n x-bs)))` by
    suspend "write_classification" >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n x<=a /\ a<w2n x+32) <=> (w2n y<=b /\ b<w2n y+32))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n x<=a /\ a<w2n x+32 ==> a-w2n x=b-w2n y)` by
    (irule ld_fixed_live_write_footprint >> metis_tac[]) >>
  `step_inst fuel CS i s = OK (mstore (w2n x) v s)` by
    (simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MSTORE` (fn th => pure_rewrite_tac[th]) >>
     simp[exec_write2_def]) >>
  drule_all (ld_mstore_memory_backward |> Q.INST
    [`R` |-> `\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qx_choose_then `ss` strip_assume_tac) >>
  `ss = mstore (w2n x) v s` by
    gvs[step_inst_non_invoke] >>
  qexistsl_tac [`mstore (w2n x) v s`,`x`,`v`,`y`,`w`] >>
  gvs[]
QED

Resume ld_reachable_mstore_backward[source_operands]:
  drule ld_owned_operand_defined >>
  disch_then (qspec_then `dst` mp_tac) >> simp[] >> strip_tac >>
  drule ld_owned_operand_defined >>
  disch_then (qspec_then `value` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand value s` >>
  gvs[] >> metis_tac[]
QED

Resume ld_reachable_mstore_backward[write_classification]:
  drule ld_access_write_classification >>
  disch_then (qspecl_then [`w2n x`,`32`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      `ld_op_prov AG dst = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         simp[mem_write_ops_def, GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >>
      disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  disj2_tac >>
  gvs[mem_write_ops_def] >>
  `owner IN live` by metis_tac[] >>
  `v' IN V` by simp[] >>
  `?bt. ld_site_entry E owner bs bt sz` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`y`,`x`,`Var v'`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs+sz < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)` by
    metis_tac[] >>
  `0 < (32:num)` by decide_tac >>
  drule_all ld_owned_address_transport >> metis_tac[]
QED

Finalise ld_reachable_mstore_backward
