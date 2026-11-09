Theory lowerDloadBytesMemory
Ancestors
  lowerDloadBytesEffects lowerDloadBytesScalar lowerDloadCopyReadback
  lowerDloadMacroBoundary
  lowerDloadStoreProducer lowerDloadDefs lowerDloadCleanCopy
  lowerDloadAccessClassification lowerDloadReachableDiscipline
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  venomExecSemantics venomState venomInst memLocDefs finite_map
  list words pred_set lowerDloadRelocation codegenRel arithmetic

Theorem ld_reachable_bytes_memory:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  ~in_revert_forward fn s /\
  ld_owned_vars V E AG BH tn u0 s t0 /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN V) /\
  (!v owner bs size. FLOOKUP AG v = SOME(owner,(bs,size)) ==> owner IN live) /\
  (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
    lo <= bs /\ lo <= bt /\ bs+size < dimword(:256) /\
    bt+size < dimword(:256)) /\
  (!owner other bs bt size cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt size /\ ld_site_entry E other cs ct cz ==>
    (bs+size <= cs \/ cs+cz <= bs) /\ (bt+size <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem u0.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t0) /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  dload_offset_ok CS fn inst s ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint inst s z tn).t_mem u.t_mem
      (\a. read_memory a 1 z) (\b. read_memory b 1 t)
Proof
  strip_tac >>
  `eval_operand off s = eval_operand off t0 /\
   eval_operand sz s = eval_operand sz t0` by
    (drule_all ld_reachable_bytes_scalars >> simp[]) >>
  `?q x n. eval_operand dst t0 = SOME q /\
    eval_operand off t0 = SOME x /\ eval_operand sz t0 = SOME n` by
    (drule_all ld_bytes_completed_defined >> simp[]) >>
  `?p. eval_operand dst s = SOME p` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `dst` mp_tac) >> simp[] >>
     Cases_on `eval_operand dst s` >> gvs[]) >>
  `w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256)` by
    (fs[dload_offset_ok_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `ld_byte_rel R` >>
  qabbrev_tac `bs = TAKE (w2n n)
    (DROP (w2n x) s.vs_data_section ++ REPLICATE (w2n n) 0w)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`, LENGTH_TAKE] >>
  `step_inst fuel CS inst s = OK (write_memory_with_expansion (w2n p) bs s)` by
    (simp[step_inst_non_invoke, step_inst_base_def, Abbr `bs`]) >>
  `u.t_mem = u0.t_mem DIFF {b | w2n q <= b /\ b < w2n q + w2n n}` by
    (drule_all ld_bytes_completed_mem_taint >> simp[]) >>
  `(step_taint inst s (write_memory_with_expansion (w2n p) bs s) tn).t_mem =
    tn.t_mem DIFF {b | w2n p <= b /\ b < w2n p + w2n n}` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) ld_clean_copy_mem_taint >> simp[]) >>
  `t.vs_memory = (write_memory_with_expansion (w2n q) bs t0).vs_memory` by
    (drule_all ld_bytes_completed_memory >>
     drule_all ld_codecopy_payload >> disch_then (qspec_then `w2n n` mp_tac) >>
     simp[Abbr `bs`]) >>
  `(!aa bb. R aa bb ==> ((w2n p<=aa /\ aa<w2n p+w2n n) <=>
                          (w2n q<=bb /\ bb<w2n q+w2n n))) /\
   (!aa bb. R aa bb /\ w2n p<=aa /\ aa<w2n p+w2n n ==> aa-w2n p=bb-w2n q)` by
    suspend "footprint" >>
  qexists_tac `write_memory_with_expansion (w2n p) bs s` >> simp[] >>
  `ld_byte_rel R
    (tn.t_mem DIFF {aa | w2n p<=aa /\ aa<w2n p+LENGTH bs})
    (u0.t_mem DIFF {bb | w2n q<=bb /\ bb<w2n q+LENGTH bs})
    (\aa. read_memory aa 1 (write_memory_with_expansion (w2n p) bs s))
    (\bb. read_memory bb 1 (write_memory_with_expansion (w2n q) bs t0))` by
    (irule ld_shared_payload_write >> gvs[ADD_COMM]) >>
  gvs[ld_byte_rel_def, read_memory_def, read_byte_def] >> first_assum ACCEPT_TAC
QED

Resume ld_reachable_bytes_memory[footprint]:
  Cases_on `w2n n = 0` >- simp[] >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `op_taint tn dst = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM (w2n p,w2n n) (source_memory_write_ranges inst s)` by
    simp[source_memory_write_ranges_def, sized_source_write_range_def] >>
  `((w2n p = w2n q /\ w2n p+w2n n <= lo) \/
    (?owner bp bq size. owner IN live /\ ld_site_entry E owner bp bq size /\
      bp <= w2n p /\ w2n p+w2n n <= bp+size /\
      w2n q = bq+(w2n p-bp)))` by
    suspend "classify" >>
  simp_tac bool_ss [Abbr `R`] >> irule ld_fixed_live_write_footprint >> metis_tac[]
QED

Resume ld_reachable_bytes_memory[classify]:
  drule ld_access_write_classification >>
  disch_then (qspecl_then [`w2n p`,`w2n n`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      `ld_op_prov AG dst = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         simp[mem_write_ops_def, GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >>
      disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  disj2_tac >> gvs[mem_write_ops_def] >>
  `owner IN live` by metis_tac[] >>
  `v IN V` by simp[] >>
  `?bt. ld_site_entry E owner bs' bt sz'` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`q`,`p`,`Var v`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs'+sz' < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs' bt sz' ==> bt+sz' < dimword(:256)` by
    metis_tac[] >>
  `0 < w2n n` by (CCONTR_TAC >> gvs[w2n_eq_0]) >>
  `w2n p + w2n n <= bs'+sz'` by decide_tac >>
  drule_all ld_owned_address_transport >> metis_tac[ADD_COMM]
QED

Finalise ld_reachable_bytes_memory
