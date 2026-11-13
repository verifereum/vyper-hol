Theory fmpStageFmpStepsDallocaShared
Ancestors
  fmpStageRel o1LowerDloadMapEvolution finite_map words pred_set
  ptrDiscipline o1LowerDloadRelocationKernel o1LowerDloadShared

Theorem fmp_dalloca_sites:
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  raw0 <= w2n raw /\ fmp0 <= lo /\
  w2n raw + z < dimword (:256) /\
  sm1 = (if z = 0 then sm else sm |+ ((w2n raw,z),(lo,id))) ==>
  fmp_sites_ok sm1 fmp0 raw0 (lo+z) (n2w (w2n raw+z))
Proof
  strip_tac >> Cases_on `z = 0`
  >- gvs[] >>
  gvs[fmp_sites_ok_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==> _`
    imp_res_tac >> simp[] >>
  metis_tac[]
QED

Theorem fmp_dalloca_ld_sites_update[local]:
  fmp_ld_sites (sm |+ ((b,z),(c,id))) =
    fmp_ld_sites sm |+ ((b,z),(b,c,z))
Proof
  simp[fmap_eq_flookup] >> gen_tac >> PairCases_on `x` >>
  simp[FLOOKUP_fmp_ld_sites, FLOOKUP_UPDATE] >>
  Cases_on `b = x0 /\ z = x1` >> simp[]
QED

Theorem fmp_dalloca_memory:
  ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  w2n s1.vs_fmp = w2n s.vs_fmp + z /\
  s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
  sm1 = (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,id))) ==>
  ld_memory_agree (fmp_ld_sites sm1) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory
Proof
  strip_tac >>
  gvs[step_taint_def, mem_taint_def, step_writes_def,
      codegenRelTheory.source_memory_write_ranges_def,
      range_bytes_def, written_taint_def] >>
  Cases_on `z = 0` >> gvs[] >>
  gvs[fmp_dalloca_ld_sites_update, ld_memory_agree_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs(), new_site_bytes_def] >>
  qpat_x_assum `!id b c z j. _` irule >>
  simp[] >> metis_tac[]
QED

Theorem fmp_dalloca_shared_fields:
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_returndata = t.vs_returndata /\ s.vs_halted = t.vs_halted /\
  inst.inst_opcode = DALLOCA /\
  s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
        (update_var out (n2w lo)
         (update_var aligned (n2w z)
          (update_var mask (~31w)
           (update_var plus31 (sz+31w) t))))) with vs_inst_idx := idx ==>
  ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn)
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1 /\
  s1.vs_returndata = t1.vs_returndata /\ s1.vs_halted = t1.vs_halted
Proof
  simp[ld_shared_agree_def, venomStateTheory.update_var_def,
       step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED

Theorem fmp_dalloca_shared:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  raw0 <= w2n s.vs_fmp /\ fmp0 <= lo /\
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  w2n s.vs_fmp + z < dimword (:256) /\
  sm1 = (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) /\
  s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
        (update_var out (n2w lo)
         (update_var aligned (n2w z)
          (update_var mask (~31w)
           (update_var plus31 (sz+31w) t))))) with vs_inst_idx := idx ==>
  fmp_sites_ok sm1 fmp0 raw0 (lo+z) s1.vs_fmp /\
  ld_memory_agree (fmp_ld_sites sm1) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn)
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1 /\
  s1.vs_returndata = t1.vs_returndata /\ s1.vs_halted = t1.vs_halted
Proof
  strip_tac >>
  `fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
   ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
   ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_returndata = t.vs_returndata /\ s.vs_halted = t.vs_halted`
    by fs[fmp_stage_rel_def] >>
  conj_tac
  >- (drule_all fmp_dalloca_sites >>
      simp[venomStateTheory.update_var_def]) >>
  conj_tac
  >- (irule fmp_dalloca_memory >>
      simp[venomStateTheory.update_var_def] >> metis_tac[]) >>
  irule fmp_dalloca_shared_fields >> metis_tac[]
QED
