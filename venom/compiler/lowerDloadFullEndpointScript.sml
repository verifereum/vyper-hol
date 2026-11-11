(* Exhaustive endpoint of a nonterminal, non-INVOKE expansion. *)
Theory lowerDloadFullEndpoint
Ancestors
  lowerDloadOrdinaryEndpoint lowerDloadExpansionEndpoint
  lowerDloadSafetyUpdates lowerDloadOracleCallAssembly
  lowerDloadSafetyAllocation lowerDloadSafetyLocations lowerDloadSafetyAmbient
  lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadConfiguredOrigins
  o1LowerDloadClosure ptrDiscipline venomWf venomInst venomState
  venomExecSemantics o1PassContract unitMemInv lowerDloadDefs
  contextCodegenRel finite_map pred_set list arithmetic

Theorem ld_full_endpoint:
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  reserved_intervals_wf C.ctx_global_reserved /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs0 /\ fmp_free_ctx C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  mem_inv raw_mem_ok C vs0 /\ mem_inv dload_offset_ok C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
  (!fn. MEM fn C.ctx_functions ==>
    lookup_function fn.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))) /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) /\
  fn' = ld_image f /\ ir_supply_covers_fn f.lf_supply fn /\
  ~in_revert_forward fn s /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' fn' X p h t0 t /\ SUC h = LENGTH X /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' (EL h X) t = OK u ==>
  ?ss Ar g.
    step_inst 0 C inst s = OK ss /\
    u.vs_inst_idx = t.vs_inst_idx /\
    (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = p + LENGTH X /\
    g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
    g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := p + LENGTH X) /\
    g.lf_tv = (step_taint inst s ss tn).t_var /\
    step_prov PG G inst ss = ld_erase Ar o_f g.lf_H /\
    ld_vars P Ar g /\ ld_maps Ar g /\
    ld_memory lo Ar (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_global lo Ar (g::fs) /\ FDOM Ar = ld_slots Ar (g::fs) /\
    EVERY (ld_maps Ar) fs /\
    (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (g::fs) /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) (g::fs) /\
    (!j k. j < k /\ k < LENGTH (g::fs) ==>
      list_precedes (EL j (g::fs)).lf_fn.fn_name
                    (EL k (g::fs)).lf_fn.fn_name names) /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N)
Proof
  strip_tac >>
  `active_inst fn inst s` by metis_tac[ld_sync_source] >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, active_inst_def] >> metis_tac[EL_MEM]) >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- suspend "dload" >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- suspend "dloadbytes" >>
  `X = [inst]` by (drule_all ld_envelope_ordinary >> simp[]) >>
  gvs[] >>
  `t = t0` by metis_tac[ld_prefix_zero] >> gvs[] >>
  `t.vs_inst_idx = p` by metis_tac[ld_sync_envelope_position] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- suspend "alloca" >>
  `ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p` by metis_tac[] >>
  drule_all (SRULE [EVERY_DEF] ld_ordinary_endpoint) >> strip_tac >>
  qexistsl [`ss`,`A`,`g`] >> simp[] >>
  drule ld_head_order_cong >> simp[]
QED

Resume ld_full_endpoint[dload]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_dload_endpoint >> strip_tac >>
  qexistsl [`ss`,`Ar`,`g`] >> simp[]
QED
Resume ld_full_endpoint[dloadbytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all ld_dloadbytes_endpoint >> strip_tac >>
  qexistsl [`ss`,`Ar`,`g`] >> simp[]
QED
Resume ld_full_endpoint[alloca]:
  `?out. inst.inst_outputs = [out]` by
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `?sz. inst.inst_operands = [Lit sz]` by metis_tac[ld_alloca_step] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `MEM out (fn_ir_vars fn)` by
    (irule ld_inst_output_ir >> qexists `inst` >> simp[]) >>
  `out IN fn_pv P fn` by
    (mp_tac ptr_roots_subset_fn_pv >>
     simp[SUBSET_DEF, ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists `inst` >> simp[inst_output_def]) >>
  `ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p` by metis_tac[] >>
  `ir_supply_covers_fn f.lf_supply fn` by metis_tac[] >>
  `u.vs_inst_idx = t.vs_inst_idx` by metis_tac[step_inst_preserves_inst_idx] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- suspend "fresh" >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME bn` >>
  PairCases_on `bn` >>
  drule_all ld_cached_alloca_endpoint >> strip_tac >>
  `g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
   g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
   g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := p+1) /\
   g.lf_tv = (step_taint inst s ss tn).t_var` by simp[] >>
  qpat_x_assum `g = _` kall_tac >>
  qexistsl [`ss`,`A`,`g`] >> simp[] >>
  drule ld_head_order_cong >> simp[]
QED
Resume ld_full_endpoint[fresh]:
  `(f.lf_serial,inst.inst_id) NOTIN FDOM A` by
    (drule_all ld_sync_original_site_fresh >> simp[]) >>
  drule_all ld_fresh_alloca_endpoint >> strip_tac >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  qexistsl [`ss`,`Ar`,`g`] >> simp[] >>
  drule ld_head_order_cong >> simp[]
QED
Finalise ld_full_endpoint

val _ = if null (hyp ld_full_endpoint) then ()
  else raise Fail "full endpoint has hypotheses";
