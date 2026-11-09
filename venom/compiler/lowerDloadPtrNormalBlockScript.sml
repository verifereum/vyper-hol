Theory lowerDloadPtrNormalBlock
Ancestors lowerDloadPtrBranch lowerDloadPtrEntry lowerDloadPtrSupport
  venomExecSemantics venomState venomExecProofs contextCodegenRel list rich_list pred_set

Theorem dload_normal_branch_block:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!a v lbl op w. MEM a (fn_insts f) /\ a.inst_opcode = PHI /\
    a.inst_outputs = [v] /\ v IN V /\
    resolve_phi lbl a.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\ ~t1.vs_halted /\
  enters_block g t1 t2 /\ active_inst g j t2 /\
  (!h. MEM h C.ctx_functions ==> fn_ptr_ok P h) /\
  ir_supply_covers_fn q f /\
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                 ci.inst_id = id}) /\
  (!k. k < LENGTH cs ==>
    let c = EL k cs; d = EL k ds in
    dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
      (DROP (SUC k) fs) /\
    dload_equal_environment c.cf_state d.cf_state /\
    c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    c.cf_inst = d.cf_inst /\
    (!a. a IN set (fn_ir_vars c.cf_fn) ==>
      (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
    (?qc. ir_supply_covers_fn qc c.cf_fn /\
      (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
      dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
        c.cf_inst [c.cf_inst] 0)) ==>
  ?s1 s2 i' emitted'.
    step_inst fuel C i s = OK s1 /\ ~s1.vs_halted /\
    enters_block f s1 s2 /\
    frame_reachable vs C cs PG (entry_prov f s1 G)
      (entry_taint_vars f s1 tn) f i' s2 /\
    dload_control_match q f g s2 t2 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s2 = NONE <=> lookup_var v t2 = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (entry_prov f s1 G) (entry_prov g t1 H)
      (entry_taint_vars f s1 tn) (entry_taint_vars g t1 un) s2 t2 cs ds /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t2::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s2.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0)) /\
    ir_supply_covers_fn q f /\
    FDOM (entry_prov f s1 G) SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name)
Proof
  strip_tac >> drule_all dload_actual_branch_block_tracked >> strip_tac >>
  qexistsl_tac [`s1`, `s2`, `i'`, `emitted'`] >> simp[] >>
  conj_tac >- suspend "stack" >>
  conj_tac >- suspend "saved" >>
  suspend "support"
QED

Resume dload_normal_branch_block[stack]:
  `t1.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `step_inst fuel C' i t = OK t1` mp_tac >>
     gvs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[jump_to_def]) >>
  `t2.vs_allocas = t.vs_allocas` by
    metis_tac[dload_enters_block_allocations] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < LENGTH fs ==> _` (qspec_then `k` mp_tac) >>
  Cases_on `k` >> simp[]
QED

Resume dload_normal_branch_block[saved]:
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `step_inst fuel C i s = OK s1` mp_tac >>
     gvs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[jump_to_def]) >>
  `s2.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `enters_block f s1 s2` mp_tac >>
     rw[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < LENGTH cs ==> _` (qspec_then `k` mp_tac) >>
  simp[]
QED

Resume dload_normal_branch_block[support]:
  qpat_assum `frame_reachable vs C cs _ _ _ f i' s2`
    (mp_then Any mp_tac frame_reachable_prov_supported) >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >>
  strip_tac >> rpt conj_tac >> rpt strip_tac >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Finalise dload_normal_branch_block
