Theory lowerDloadPtrNormalNext
Ancestors lowerDloadPtrSupport lowerDloadPtrAggregate lowerDloadPtrPhase
  lowerDloadPtrRel lowerDloadDefs ptrDiscipline venomExecSemantics venomState
  contextCodegenRel list pred_set finite_map option

Theorem dload_normal_unchanged_successor:
  (!h. MEM h C.ctx_functions ==> fn_ptr_ok P h) /\
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                 ci.inst_id = id}) /\
  ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  (!k. k < LENGTH cs ==>
    dload_live_layout lo (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
      (DROP (SUC k) fs) /\
    dload_equal_environment (EL k cs).cf_state (EL k ds).cf_state /\
    (EL k cs).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL k cs).cf_inst = (EL k ds).cf_inst /\
    (!a. a IN set (fn_ir_vars (EL k cs).cf_fn) ==>
      (lookup_var a (EL k cs).cf_state = NONE <=> lookup_var a (EL k ds).cf_state = NONE)) /\
    (?qc. ir_supply_covers_fn qc (EL k cs).cf_fn /\
      (?qc'. lower_dload_function_supply qc (EL k cs).cf_fn = ((EL k ds).cf_fn,qc')) /\
      dload_control_match qc (EL k cs).cf_fn (EL k ds).cf_fn (EL k cs).cf_state (EL k ds).cf_state
        (EL k cs).cf_inst [(EL k cs).cf_inst] 0)) /\
  frame_reachable vs C cs PG G2 tn2 f i2 s2 /\
  dload_boundary_core fl lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G2 H2 tn2 un2 s2 t2 cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s2 = NONE <=> lookup_var v t2 = NONE)) /\
  dload_control_match q f g s2 t2 i2 emitted2 0 /\ j2 = EL 0 emitted2 /\
  t2.vs_allocas = t0.vs_allocas /\
  s2.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address ==>
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core fl lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t2 H2 un2 /\
    dload_control_match q f g s t2 i emitted n /\ j2 = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      dload_live_layout lo (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment (EL k cs).cf_state (EL k ds).cf_state /\
      (EL k cs).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      (EL k cs).cf_inst = (EL k ds).cf_inst /\
      (!a. a IN set (fn_ir_vars (EL k cs).cf_fn) ==>
        (lookup_var a (EL k cs).cf_state = NONE <=> lookup_var a (EL k ds).cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc (EL k cs).cf_fn /\
        (?qc'. lower_dload_function_supply qc (EL k cs).cf_fn = ((EL k ds).cf_fn,qc')) /\
        dload_control_match qc (EL k cs).cf_fn (EL k ds).cf_fn (EL k cs).cf_state (EL k ds).cf_state
          (EL k cs).cf_inst [(EL k cs).cf_inst] 0))
Proof
  strip_tac >>
  drule frame_reachable_prov_supported >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  qexistsl [`cs`,`PG`,`G2`,`tn2`,`f`,`i2`,`s2`,`q`,`emitted2`,`0`,
    `0`,`t2`,`H2`,`un2`,`fs`] >> simp[dload_prefix_zero] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < LENGTH fs ==> _` (qspec_then `k` mp_tac) >>
  Cases_on `k` >> simp[]
QED

Theorem dload_normal_changed_head_successor:
  (!h. MEM h C.ctx_functions ==> fn_ptr_ok P h) /\
  LENGTH (r::rs) = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH (r::rs) ==>
    (EL k (r::rs)).dr_scratch =
      FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                 ci.inst_id = id}) /\
  ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  (!k. k < LENGTH cs ==>
    dload_live_layout lo (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
      (DROP (SUC k) (r::rs)) /\
    dload_equal_environment (EL k cs).cf_state (EL k ds).cf_state /\
    (EL k cs).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL k cs).cf_inst = (EL k ds).cf_inst /\
    (!a. a IN set (fn_ir_vars (EL k cs).cf_fn) ==>
      (lookup_var a (EL k cs).cf_state = NONE <=> lookup_var a (EL k ds).cf_state = NONE)) /\
    (?qc. ir_supply_covers_fn qc (EL k cs).cf_fn /\
      (?qc'. lower_dload_function_supply qc (EL k cs).cf_fn = ((EL k ds).cf_fn,qc')) /\
      dload_control_match qc (EL k cs).cf_fn (EL k ds).cf_fn (EL k cs).cf_state (EL k ds).cf_state
        (EL k cs).cf_inst [(EL k cs).cf_inst] 0)) /\
  frame_reachable vs C cs PG G2 tn2 f i2 s2 /\
  dload_boundary_core fl lo (r1::rs)
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G2 H2 tn2 un2 s2 t2 cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s2 = NONE <=> lookup_var v t2 = NONE)) /\
  dload_control_match q f g s2 t2 i2 emitted2 0 /\ j2 = EL 0 emitted2 /\
  r1.dr_scratch = FDOM t2.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
  s2.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address ==>
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core fl lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t2 H2 un2 /\
    dload_control_match q f g s t2 i emitted n /\ j2 = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      dload_live_layout lo (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment (EL k cs).cf_state (EL k ds).cf_state /\
      (EL k cs).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      (EL k cs).cf_inst = (EL k ds).cf_inst /\
      (!a. a IN set (fn_ir_vars (EL k cs).cf_fn) ==>
        (lookup_var a (EL k cs).cf_state = NONE <=> lookup_var a (EL k ds).cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc (EL k cs).cf_fn /\
        (?qc'. lower_dload_function_supply qc (EL k cs).cf_fn = ((EL k ds).cf_fn,qc')) /\
        dload_control_match qc (EL k cs).cf_fn (EL k ds).cf_fn (EL k cs).cf_state (EL k ds).cf_state
          (EL k cs).cf_inst [(EL k cs).cf_inst] 0))
Proof
  strip_tac >>
  drule_at (Pat `dload_boundary_core`) dload_normal_unchanged_successor >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (qspecl_then [`t2`,`s`,`j2`,`P`,`C'`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >- gvs[] >> conj_tac >- (rpt strip_tac >> Cases_on `k` >> simp[]
      >- (simp[EXTENSION] >> metis_tac[]) >>
      qpat_x_assum `!k. k < LENGTH (r::rs) ==> _`
        (qspec_then `SUC n` mp_tac) >> gvs[]) >>
    rpt strip_tac >>
    qpat_x_assum `!k. k < LENGTH cs ==> _` (qspec_then `k` mp_tac) >> simp[])) >>
  simp[]
QED
