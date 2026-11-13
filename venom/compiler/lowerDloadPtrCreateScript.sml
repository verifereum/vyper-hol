Theory lowerDloadPtrCreate
Ancestors
  lowerDloadPtrCreateInterfaces lowerDloadPtrCallBuffers lowerDloadPtrExternalCall
  lowerDloadPtrResidualInterfaces lowerDloadPtrAggregate lowerDloadPtrRel
  lowerDloadPtrCall lowerDloadPtrPhi lowerDloadPtrBlockEntry lowerDloadPtrScalar
  ptrDiscipline venomExecSemantics venomState contextCodegenRel codegenRel
  pointerConfinedDefs memLocDefs finite_map pred_set list arithmetic

Theorem dload_create_operand_safety:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;a;sz] /\
    MEM op [value;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;a;sz;salt] /\
    MEM op [value;sz;salt])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s ==>
  op_prov G op = NONE /\
  (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {}) /\
  tn.t_stor = {} /\ tn.t_trans = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. op = Var v ==> v NOTIN pv` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
     qpat_x_assum `!v. _` (qspec_then `v` mp_tac) >>
     simp[] >> Cases_on `a = Var v` >> gvs[] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dload_create_success_inputs:
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  step_inst fuel C i t = OK t1 ==>
  (!op. MEM op i.inst_operands ==> eval_operand op t <> NONE) /\
  ~t.vs_call_ctx.cc_static /\
  ((i.inst_opcode = CREATE /\ ?v a z. i.inst_operands = [v;a;z]) \/
   (i.inst_opcode = CREATE2 /\ ?v a z salt. i.inst_operands = [v;a;z;salt]))
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  simp[] >> rpt strip_tac >> gvs[eval_operands_def] >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "CREATE operand interface: nonempty hypotheses")
  [dload_create_operand_safety, dload_create_success_inputs];

Theorem dload_create_evaluated_inputs:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;a;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;a;sz;salt])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel C i t = OK t1 ==>
  (!op. MEM op i.inst_operands ==> eval_operand op s <> NONE) /\
  (!op. MEM op (if i.inst_opcode = CREATE then [value;sz] else [value;sz;salt]) ==>
    eval_operand op s = eval_operand op t) /\
  (!x y z. eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
    eval_operand sz s = SOME z ==>
    read_memory (w2n x) (w2n z) s = read_memory (w2n y) (w2n z) t) /\
  ~s.vs_call_ctx.cc_static /\ tn.t_stor = {} /\ tn.t_trans = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. MEM op i.inst_operands ==> eval_operand op t <> NONE` by
    metis_tac[dload_create_success_inputs] >>
  `~t.vs_call_ctx.cc_static` by metis_tac[dload_create_success_inputs] >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s <> NONE` by metis_tac[] >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `!op. MEM op (if i.inst_opcode = CREATE then [value;sz] else [value;sz;salt]) ==>
    op_prov G op = NONE /\
    (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {}) /\
    tn.t_stor = {} /\ tn.t_trans = {}` by
    (gen_tac >> disch_tac >> irule dload_create_operand_safety >>
     gvs[] >> metis_tac[]) >>
  `!op. MEM op (if i.inst_opcode = CREATE then [value;sz] else [value;sz;salt]) ==>
    eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule scalar_operand_equal >>
     disch_then irule >> gvs[] >> metis_tac[]) >>
  `~s.vs_call_ctx.cc_static` by
    (fs[dload_boundary_core_def, dload_equal_environment_def,
        venom_state_component_equality]) >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by (gvs[] >> metis_tac[]) >>
  simp[] >> suspend "create_read_inputs"
QED

Resume dload_create_evaluated_inputs[create_read_inputs]:
  rpt strip_tac >>
  `op_taint tn a = {}` by (gvs[] >> metis_tac[]) >>
  `!v. a = Var v ==> v IN V` by (gvs[] >> metis_tac[]) >>
  `dload_value_word fs {} (op_prov G a) (op_prov H a) x y` by
    (drule_all dload_matched_operand >> simp[]) >>
  `MEM (w2n x,w2n z) (source_memory_read_ranges i s)` by
    (gvs[source_memory_read_ranges_def, memory_range_of_operands_def,
         AllCaseEqs()] >>
     Cases_on `eval_operand value s` >> gvs[] >>
     Cases_on `eval_operand salt s` >> gvs[] >> metis_tac[]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `?ops. mem_read_ops i = SOME ops /\ ops.iao_ofst = a` by
    (gvs[mem_read_ops_def] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
     i.inst_opcode = DELEGATECALL \/ i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2`
    assume_tac >- metis_tac[] >>
  drule_all dload_call_clean_slice >> simp[read_memory_def]
QED
Finalise dload_create_evaluated_inputs

val _ = if null (hyp dload_create_evaluated_inputs) then ()
        else raise Fail "CREATE evaluated inputs: nonempty hypotheses";

Theorem dload_create_step:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;a;sz] /\ salt = NONE) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;a;sz;so] /\
    eval_operand so s = salt /\ eval_operand so t = salt /\ salt <> NONE)) /\
  eval_operand value s = SOME vv /\ eval_operand value t = SOME vv /\
  eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
  eval_operand sz s = SOME az /\ eval_operand sz t = SOME az /\
  ~s.vs_call_ctx.cc_static /\ dload_equal_environment s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    exec_create i s vv ao az salt = OK s1 /\
    exec_create i t vv bo az salt = OK t1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx] >>
  `step_inst fuel Cs i s = exec_create i s vv ao az salt /\
   exec_create i t vv bo az salt = OK t1` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     fs[step_inst_non_invoke] >>
     qpat_x_assum `step_inst_base i t = OK t1` mp_tac >>
     pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
     Cases_on `salt` >> simp[Excl "consume_create_outcome_eq"]) >>
  drule_all dload_exec_create_environment >> strip_tac >>
  qexists `s1` >> simp[]
QED


Theorem dload_create_mem_ghost:
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp ==>
  (step_taint i s s1 tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  `new_site_bytes s s1 = {}` by
    (gvs[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `written_taint tn i s = {}` by
    (irule written_taint_opcode_exclusion >> simp[]) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def,
      source_memory_write_ranges_def, range_bytes_def]
QED

Theorem dload_create_boundary:
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  exec_create i s value ao az salt = OK s1 /\
  exec_create i t value bo az salt = OK t1 /\
  dload_equal_environment s1 t1 /\
  (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) ==>
  dload_boundary_core lo fs V Ws PG PH
    (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
  (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t /\
   dload_memory_match lo fs tn un s t /\
   dload_shared_store tn un s t /\ dload_equal_environment s t` by
    metis_tac[dload_boundary_core_def] >>
  `s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
   s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
   s1.vs_memory = s.vs_memory /\ t1.vs_memory = t.vs_memory /\
   s1.vs_params = s.vs_params /\ t1.vs_params = t.vs_params /\
   s1.vs_fmp = s.vs_fmp /\ t1.vs_fmp = t.vs_fmp` by
    metis_tac[dload_exec_create_footprint, dload_create_frame_fields] >>
  `dload_vars_match fs V (step_prov PG G i s1) (step_prov PH H i t1)
     (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
   (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))` by
    (irule dload_scalar_result_vars >> metis_tac[dload_create_frame_fields]) >>
  `dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (irule dload_exec_create_shared_store >> metis_tac[]) >>
  `dload_memory_match lo fs (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (`(step_taint i s s1 tn).t_mem = tn.t_mem /\
      (step_taint i t t1 un).t_mem = un.t_mem` by
       metis_tac[dload_create_mem_ghost] >>
     metis_tac[dload_memory_match_memory_cong, dload_memory_match_taint_cong]) >>
  simp[dload_boundary_core_def] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_boundary_core_def] >> strip_tac >>
  irule dload_allocation_neutral_tables >> metis_tac[]
QED

Theorem dload_boundary_core_create_shaped[local]:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;a;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;a;sz;so])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
    s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb /\
    s1.vs_prev_bb = s.vs_prev_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\ t1.vs_inst_idx = t.vs_inst_idx /\
    s1.vs_call_ctx = s.vs_call_ctx /\ t1.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_create_evaluated_inputs >> strip_tac >>
  `dload_equal_environment s t` by metis_tac[dload_boundary_core_def] >>
  `!op. MEM op i.inst_operands ==> eval_operand op t <> NONE` by
    metis_tac[dload_create_success_inputs] >>
  `?vv ao bo az.
    eval_operand value s = SOME vv /\ eval_operand value t = SOME vv /\
    eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
    eval_operand sz s = SOME az /\ eval_operand sz t = SOME az` by
    (Cases_on `eval_operand value s` >> gvs[] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand a t` >> gvs[] >>
     Cases_on `eval_operand sz s` >> gvs[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `?salt.
    ((i.inst_opcode = CREATE /\ i.inst_operands = [value;a;sz] /\ salt = NONE) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;a;sz;so] /\
      eval_operand so s = salt /\ eval_operand so t = salt /\ salt <> NONE))`
    (qx_choose_then `salt` assume_tac)
  >- (Cases_on `i.inst_opcode = CREATE` >- (qexists `NONE` >> gvs[]) >>
      qexists `eval_operand so s` >> gvs[] >> metis_tac[]) >>
  `read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t` by
    metis_tac[] >>
  drule_all dload_create_step >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  Q.SUBGOAL_THEN `i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2`
    assume_tac >- metis_tac[] >>
  drule_all dload_create_boundary >> strip_tac >>
  qexists `s1` >> simp[] >>
  qpat_x_assum `exec_create i s _ _ _ _ = OK s1`
    (strip_assume_tac o MATCH_MP dload_exec_create_footprint) >>
  qpat_x_assum `exec_create i t _ _ _ _ = OK t1`
    (strip_assume_tac o MATCH_MP dload_exec_create_footprint) >> simp[]
QED

Theorem dload_boundary_core_create:
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
    s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb /\
    s1.vs_prev_bb = s.vs_prev_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\ t1.vs_inst_idx = t.vs_inst_idx /\
    s1.vs_call_ctx = s.vs_call_ctx /\ t1.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_create_success_inputs >>
  disch_then (assume_tac o CONJUNCT2 o CONJUNCT2) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  irule dload_boundary_core_create_shaped >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "CREATE transport: nonempty hypotheses")
  [dload_create_step, dload_create_frame_fields, dload_create_mem_ghost,
   dload_create_boundary, dload_boundary_core_create_shaped,
   dload_boundary_core_create];
