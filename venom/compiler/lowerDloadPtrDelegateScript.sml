Theory lowerDloadPtrDelegate
Ancestors lowerDloadPtrDelegateInterfaces lowerDloadPtrCallBuffers
  lowerDloadPtrPhi lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrScalar
  lowerDloadPtrResidualInterfaces lowerDloadPtrCall lowerDloadPtrExternalCall
  pointerConfinedDefs memLocDefs ptrDiscipline contextCodegenRel codegenRel
  venomExecSemantics venomState finite_map pred_set list

Theorem dload_delegate_success_inputs:
  i.inst_opcode = DELEGATECALL /\ step_inst fuel C i t = OK t1 ==>
  !op. MEM op i.inst_operands ==> eval_operand op t <> NONE
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dload_delegate_evaluated_inputs:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;addr;a;sz;r;rs] /\
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
  (!op. MEM op [gas;addr;sz;rs] ==> eval_operand op s = eval_operand op t) /\
  (!op x y. MEM op [a;r] /\ eval_operand op s = SOME x /\
    eval_operand op t = SOME y ==>
    dload_value_word fs {} (op_prov G op) (op_prov H op) x y) /\
  (!x y z. eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
    eval_operand sz s = SOME z ==>
    MEM (w2n x,w2n z) (source_memory_read_ranges i s) /\
    read_memory (w2n x) (w2n z) s = read_memory (w2n y) (w2n z) t) /\
  (!x z. eval_operand r s = SOME x /\ eval_operand rs s = SOME z ==>
    MEM (w2n x,w2n z) (source_memory_write_ranges i s)) /\
  tn.t_stor = {} /\ tn.t_trans = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. MEM op i.inst_operands ==> eval_operand op t <> NONE` by
    metis_tac[dload_delegate_success_inputs] >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s <> NONE` by metis_tac[] >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `!op. MEM op [gas;addr;sz;rs] ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule scalar_operand_equal >> disch_then irule >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all dload_delegate_scalar_safety >> simp[]) >>
     gvs[] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (fs[taint_ok_def] >> rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `op` mp_tac) >> simp[]) >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by gvs[taint_ok_def] >>
  `!op x y. MEM op [a;r] /\ eval_operand op s = SOME x /\
    eval_operand op t = SOME y ==>
    dload_value_word fs {} (op_prov G op) (op_prov H op) x y` by
    (rpt strip_tac >>
     `op_taint tn op = {}` by (gvs[] >> metis_tac[]) >>
     `!v. op = Var v ==> v IN V` by (gvs[] >> metis_tac[]) >>
     drule_all dload_matched_operand >> simp[]) >>
  simp[] >> conj_tac
  >- suspend "delegate_read_inputs"
  >> suspend "delegate_write_inputs"
QED

Resume dload_delegate_evaluated_inputs[delegate_read_inputs]:
  rpt strip_tac >>
  `MEM (w2n x,w2n z) (source_memory_read_ranges i s)` by
    (gvs[source_memory_read_ranges_def, memory_range_of_operands_def, AllCaseEqs()] >>
     Cases_on `eval_operand gas s` >> gvs[] >>
     Cases_on `eval_operand addr t` >> gvs[] >>
     Cases_on `eval_operand r s` >> gvs[] >>
     Cases_on `eval_operand rs t` >> gvs[] >> metis_tac[]) >>
  simp[] >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `dload_value_word fs {} (op_prov G a) (op_prov H a) x y` by simp[] >>
  `?ops. mem_read_ops i = SOME ops /\ ops.iao_ofst = a` by gvs[mem_read_ops_def] >>
  Q.SUBGOAL_THEN
    `i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
     i.inst_opcode = DELEGATECALL \/ i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2`
    assume_tac >- metis_tac[] >>
  drule_all dload_call_clean_slice >> simp[read_memory_def]
QED

Resume dload_delegate_evaluated_inputs[delegate_write_inputs]:
  rpt strip_tac >>
  gvs[source_memory_write_ranges_def, AllCaseEqs()] >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr t` >> gvs[] >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >> metis_tac[]
QED
Finalise dload_delegate_evaluated_inputs

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "delegate evaluated inputs: nonempty hypotheses")
  [dload_delegate_success_inputs, dload_delegate_evaluated_inputs];

Theorem dload_delegate_ghosts[local]:
  i.inst_opcode = DELEGATECALL /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp ==>
  step_prov PG G i s1 = set_prov G i.inst_outputs NONE /\
  step_taint i s s1 tn =
    <|t_mem := tn.t_mem DIFF
        {a | w2n ro <= a /\
             a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)};
      t_var := set_var_taint tn.t_var i.inst_outputs {};
      t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|>
Proof
  strip_tac >>
  `new_site_bytes s s1 = {}` by
    (gvs[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    (conj_tac >- (irule out_taint_opcode_exclusion >> simp[]) >>
     irule written_taint_opcode_exclusion >> simp[]) >>
  gvs[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
      step_writes_def, range_bytes_def, adopt_reset_def, store_taint_def,
      imm_taint_def]
QED

Theorem dload_delegate_frame_fields[local]:
  exec_delegatecall i s gas addr ao az ro rz = OK s1 ==>
  s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next /\
  s1.vs_fmp = s.vs_fmp /\ s1.vs_params = s.vs_params /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_call_ctx = s.vs_call_ctx /\
  (!v. ~MEM v i.inst_outputs ==> lookup_var v s1 = lookup_var v s) /\
  s1.vs_memory = (write_memory_with_expansion (w2n ro)
    (TAKE (w2n rz) s1.vs_returndata) s).vs_memory
Proof
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "delegate footprints: nonempty hypotheses")
  [dload_delegate_ghosts, dload_delegate_frame_fields];

Theorem dload_delegate_memory[local]:
  i.inst_opcode = DELEGATECALL /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  source_memory_write_ranges i t = [(w2n rt,w2n rz)] /\
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q ro rt /\
  exec_delegatecall i s gas addr ao az ro rz = OK s1 /\
  exec_delegatecall i t gas addr bo az rt rz = OK t1 /\
  s1.vs_returndata = t1.vs_returndata /\
  (w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n)) ==>
  dload_memory_match lo fs (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp /\
   t1.vs_allocas = t.vs_allocas /\ t1.vs_fmp = t.vs_fmp /\
   s1.vs_memory = (write_memory_with_expansion (w2n ro)
     (TAKE (w2n rz) s1.vs_returndata) s).vs_memory /\
   t1.vs_memory = (write_memory_with_expansion (w2n rt)
     (TAKE (w2n rz) s1.vs_returndata) t).vs_memory` by
    metis_tac[dload_delegate_frame_fields] >>
  `dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF
      {a | w2n ro <= a /\ a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)})
    (un with t_mem := un.t_mem DIFF
      {a | w2n rt <= a /\ a < w2n rt + MIN (w2n rz) (LENGTH s1.vs_returndata)}) s1 t1` by
    (irule dload_clean_return_memory_match >> metis_tac[]) >>
  `step_taint i s s1 tn =
    <|t_mem := tn.t_mem DIFF
        {a | w2n ro <= a /\ a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)};
      t_var := set_var_taint tn.t_var i.inst_outputs {};
      t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|>` by
    (irule (cj 2 dload_delegate_ghosts) >> metis_tac[]) >>
  `step_taint i t t1 un =
    <|t_mem := un.t_mem DIFF
        {a | w2n rt <= a /\ a < w2n rt + MIN (w2n rz) (LENGTH t1.vs_returndata)};
      t_var := set_var_taint un.t_var i.inst_outputs {};
      t_stor := un.t_stor; t_trans := un.t_trans; t_imm := un.t_imm|>` by
    (irule (cj 2 dload_delegate_ghosts) >> metis_tac[]) >>
  qpat_x_assum `dload_memory_match _ _ _ _ s1 t1` mp_tac >>
  pure_asm_rewrite_tac[] >>
  POP_ASSUM_LIST (K all_tac) >> simp[dload_memory_match_def] >> metis_tac[]
QED

val _ = if null (hyp dload_delegate_memory) then ()
  else raise Fail "delegate memory: nonempty hypotheses";


Theorem dload_delegate_reverse_inputs[local]:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} ==>
  dload_equal_environment t s /\ dload_shared_store un tn t s /\
  un.t_stor = {} /\ un.t_trans = {}
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    metis_tac[dload_delegate_full_stores] >>
  conj_tac
  >- gvs[dload_equal_environment_def, venom_state_component_equality] >>
  gvs[dload_shared_store_def, storage_agree_except_def, word_agree_except_def] >>
  metis_tac[]
QED

Theorem dload_delegate_exec_shape[local]:
  exec_delegatecall i s gas addr ao az ro rz = OK s1 ==>
  s1 = s with <|vs_vars := s1.vs_vars;
    vs_returndata := s1.vs_returndata; vs_accounts := s1.vs_accounts;
    vs_logs := s1.vs_logs;
    vs_memory := (write_memory_with_expansion (w2n ro)
       (TAKE (w2n rz) s1.vs_returndata) s).vs_memory;
    vs_transient := s1.vs_transient;
    vs_pending_deletions := s1.vs_pending_deletions;
    vs_outcomes := s1.vs_outcomes; vs_requests := s1.vs_requests|>
Proof
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, venom_state_component_equality]
QED

Theorem dload_delegate_exec_backward[local]:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  exec_delegatecall i t gas addr bo az rt rz = OK t1 ==>
  ?s1. exec_delegatecall i s gas addr ao az (ro:bytes32) rz = OK s1 /\
    dload_equal_environment s1 t1 /\
    s1.vs_accounts = t1.vs_accounts /\ s1.vs_transient = t1.vs_transient /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1)
Proof
  strip_tac >> drule_all dload_delegate_reverse_inputs >> strip_tac >>
  `read_memory (w2n bo) (w2n az) t = read_memory (w2n ao) (w2n az) s` by metis_tac[] >>
  drule_all (Q.ISPEC `ro:bytes32` (Q.GEN `tr` (SPEC_ALL dload_delegate_exec_success))) >>
  strip_tac >> first_x_assum (qspec_then `ro:bytes32` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `exec_delegatecall i s _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  drule dload_delegate_exec_shape >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `dload_equal_environment s t` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_delegate_step[local]:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;address;a;sz;r;rs] /\
  eval_operand gas s = SOME gv /\ eval_operand gas t = SOME gv /\
  eval_operand address s = SOME addr /\ eval_operand address t = SOME addr /\
  eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
  eval_operand sz s = SOME az /\ eval_operand sz t = SOME az /\
  eval_operand r s = SOME ro /\ eval_operand r t = SOME rt /\
  eval_operand rs s = SOME rz /\ eval_operand rs t = SOME rz /\
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    exec_delegatecall i s gv addr ao az ro rz = OK s1 /\
    exec_delegatecall i t gv addr bo az rt rz = OK t1 /\
    dload_equal_environment s1 t1 /\
    s1.vs_accounts = t1.vs_accounts /\ s1.vs_transient = t1.vs_transient /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst fuel Cs i s = exec_delegatecall i s gv addr ao az ro rz /\
   exec_delegatecall i t gv addr bo az rt rz = OK t1` by
    (qpat_x_assum `step_inst fuel Ct i t = OK t1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def]) >>
  drule_all dload_delegate_exec_backward >>
  disch_then (qspec_then `ro` strip_assume_tac) >>
  qexists `s1` >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "delegate backward: nonempty hypotheses")
  [dload_delegate_reverse_inputs, dload_delegate_exec_shape,
   dload_delegate_exec_backward, dload_delegate_step];

Theorem dload_delegate_shared_store[local]:
  i.inst_opcode = DELEGATECALL /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  exec_delegatecall i s gas addr ao az ro rz = OK s1 /\
  exec_delegatecall i t gas addr bo az rt rz = OK t1 /\
  s1.vs_accounts = t1.vs_accounts /\ s1.vs_transient = t1.vs_transient ==>
  dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  strip_tac >>
  `s1.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `exec_delegatecall i s _ _ _ _ _ _ = _` mp_tac >>
     disch_then (fn th => assume_tac th) >>
     drule dload_delegate_exec_shape >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `t1.vs_immutables = t.vs_immutables` by
    (qpat_x_assum `exec_delegatecall i s _ _ _ _ _ _ = _` kall_tac >>
     drule dload_delegate_exec_shape >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[dload_shared_store_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, storage_agree_except_def,
      word_agree_except_def] >> metis_tac[]
QED

Theorem dload_delegate_outputs[local]:
  exec_delegatecall i s gas addr ao az ro rz = OK s1 ==>
  ?out. i.inst_outputs = [out]
Proof
  simp[exec_delegatecall_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem dload_delegate_boundary[local]:
  i.inst_opcode = DELEGATECALL /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  source_memory_write_ranges i t = [(w2n rt,w2n rz)] /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  dload_value_word fs {} p q ro rt /\
  (w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n)) /\
  exec_delegatecall i s gas addr ao az ro rz = OK s1 /\
  exec_delegatecall i t gas addr bo az rt rz = OK t1 /\
  dload_equal_environment s1 t1 /\
  s1.vs_accounts = t1.vs_accounts /\ s1.vs_transient = t1.vs_transient /\
  (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) ==>
  dload_boundary_core lo fs V Ws PG PH
    (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
  (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t /\
   dload_memory_match lo fs tn un s t /\
   dload_shared_store tn un s t /\ dload_equal_environment s t /\
   dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs` by
    metis_tac[dload_boundary_core_def] >>
  `s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
   s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
   s1.vs_params = s.vs_params /\ t1.vs_params = t.vs_params /\
   s1.vs_fmp = s.vs_fmp /\ t1.vs_fmp = t.vs_fmp` by
    metis_tac[dload_delegate_frame_fields] >>
  `dload_vars_match fs V (step_prov PG G i s1) (step_prov PH H i t1)
     (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
   (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))` by
    (irule dload_scalar_result_vars >>
     metis_tac[dload_delegate_frame_fields, dload_delegate_outputs]) >>
  `dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (drule_all dload_delegate_shared_store >> simp[]) >>
  `s1.vs_returndata = t1.vs_returndata` by
    gvs[dload_equal_environment_def, venom_state_component_equality] >>
  `dload_memory_match lo fs (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (irule dload_delegate_memory >> metis_tac[]) >>
  simp[dload_boundary_core_def] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_boundary_core_def] >> strip_tac >>
  irule dload_allocation_neutral_tables >> metis_tac[]
QED

Theorem dload_boundary_core_delegate_shaped[local]:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;address;a;sz;r;rs] /\
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
  drule_all dload_delegate_evaluated_inputs >> strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op t <> NONE` by
    metis_tac[dload_delegate_success_inputs] >>
  `dload_equal_environment s t /\ dload_shared_store tn un s t` by
    metis_tac[dload_boundary_core_def] >>
  `?gv addr ao bo az ro rt rz.
    eval_operand gas s = SOME gv /\ eval_operand gas t = SOME gv /\
    eval_operand address s = SOME addr /\ eval_operand address t = SOME addr /\
    eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
    eval_operand sz s = SOME az /\ eval_operand sz t = SOME az /\
    eval_operand r s = SOME ro /\ eval_operand r t = SOME rt /\
    eval_operand rs s = SOME rz /\ eval_operand rs t = SOME rz` by
    (Cases_on `eval_operand gas s` >> gvs[] >>
     Cases_on `eval_operand address s` >> gvs[] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand a t` >> gvs[] >>
     Cases_on `eval_operand sz s` >> gvs[] >>
     Cases_on `eval_operand r s` >> gvs[] >>
     Cases_on `eval_operand r t` >> gvs[] >>
     Cases_on `eval_operand rs s` >> gvs[] >> metis_tac[]) >>
  `read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t` by
    metis_tac[] >>
  drule_all dload_delegate_step >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  `source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
   source_memory_write_ranges i t = [(w2n rt,w2n rz)]` by
    gvs[source_memory_write_ranges_def] >>
  `dload_value_word fs {} (op_prov G r) (op_prov H r) ro rt` by
    (first_x_assum irule >> simp[]) >>
  `(w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ op_prov G r <> NONE) ==>
    ?b n. op_prov G r = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n))` by
    (`?ops. mem_write_ops i = SOME ops /\ ops.iao_ofst = r` by
       gvs[mem_write_ops_def] >>
     `MEM (w2n ro,w2n rz) (source_memory_write_ranges i s)` by simp[] >>
     qpat_assum `ops.iao_ofst = r` (SUBST1_TAC o SYM) >>
     rpt strip_tac >> irule dload_write_access_containment >> simp[] >>
     metis_tac[]) >>
  drule_all dload_delegate_boundary >> strip_tac >>
  qexists `s1` >> simp[] >>
  metis_tac[dload_delegate_frame_fields]
QED

Theorem dload_boundary_core_delegate:
  i.inst_opcode = DELEGATECALL /\
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
  `?gas address a sz r rs. i.inst_operands = [gas;address;a;sz;r;rs]` by
    (qpat_x_assum `step_inst fuel Ct i t = OK t1` mp_tac >>
     simp[step_inst_non_invoke] >>
     pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
     Cases_on `i.inst_operands` >> simp[] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  irule dload_boundary_core_delegate_shaped >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "delegate full core: nonempty hypotheses")
  [dload_delegate_shared_store, dload_delegate_boundary,
   dload_boundary_core_delegate_shaped, dload_boundary_core_delegate];
