(* Operational boundaries for the actual clone/rewrite pipeline. *)
Theory functionInlinerOperational
Ancestors
  functionInlinerFrame functionInlinerOpacity functionInlinerNamespace
  functionInlinerDefs venomExecSemantics venomState venomInst list rich_list

Theorem inline_parameter_step:
  MEM inst.inst_opcode [PARAM; FMP_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] /\
  w2n idx < LENGTH s.vs_params ==>
  step_inst fuel ctx inst s = OK (update_var x (EL (w2n idx) s.vs_params) s)
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def]
QED

Theorem inline_token_step:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [x] ==>
  step_inst fuel ctx inst s = OK (update_var x s.vs_return_pc_token s)
Proof
  rpt strip_tac >> simp[step_inst_non_invoke, step_inst_base_def]
QED

Theorem rewrite_inline_parameter_step:
  is_param_opcode inst.inst_opcode /\ param_idx < LENGTH args /\
  inst.inst_outputs = [x] /\ eval_operand (EL param_idx args) t = SOME w ==>
  rewrite_inline_inst args outs ret inst param_idx =
    ([inst with <| inst_opcode := ASSIGN; inst_operands := [EL param_idx args] |>], param_idx + 1) /\
  step_inst fuel ctx
    (inst with <| inst_opcode := ASSIGN; inst_operands := [EL param_idx args] |>) t =
    OK (update_var x w t)
Proof
  rpt strip_tac >>
  simp[rewrite_inline_inst_def, step_inst_non_invoke, step_inst_base_def,
    eval_operands_def]
QED

Theorem inline_parameter_rewrite_frame:
  MEM inst.inst_opcode [PARAM; FMP_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [x] /\
  w2n idx < LENGTH s.vs_params /\ param_idx < LENGTH args /\
  eval_operand (EL param_idx args) t = SOME (EL (w2n idx) s.vs_params) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  ?s' t'. step_inst fuel ctx inst s = OK s' /\
    step_inst fuel ctx'
      ((clone_instruction p labels inst) with
        <| inst_opcode := ASSIGN; inst_operands := [EL param_idx args] |>) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  qexistsl [`update_var x (EL (w2n idx) s.vs_params) s`,
    `update_var (STRCAT p x) (EL (w2n idx) s.vs_params) t`] >>
  conj_tac >- (irule inline_parameter_step >> simp[]) >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, clone_instruction_def,
      eval_operands_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_token_rewrite_frame:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [x] /\ x IN opaque /\
  param_idx < LENGTH args /\ EL param_idx args = Lit 0w /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  rewrite_inline_inst args outs ret (clone_instruction p labels inst) param_idx =
    ([(clone_instruction p labels inst) with
      <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>], param_idx + 1) /\
  ?s' t'. step_inst fuel ctx inst s = OK s' /\
    step_inst fuel ctx'
      ((clone_instruction p labels inst) with
        <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def] >>
  qexistsl [`update_var x s.vs_return_pc_token s`,
    `update_var (STRCAT p x) 0w t`] >>
  conj_tac >- (irule inline_token_step >> simp[]) >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, clone_instruction_def,
      eval_operands_def, eval_operand_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_token_seed >> simp[]
QED

(* Operand evaluation is a boundary premise: opaque copies may carry a
   different word, but ordinary outputs must receive the same value. *)
Theorem inline_assign_clone_frame:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [x] /\ eval_operand op s = SOME a /\
  eval_operand (clone_operand p labels op) t = SOME b /\
  (x NOTIN opaque ==> a = b) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  ?s' t'. step_inst fuel ctx inst s = OK s' /\
    step_inst fuel ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  qexistsl [`update_var x a s`, `update_var (STRCAT p x) b t`] >>
  conj_tac >- simp[step_inst_non_invoke, step_inst_base_def] >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_pure2_clone_frame:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_pure2 f inst s = OK s' ==>
  ?t'. exec_pure2 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  qexists `update_var (STRCAT p x) (f v1 v2) t` >>
  conj_tac >- simp[exec_pure2_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

(* Reuse the common constructor lifting; internal returns are deliberately
   outside the ordinary-step interface. *)
Definition inline_ordinary_result_def:
  inline_ordinary_result R r q <=>
    lift_result R R R r q /\ (!ret st. r <> IntRet ret st)
End

Theorem inline_ordinary_result_cases[simp]:
  (inline_ordinary_result R (OK s) q <=> ?t. q = OK t /\ R s t) /\
  (inline_ordinary_result R (Halt s) q <=> ?t. q = Halt t /\ R s t) /\
  (inline_ordinary_result R (Abort a s) q <=> ?t. q = Abort a t /\ R s t) /\
  (inline_ordinary_result R (Error e) q <=> ?e'. q = Error e') /\
  (inline_ordinary_result R (IntRet ret s) q <=> F)
Proof
  Cases_on `q` >> simp[inline_ordinary_result_def, stateEquivTheory.lift_result_def] >>
  metis_tac[]
QED

Theorem inline_opaque_frame_shared_effect:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  inline_shared_frame s' = inline_shared_frame t' /\
  s'.vs_vars = s.vs_vars /\ t'.vs_vars = t.vs_vars ==>
  inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def, lookup_var_def]
QED

Theorem inline_opaque_frame_writes_establish:
  !pairs ren V opaque saved P s t.
    inline_opaque_frame_rel ren V opaque saved P s t /\
    (!u v. u IN V UNION set (MAP FST pairs) /\
           v IN V UNION set (MAP FST pairs) ==> (ren u = ren v <=> u = v)) /\
    EVERY (\p. ren (FST p) NOTIN P) pairs ==>
    inline_opaque_frame_rel ren (V UNION set (MAP FST pairs)) opaque saved P
      (FOLDL (\s (x,w). update_var x w s) s pairs)
      (FOLDL (\t (x,w). update_var (ren x) w t) t pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  rpt strip_tac >>
  `V UNION (h0 INSERT set (MAP FST pairs)) =
    (h0 INSERT V) UNION set (MAP FST pairs)` by SET_TAC[] >>
  pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >> conj_tac
  >- metis_tac[] >>
  irule inline_opaque_frame_write_establish >> simp[] >> metis_tac[]
QED

Theorem inline_pure1_clone_frame:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_pure1 f inst s = OK s' ==>
  ?t'. exec_pure1 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >> gvs[exec_pure1_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  qexists `update_var (STRCAT p x) (f v) t` >>
  conj_tac >- simp[exec_pure1_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_pure3_clone_frame:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_pure3 f inst s = OK s' ==>
  ?t'. exec_pure3 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >> gvs[exec_pure3_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  qexists `update_var (STRCAT p x) (f v1 v2 v3) t` >>
  conj_tac >- simp[exec_pure3_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_read0_clone_frame:
  inst.inst_outputs = [x] /\
  (!s t. inline_shared_frame s = inline_shared_frame t ==> f s = f t) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_read0 f inst s = OK s' ==>
  ?t'. exec_read0 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  `f s = f t` by metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  gvs[exec_read0_def] >>
  qexists `update_var (STRCAT p x) (f t) t` >>
  conj_tac >- simp[exec_read0_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_read1_clone_frame:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  (!w s t. inline_shared_frame s = inline_shared_frame t ==> f w s = f w t) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_read1 f inst s = OK s' ==>
  ?t'. exec_read1 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >> gvs[exec_read1_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  `f v s = f v t` by metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  qexists `update_var (STRCAT p x) (f v t) t` >>
  conj_tac >- simp[exec_read1_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_write2_clone_frame:
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  (!a b s t. inline_shared_frame s = inline_shared_frame t ==>
    inline_shared_frame (f a b s) = inline_shared_frame (f a b t)) /\
  (!a b s. (f a b s).vs_vars = s.vs_vars) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  exec_write2 f inst s = OK s' ==>
  ?t'. exec_write2 f (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  rpt strip_tac >> gvs[exec_write2_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  qexists `f v1 v2 t` >>
  conj_tac >- simp[exec_write2_def, clone_instruction_def] >>
  irule inline_opaque_frame_shared_effect >> conj_tac
  >- metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  qexistsl [`s`, `t`] >> simp[]
QED

Theorem inline_shared_frame_mstore:
  inline_shared_frame (mstore offset w s) = mstore offset w (inline_shared_frame s)
Proof
  simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def, mstore_def]
QED

Theorem inline_mstore_clone_frame:
  inst.inst_opcode = MSTORE /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst fuel' ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, Once step_inst_base_def] >>
  `?t'. exec_write2 (\addr val s. mstore (w2n addr) val s)
      (clone_instruction p labels inst) t = OK t' /\
      inline_opaque_frame_rel ren V opaque saved P s' t'` suffices_by
    (strip_tac >> qexists `t'` >> simp[step_inst_non_invoke,
       Once step_inst_base_def, clone_instruction_def] >>
     gvs[clone_instruction_def]) >>
  irule inline_write2_clone_frame >> conj_tac
  >- simp[inline_shared_frame_mstore] >>
  conj_tac >- simp[mstore_def] >>
  qexists `s` >> simp[]
QED

Theorem inline_shared_frame_gas_readings[simp]:
  (inline_shared_frame s).vs_gas_readings = s.vs_gas_readings /\
  inline_shared_frame (s with vs_gas_readings := gs) =
    (inline_shared_frame s) with vs_gas_readings := gs
Proof
  simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED

Theorem inline_opaque_frame_gas_readings:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  s.vs_gas_readings = t.vs_gas_readings /\
  inline_opaque_frame_rel ren V opaque saved P
    (s with vs_gas_readings := gs) (t with vs_gas_readings := gs)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def, lookup_var_def] >>
  metis_tac[inline_shared_frame_gas_readings]
QED

Theorem inline_gas_clone_frame:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ exec_gas inst s = OK s' ==>
  ?t'. exec_gas (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[inline_opaque_frame_gas_readings] >>
  Cases_on `t.vs_gas_readings`
  >- (gvs[exec_gas_def, clone_instruction_def] >>
      qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
      irule inline_opaque_frame_write_establish >> simp[]) >>
  gvs[exec_gas_def, clone_instruction_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[] >>
  metis_tac[inline_opaque_frame_gas_readings]
QED

Theorem inline_opaque_frame_observations:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  s.vs_halted = t.vs_halted /\ s.vs_returndata = t.vs_returndata /\
  s.vs_memory = t.vs_memory /\ s.vs_accounts = t.vs_accounts /\
  s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    venom_state_component_equality]
QED

Theorem inline_pure2_clone_result:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_pure2 f inst s) (exec_pure2 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_pure2 f inst s`
  >- (simp[] >> irule inline_pure2_clone_frame >> simp[] >> qexists `s` >> simp[])
  >- gvs[exec_pure2_def, AllCaseEqs()]
  >- gvs[exec_pure2_def, AllCaseEqs()]
  >- gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs(), clone_instruction_def, exec_pure2_def]
QED

Theorem inline_writes_control:
  !pairs s.
    (FOLDL (\s (x,w). update_var x w s) s pairs).vs_current_bb = s.vs_current_bb /\
    (FOLDL (\s (x,w). update_var x w s) s pairs).vs_prev_bb = s.vs_prev_bb /\
    (FOLDL (\s (x,w). update_var x w s) s pairs).vs_inst_idx = s.vs_inst_idx /\
    (FOLDL (\s (x,w). update_var x w s) s pairs).vs_halted = s.vs_halted
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[update_var_def]
QED

(* Terminal probes for the result lifting: observable equality does not
   require equal source and target control/bookkeeping fields. *)
Theorem inline_ordinary_stop_probe:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx (inst with inst_opcode := STOP) s)
    (step_inst fuel' ctx' (inst with inst_opcode := STOP) t)
Proof
  simp[step_inst_non_invoke, step_inst_base_def] >> rpt strip_tac >>
  irule inline_opaque_frame_shared_effect >> simp[halt_state_def] >>
  conj_tac
  >- (gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
        inline_shared_frame_def, stateFrameTheory.execution_frame_def,
        venom_state_component_equality]) >>
  qexistsl [`s`, `t`] >> simp[]
QED

Theorem inline_ordinary_abort_probe:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx (inst with <| inst_opcode := ASSERT;
       inst_operands := [Lit 0w] |>) s)
    (step_inst fuel' ctx' (inst with <| inst_opcode := ASSERT;
       inst_operands := [Lit 0w] |>) t)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def] >>
  rpt strip_tac >> irule inline_opaque_frame_shared_effect >>
  simp[revert_state_def, set_returndata_def] >> conj_tac
  >- (gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
        inline_shared_frame_def, stateFrameTheory.execution_frame_def,
        venom_state_component_equality]) >>
  qexistsl [`s`, `t`] >> simp[]
QED
