(* Operational boundaries for the actual clone/rewrite pipeline. *)
Theory functionInlinerOperational
Ancestors
  functionInlinerFrame functionInlinerOpacity functionInlinerNamespace
  functionInlinerDefs venomExecSemantics venomState venomInst venomWf list rich_list
  venomInstProofs1

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
  param_idx < LENGTH args /\ eval_operand (EL param_idx args) t = SOME w /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  rewrite_inline_inst args outs ret (clone_instruction p labels inst) param_idx =
    ([(clone_instruction p labels inst) with
      <| inst_opcode := ASSIGN; inst_operands := [EL param_idx args] |>], param_idx + 1) /\
  ?s' t'. step_inst fuel ctx inst s = OK s' /\
    step_inst fuel ctx'
      ((clone_instruction p labels inst) with
        <| inst_opcode := ASSIGN; inst_operands := [EL param_idx args] |>) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def] >>
  qexistsl [`update_var x s.vs_return_pc_token s`,
    `update_var (STRCAT p x) w t`] >>
  conj_tac >- (irule inline_token_step >> simp[]) >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, clone_instruction_def,
      eval_operands_def, eval_operand_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_token_unreplaced_frame:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [x] /\ x IN opaque /\
  LENGTH args <= param_idx /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  rewrite_inline_inst args outs ret (clone_instruction p labels inst) param_idx =
    ([clone_instruction p labels inst], param_idx) /\
  ?s' t'. step_inst fuel ctx inst s = OK s' /\
    step_inst fuel ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def] >>
  qexistsl [`update_var x s.vs_return_pc_token s`,
    `update_var (STRCAT p x) t.vs_return_pc_token t`] >>
  conj_tac >- (irule inline_token_step >> simp[]) >>
  conj_tac
  >- (irule inline_token_step >> simp[clone_instruction_def, clone_operand_def]) >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
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

Theorem inline_write2_success:
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  (!a b s t. inline_shared_frame s = inline_shared_frame t ==>
    inline_shared_frame (f a b s) = inline_shared_frame (f a b t)) /\
  (!a b s. (f a b s).vs_vars = s.vs_vars) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  exec_write2 f src s = OK s' ==>
  ?t'. exec_write2 f dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  rpt strip_tac >> gvs[exec_write2_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  qexists `f v1 v2 t` >>
  conj_tac
  >- (namedCases_on `dst.inst_operands` ["", "d1 ds"] >>
      gvs[eval_operands_def, AllCaseEqs()] >>
      namedCases_on `ds` ["", "d2 tail"] >>
      gvs[eval_operands_def, AllCaseEqs()] >>
      Cases_on `tail` >> gvs[eval_operands_def, AllCaseEqs(), exec_write2_def]) >>
  irule inline_opaque_frame_shared_effect >> conj_tac
  >- metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  qexistsl [`s`, `t`] >> simp[]
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
  strip_tac >> irule inline_write2_success >> simp[] >>
  qexistsl [`s`, `inst`] >> simp[clone_instruction_def]
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

(* Exhaustive semantic classes for the ordinary (non-rewritten) fragment. *)
Definition inline_pure1_opcode_def:
  inline_pure1_opcode opc <=> MEM opc [ISZERO; NOT]
End

Definition inline_pure2_opcode_def:
  inline_pure2_opcode opc <=>
    MEM opc [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp;
      EQ; LT; GT; SLT; SGT; AND; OR; XOR; SHL; SHR; SAR;
      SIGNEXTEND; BYTE; OFFSET]
End

Definition inline_pure3_opcode_def:
  inline_pure3_opcode opc <=> MEM opc [ADDMOD; MULMOD]
End

Definition inline_read0_opcode_def:
  inline_read0_opcode opc <=>
    MEM opc [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
      COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
      BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE]
End

Definition inline_read1_opcode_def:
  inline_read1_opcode opc <=>
    MEM opc [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; BALANCE;
      CALLDATALOAD; EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD]
End

Definition inline_effect_opcode_def:
  inline_effect_opcode opc <=>
    MEM opc [MSTORE; MSTORE8; MCOPY; SSTORE; TSTORE; ISTORE;
      CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY;
      LOG; SELFDESTRUCT; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
End

Definition inline_special_opcode_def:
  inline_special_opcode opc <=>
    MEM opc [GETFMP; INITIAL_FMP; BUMP; GAS; SHA3; NOP;
      STOP; RETURN; REVERT; SINK; ASSERT; ASSERT_UNREACHABLE; INVALID]
End

Definition inline_ordinary_opcode_def:
  inline_ordinary_opcode opc <=>
    ~MEM opc [INVOKE; PHI; ASSIGN; PARAM; FMP_PARAM; RETPC_PARAM;
      RET; RETFMP; JMP; JNZ; DJMP; ALLOCA; DALLOCA; DRET; SETFMP]
End

(* Only declared outputs may change in an ordinary successful step. *)
Definition inline_success_footprint_def:
  inline_success_footprint outs s t <=>
    t.vs_params = s.vs_params /\
    t.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    t.vs_return_pc_token = s.vs_return_pc_token /\
    t.vs_labels = s.vs_labels /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!x. ~MEM x outs ==> lookup_var x t = lookup_var x s)
End

Theorem inline_ordinary_OK_nonterminator:
  inline_ordinary_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK t ==>
  ~is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[inline_ordinary_opcode_def, is_terminator_def] >>
  fs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  fs[AllCaseEqs()]
QED

Theorem inline_ordinary_success_footprint:
  inline_ordinary_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK t ==>
  inline_success_footprint inst.inst_outputs s t
Proof
  rpt strip_tac >>
  drule_all inline_ordinary_OK_nonterminator >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[inline_ordinary_opcode_def] >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  drule_all step_inst_preserves_inst_idx >>
  simp[inline_success_footprint_def]
QED

Theorem inline_ordinary_opcode_coverage:
  inline_ordinary_opcode opc <=>
    inline_pure1_opcode opc \/ inline_pure2_opcode opc \/
    inline_pure3_opcode opc \/ inline_read0_opcode opc \/
    inline_read1_opcode opc \/ inline_effect_opcode opc \/
    inline_special_opcode opc
Proof
  Cases_on `opc` >> simp[inline_ordinary_opcode_def,
    inline_pure1_opcode_def, inline_pure2_opcode_def, inline_pure3_opcode_def,
    inline_read0_opcode_def, inline_read1_opcode_def,
    inline_effect_opcode_def, inline_special_opcode_def]
QED

Theorem inline_pure2_opcode_dispatch:
  inline_pure2_opcode inst.inst_opcode ==>
  ?f. (!s. step_inst_base inst s = exec_pure2 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_pure2 f (clone_instruction p labels inst) s)
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inline_pure2_opcode_def] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  metis_tac[]
QED

Theorem inline_pure2_opcode_clone_result:
  inline_pure2_opcode inst.inst_opcode /\ inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[inline_pure2_opcode_def]) >>
  drule inline_pure2_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke] >>
  irule inline_pure2_clone_result >> simp[]
QED

Theorem inline_pure1_opcode_dispatch:
  inline_pure1_opcode inst.inst_opcode ==>
  ?f. (!s. step_inst_base inst s = exec_pure1 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_pure1 f (clone_instruction p labels inst) s)
Proof
  Cases_on `inst.inst_opcode` >> simp[inline_pure1_opcode_def] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >> metis_tac[]
QED

Theorem inline_pure3_opcode_dispatch:
  inline_pure3_opcode inst.inst_opcode ==>
  ?f. (!s. step_inst_base inst s = exec_pure3 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_pure3 f (clone_instruction p labels inst) s)
Proof
  Cases_on `inst.inst_opcode` >> simp[inline_pure3_opcode_def] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >> metis_tac[]
QED

Theorem inline_read0_opcode_dispatch:
  inline_read0_opcode inst.inst_opcode ==>
  ?f. (!s. step_inst_base inst s = exec_read0 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_read0 f (clone_instruction p labels inst) s) /\
    (!s. f (inline_shared_frame s) = f s)
Proof
  Cases_on `inst.inst_opcode` >> simp[inline_read0_opcode_def] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  qmatch_goalsub_abbrev_tac `exec_read0 reader inst` >>
  qexists `reader` >>
  simp[Abbr `reader`, inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED

Theorem inline_read1_opcode_dispatch:
  inline_read1_opcode inst.inst_opcode ==>
  ?f. (!s. step_inst_base inst s = exec_read1 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_read1 f (clone_instruction p labels inst) s) /\
    (!w s. f w (inline_shared_frame s) = f w s)
Proof
  Cases_on `inst.inst_opcode` >> simp[inline_read1_opcode_def] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  qmatch_goalsub_abbrev_tac `exec_read1 reader inst` >>
  qexists `reader` >>
  simp[Abbr `reader`, inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem inline_pure13_opcode_clone_frame:
  (inline_pure1_opcode inst.inst_opcode \/ inline_pure3_opcode inst.inst_opcode) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst fuel' ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[inline_pure1_opcode_def, inline_pure3_opcode_def]) >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  gvs[step_inst_non_invoke] >>
  Cases_on `inline_pure1_opcode inst.inst_opcode`
  >- (drule inline_pure1_opcode_dispatch >>
      disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
      gvs[] >> irule inline_pure1_clone_frame >> simp[] >>
      qexists `s` >> simp[]) >>
  gvs[] >> drule inline_pure3_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  gvs[] >> irule inline_pure3_clone_frame >> simp[] >>
  qexists `s` >> simp[]
QED

Theorem inline_read_opcode_clone_frame:
  (inline_read0_opcode inst.inst_opcode \/ inline_read1_opcode inst.inst_opcode) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst fuel' ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[inline_read0_opcode_def, inline_read1_opcode_def]) >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  gvs[step_inst_non_invoke] >>
  Cases_on `inline_read0_opcode inst.inst_opcode`
  >- (drule inline_read0_opcode_dispatch >>
      disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
      gvs[] >> irule inline_read0_clone_frame >>
      metis_tac[]) >>
  gvs[] >> drule inline_read1_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  gvs[] >> irule inline_read1_clone_frame >>
  metis_tac[]
QED

Theorem inline_shared_frame_requests:
  venom_call_request (inline_shared_frame s) addr value ao az static =
    venom_call_request s addr value ao az static /\
  venom_create_request (inline_shared_frame s) value off sz salt =
    venom_create_request s value off sz salt
Proof
  simp[venomCallOracleDefsTheory.venom_call_request_def,
    venomCallOracleDefsTheory.venom_create_request_def,
    read_memory_def, inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED

Theorem inline_shared_frame_consume_call:
  consume_call_outcome rq ro rz (inline_shared_frame s) =
    (FST (consume_call_outcome rq ro rz s),
     inline_shared_frame (SND (consume_call_outcome rq ro rz s)))
Proof
  simp[venomCallOracleDefsTheory.consume_call_outcome_eq,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    write_memory_with_expansion_def]
QED

Theorem inline_shared_frame_consume_create:
  consume_create_outcome rq (inline_shared_frame s) =
    (FST (consume_create_outcome rq s),
     inline_shared_frame (SND (consume_create_outcome rq s)))
Proof
  simp[venomCallOracleDefsTheory.consume_create_outcome_eq,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED

Theorem inline_opaque_frame_consume_call:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  FST (consume_call_outcome rq ro rz s) = FST (consume_call_outcome rq ro rz t) /\
  inline_opaque_frame_rel ren V opaque saved P
    (SND (consume_call_outcome rq ro rz s)) (SND (consume_call_outcome rq ro rz t))
Proof
  strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `consume_call_outcome rq ro rz (inline_shared_frame s) =
   consume_call_outcome rq ro rz (inline_shared_frame t)` by simp[] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[inline_shared_frame_consume_call, pairTheory.PAIR_EQ] >> strip_tac >>
  asm_rewrite_tac[] >> irule inline_opaque_frame_shared_effect >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl [`s`, `t`] >> simp[venomCallOracleDefsTheory.consume_call_outcome_eq]
QED

Theorem inline_ext_call_success:
  inst.inst_outputs = [x] /\ dst.inst_outputs = [ren x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  exec_ext_call inst s gas addr value ao az ro rz static = OK s' ==>
  ?t'. exec_ext_call dst t
      gas addr value ao az ro rz static = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  `venom_call_request s addr value ao az static =
    venom_call_request t addr value ao az static` by
    metis_tac[inline_shared_frame_requests, inline_opaque_frame_rel_def,
      inline_frame_rel_def] >>
  drule inline_opaque_frame_consume_call >>
  disch_then (qspecl_then [`w2n rz`,
    `venom_call_request s addr value ao az static`, `w2n ro`] strip_assume_tac) >>
  gvs[exec_ext_call_def] >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_ext_call_clone_frame:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\
  exec_ext_call inst s gas addr value ao az ro rz static = OK s' ==>
  ?t'. exec_ext_call (clone_instruction p labels inst) t
      gas addr value ao az ro rz static = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >> irule inline_ext_call_success >> simp[clone_instruction_def] >>
  metis_tac[]
QED

Theorem inline_opaque_frame_consume_create:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  FST (consume_create_outcome rq s) = FST (consume_create_outcome rq t) /\
  inline_opaque_frame_rel ren V opaque saved P
    (SND (consume_create_outcome rq s)) (SND (consume_create_outcome rq t))
Proof
  strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `consume_create_outcome rq (inline_shared_frame s) =
   consume_create_outcome rq (inline_shared_frame t)` by simp[] >>
  pop_assum mp_tac >>
  pure_rewrite_tac[inline_shared_frame_consume_create, pairTheory.PAIR_EQ] >> strip_tac >>
  asm_rewrite_tac[] >> irule inline_opaque_frame_shared_effect >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl [`s`, `t`] >> simp[venomCallOracleDefsTheory.consume_create_outcome_eq]
QED

Theorem inline_create_success:
  inst.inst_outputs = [x] /\ dst.inst_outputs = [ren x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  exec_create inst s value off sz salt = OK s' ==>
  ?t'. exec_create dst t value off sz salt = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  `venom_create_request s value off sz salt =
    venom_create_request t value off sz salt` by
    metis_tac[inline_shared_frame_requests, inline_opaque_frame_rel_def,
      inline_frame_rel_def] >>
  drule inline_opaque_frame_consume_create >>
  disch_then (qspec_then `venom_create_request s value off sz salt` strip_assume_tac) >>
  gvs[exec_create_def, AllCaseEqs()] >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_create_clone_frame:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\
  exec_create inst s value off sz salt = OK s' ==>
  ?t'. exec_create (clone_instruction p labels inst) t value off sz salt = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >> irule inline_create_success >> simp[clone_instruction_def] >>
  metis_tac[]
QED

Theorem inline_shared_frame_delegate_state:
  make_venom_delegatecall_state (inline_shared_frame s) target gas data code static =
    make_venom_delegatecall_state s target gas data code static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def]
QED

Theorem inline_extract_result_frame:
  extract_venom_result (inline_shared_frame s) out ro rz rr =
    OPTION_MAP (\(w,t). (w, inline_shared_frame t))
      (extract_venom_result s out ro rz rr)
Proof
  namedCases_on `rr` ["", "pair"] >> simp[extract_venom_result_def] >>
  PairCases_on `pair` >> simp[] >>
  Cases_on `pair1.contexts` >> simp[] >>
  rename1 `head::tail` >> Cases_on `tail` >> simp[] >>
  PairCases_on `head` >>
  simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    write_memory_with_expansion_def] >>
  pairarg_tac >> simp[]
QED

Theorem inline_extract_result_transport:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  extract_venom_result s out ro rz rr = SOME (w,s') ==>
  ?t'. extract_venom_result t out ro rz rr = SOME (w,t') /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  rpt strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `extract_venom_result (inline_shared_frame t) out ro rz rr =
    SOME (w,inline_shared_frame s')` by
    (qpat_assum `inline_shared_frame s = inline_shared_frame t`
       (fn th => rewrite_tac[GSYM th]) >>
     simp[inline_extract_result_frame]) >>
  gvs[inline_extract_result_frame, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  irule inline_opaque_frame_shared_effect >>
  metis_tac[venomExecProofsTheory.extract_venom_result_preserves_vars]
QED

Theorem inline_delegatecall_success:
  inst.inst_outputs = [x] /\ dst.inst_outputs = [ren x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  exec_delegatecall inst s gas addr ao az ro rz = OK s' ==>
  ?t'. exec_delegatecall dst t
      gas addr ao az ro rz = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  rpt strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_accounts = t.vs_accounts /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao) (w2n az) t` by
    (gvs[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality, read_memory_def]) >>
  `!target gas data code static.
    make_venom_delegatecall_state s target gas data code static =
      make_venom_delegatecall_state t target gas data code static` by
    metis_tac[inline_shared_frame_delegate_state] >>
  gvs[exec_delegatecall_def, AllCaseEqs()] >>
  drule_all inline_extract_result_transport >> strip_tac >>
  simp[exec_delegatecall_def] >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_delegatecall_clone_frame:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\
  exec_delegatecall inst s gas addr ao az ro rz = OK s' ==>
  ?t'. exec_delegatecall (clone_instruction p labels inst) t
      gas addr ao az ro rz = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >> irule inline_delegatecall_success >> simp[clone_instruction_def] >>
  metis_tac[]
QED

Theorem inline_write2_clone_result:
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  (!a b s t. inline_shared_frame s = inline_shared_frame t ==>
    inline_shared_frame (f a b s) = inline_shared_frame (f a b t)) /\
  (!a b s. (f a b s).vs_vars = s.vs_vars) /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (exec_write2 f inst s) (exec_write2 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_write2 f inst s`
  >- (simp[] >> irule inline_write2_clone_frame >> metis_tac[])
  >- gvs[exec_write2_def, AllCaseEqs()]
  >- gvs[exec_write2_def, AllCaseEqs()]
  >- gvs[exec_write2_def, AllCaseEqs()] >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs(), clone_instruction_def, exec_write2_def]
QED

Theorem inline_write2_opcode_fields:
  MEM opc [MSTORE; MSTORE8] ==>
  ?f. (!inst s. inst.inst_opcode = opc ==>
      step_inst_base inst s = exec_write2 f inst s) /\
    (!a b s. inline_shared_frame (f a b s) = f a b (inline_shared_frame s)) /\
    (!a b s. (f a b s).vs_vars = s.vs_vars)
Proof
  Cases_on `opc` >> simp[]
  >- (qexists `\a b s. mstore (w2n a) b s` >>
      simp[step_inst_base_opcode_eqs, inline_shared_frame_def,
        stateFrameTheory.execution_frame_def, mstore_def]) >>
  qexists `\a b s. mstore8 (w2n a) b s` >>
  simp[step_inst_base_opcode_eqs, inline_shared_frame_def,
    stateFrameTheory.execution_frame_def, mstore8_def]
QED

Theorem inline_write2_opcode_success:
  MEM src.inst_opcode [MSTORE; MSTORE8] /\ dst.inst_opcode = src.inst_opcode /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  strip_tac >> drule inline_write2_opcode_fields >> strip_tac >>
  `src.inst_opcode <> INVOKE /\ dst.inst_opcode <> INVOKE` by gvs[] >>
  gvs[step_inst_non_invoke] >> irule inline_write2_success >> simp[] >>
  qexistsl [`s`, `src`] >> simp[] >> metis_tac[]
QED

Theorem inline_write2_opcode_dispatch:
  MEM inst.inst_opcode [MSTORE; MSTORE8] ==>
  ?f. (!s. step_inst_base inst s = exec_write2 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
      exec_write2 f (clone_instruction p labels inst) s) /\
    (!a b s. inline_shared_frame (f a b s) = f a b (inline_shared_frame s)) /\
    (!a b s. (f a b s).vs_vars = s.vs_vars)
Proof
  strip_tac >> drule inline_write2_opcode_fields >> strip_tac >>
  qexists `f` >> simp[clone_instruction_def]
QED

Theorem inline_write2_opcode_clone_result:
  MEM inst.inst_opcode [MSTORE; MSTORE8] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  drule inline_write2_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  simp[step_inst_non_invoke] >>
  irule inline_write2_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_pure1_clone_result:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_pure1 f inst s) (exec_pure1 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_pure1 f inst s`
  >- (simp[] >> irule inline_pure1_clone_frame >> simp[] >> qexists `s` >> simp[])
  >- gvs[exec_pure1_def, AllCaseEqs()]
  >- gvs[exec_pure1_def, AllCaseEqs()]
  >- gvs[exec_pure1_def, AllCaseEqs()] >>
  gvs[exec_pure1_def, AllCaseEqs()] >>
  gvs[eval_operands_def, AllCaseEqs(), clone_instruction_def, exec_pure1_def]
QED

Theorem inline_pure3_clone_result:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_pure3 f inst s) (exec_pure3 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_pure3 f inst s`
  >- (simp[] >> irule inline_pure3_clone_frame >> simp[] >> qexists `s` >> simp[])
  >- gvs[exec_pure3_def, AllCaseEqs()]
  >- gvs[exec_pure3_def, AllCaseEqs()]
  >- gvs[exec_pure3_def, AllCaseEqs()] >>
  gvs[exec_pure3_def, AllCaseEqs()] >>
  gvs[clone_instruction_def] >>
  gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem inline_read0_clone_result:
  inst.inst_outputs = [x] /\
  (!s t. inline_shared_frame s = inline_shared_frame t ==> f s = f t) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_read0 f inst s) (exec_read0 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_read0 f inst s`
  >- (simp[] >> irule inline_read0_clone_frame >> metis_tac[])
  >- gvs[exec_read0_def]
  >- gvs[exec_read0_def]
  >- gvs[exec_read0_def] >>
  gvs[exec_read0_def]
QED

Theorem inline_read1_clone_result:
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  (!w s t. inline_shared_frame s = inline_shared_frame t ==> f w s = f w t) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_read1 f inst s) (exec_read1 f (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >> Cases_on `exec_read1 f inst s`
  >- (simp[] >> irule inline_read1_clone_frame >> metis_tac[])
  >- gvs[exec_read1_def, AllCaseEqs()]
  >- gvs[exec_read1_def, AllCaseEqs()]
  >- gvs[exec_read1_def, AllCaseEqs()] >>
  gvs[exec_read1_def, AllCaseEqs()] >>
  gvs[clone_instruction_def] >> gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem inline_pure13_opcode_clone_result:
  (inline_pure1_opcode inst.inst_opcode \/ inline_pure3_opcode inst.inst_opcode) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    gvs[inline_pure1_opcode_def, inline_pure3_opcode_def] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inline_pure1_opcode inst.inst_opcode`
  >- (drule inline_pure1_opcode_dispatch >>
      disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
      simp[] >> irule inline_pure1_clone_result >> simp[]) >>
  gvs[] >> drule inline_pure3_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  simp[] >> irule inline_pure3_clone_result >> simp[]
QED

Theorem inline_read_opcode_clone_result:
  (inline_read0_opcode inst.inst_opcode \/ inline_read1_opcode inst.inst_opcode) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    gvs[inline_read0_opcode_def, inline_read1_opcode_def] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inline_read0_opcode inst.inst_opcode`
  >- (drule inline_read0_opcode_dispatch >>
      disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
      simp[] >> irule inline_read0_clone_result >> simp[] >> metis_tac[]) >>
  gvs[] >> drule inline_read1_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  simp[] >> irule inline_read1_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_opaque_frame_exceptional_halt:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (halt_state (set_returndata [] s)) (halt_state (set_returndata [] t))
Proof
  rpt strip_tac >> irule inline_opaque_frame_shared_effect >>
  simp[halt_state_def, set_returndata_def] >> conj_tac
  >- gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
       inline_shared_frame_def, stateFrameTheory.execution_frame_def,
       venom_state_component_equality] >>
  qexistsl [`s`, `t`] >> simp[]
QED

Theorem inline_storage_opcode_fields:
  MEM opc [SSTORE; TSTORE] ==>
  ?f. (!inst s. inst.inst_opcode = opc ==> step_inst_base inst s =
       if s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)
       then Abort ExHalt_abort (halt_state (set_returndata [] s))
       else exec_write2 f inst s) /\
    (!a b s. inline_shared_frame (f a b s) = f a b (inline_shared_frame s)) /\
    (!a b s. (f a b s).vs_vars = s.vs_vars)
Proof
  Cases_on `opc` >> simp[]
  >- (qexists `\a b s. sstore a b s` >>
      simp[step_inst_base_opcode_eqs, inline_shared_frame_def,
        stateFrameTheory.execution_frame_def, sstore_def, contract_storage_def]) >>
  qexists `\a b s. tstore a b s` >>
  simp[step_inst_base_opcode_eqs, inline_shared_frame_def,
    stateFrameTheory.execution_frame_def, tstore_def, contract_transient_def]
QED

Theorem inline_storage_opcode_dispatch:
  MEM inst.inst_opcode [SSTORE; TSTORE] ==>
  ?f. (!s. step_inst_base inst s =
       if s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)
       then Abort ExHalt_abort (halt_state (set_returndata [] s))
       else exec_write2 f inst s) /\
    (!s. step_inst_base (clone_instruction p labels inst) s =
       if s.vs_call_ctx.cc_static /\
          IS_SOME (eval_operands (MAP (clone_operand p labels) inst.inst_operands) s)
       then Abort ExHalt_abort (halt_state (set_returndata [] s))
       else exec_write2 f (clone_instruction p labels inst) s) /\
    (!a b s. inline_shared_frame (f a b s) = f a b (inline_shared_frame s)) /\
    (!a b s. (f a b s).vs_vars = s.vs_vars)
Proof
  strip_tac >> drule inline_storage_opcode_fields >> strip_tac >>
  qexists `f` >> simp[clone_instruction_def]
QED

Theorem inline_storage_opcode_success:
  MEM src.inst_opcode [SSTORE; TSTORE] /\
  dst.inst_opcode = src.inst_opcode /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst fuel' ctx' dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  strip_tac >>
  `src.inst_opcode <> INVOKE /\ dst.inst_opcode <> INVOKE` by gvs[] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  drule inline_storage_opcode_fields >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >>
  IF_CASES_TAC >- simp[] >> strip_tac >>
  `~t.vs_call_ctx.cc_static` by
    (gvs[exec_write2_def, AllCaseEqs(), eval_operands_def]) >>
  simp[] >> irule inline_write2_success >> simp[] >>
  qexistsl [`s`, `src`] >> simp[] >>
  metis_tac[]
QED

Theorem inline_storage_opcode_clone_result:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  drule inline_storage_opcode_dispatch >>
  disch_then (qspecl_then [`p`, `labels`] strip_assume_tac) >>
  simp[step_inst_non_invoke] >>
  Cases_on `t.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)`
  >- simp[inline_opaque_frame_exceptional_halt] >>
  simp[] >> irule inline_write2_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_simple_opcode_clone_result:
  MEM inst.inst_opcode [NOP; STOP; SINK; INVALID] /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      halt_state_def, set_returndata_def, lookup_var_def, venom_state_component_equality]
QED

Theorem inline_special_read0_success:
  MEM src.inst_opcode [GETFMP; INITIAL_FMP; GAS] /\
  src.inst_operands = [] /\ dst.inst_operands = [] /\
  src.inst_outputs = [x] /\ dst.inst_outputs = [ren x] /\
  dst.inst_opcode = src.inst_opcode /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp /\ s.vs_initial_fmp = t.vs_initial_fmp` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[inline_opaque_frame_gas_readings] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]
  >- (irule inline_opaque_frame_write_establish >> simp[])
  >- (irule inline_opaque_frame_write_establish >> simp[]) >>
  Cases_on `t.vs_gas_readings` >> gvs[exec_gas_def] >>
  irule inline_opaque_frame_write_establish >> simp[] >>
  metis_tac[inline_opaque_frame_gas_readings]
QED

Theorem inline_fmp_read_clone_result:
  MEM inst.inst_opcode [GETFMP; INITIAL_FMP] /\
  inst.inst_operands = [] /\ inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `s.vs_fmp = t.vs_fmp /\ s.vs_initial_fmp = t.vs_initial_fmp` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_bump_success:
  src.inst_opcode = BUMP /\ dst.inst_opcode = BUMP /\
  LENGTH src.inst_operands = 2 /\ LENGTH dst.inst_operands = 2 /\
  src.inst_outputs = [x;y] /\ dst.inst_outputs = [ren x;ren y] /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!u v. u IN V UNION {x;y} /\ v IN V UNION {x;y} ==>
    (ren u = ren v <=> u = v)) /\ ren x NOTIN P /\ ren y NOTIN P /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren (V UNION {x;y}) opaque saved P s' t'
Proof
  strip_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute, step_inst_non_invoke,
    step_inst_base_opcode_eqs, eval_operands_def, AllCaseEqs()] >>
  `V UNION {x;y} = y INSERT (x INSERT V)` by SET_TAC[] >>
  pop_assum SUBST1_TAC >>
  irule inline_opaque_frame_write_establish >> simp[] >> conj_tac
  >- metis_tac[] >>
  metis_tac[inline_opaque_frame_write_establish]
QED

Theorem inline_bump_clone_result:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [a;b] /\
  inst.inst_outputs = [x;y] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!u v. u IN V UNION {x;y} /\ v IN V UNION {x;y} ==>
    (ren u = ren v <=> u = v)) /\
  ren x NOTIN P /\ ren y NOTIN P /\
  ren x = STRCAT p x /\ ren y = STRCAT p y ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (V UNION {x;y}) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke, clone_instruction_def, step_inst_base_opcode_eqs] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `ren y = STRCAT p y` (fn th => rewrite_tac[GSYM th]) >>
  `V UNION {x;y} = y INSERT (x INSERT V)` by SET_TAC[] >>
  pop_assum SUBST1_TAC >>
  irule inline_opaque_frame_write_establish >> simp[] >> conj_tac
  >- metis_tac[] >>
  metis_tac[inline_opaque_frame_write_establish]
QED

Theorem inline_simple_opcode_success:
  MEM src.inst_opcode [NOP; SINK; ASSERT; ASSERT_UNREACHABLE] /\
  inst_wf src /\ dst.inst_opcode = src.inst_opcode /\
  LENGTH dst.inst_operands = LENGTH src.inst_operands /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  strip_tac >>
  gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute,
    step_inst_non_invoke, step_inst_base_opcode_eqs,
    eval_operands_def, AllCaseEqs()]
QED

Theorem inline_assert_clone_result:
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  inst.inst_operands = [c] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  Cases_on `eval_operand c s` >> gvs[eval_operands_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  Cases_on `x = 0w` >> simp[] >>
  gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    halt_state_def, revert_state_def, set_returndata_def, lookup_var_def,
    venom_state_component_equality]
QED

Theorem inline_return_revert_clone_result:
  MEM inst.inst_opcode [RETURN; REVERT] /\
  inst.inst_operands = [a;b] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `(clone_instruction p labels inst).inst_opcode <> INVOKE` by
    simp[clone_instruction_def] >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[clone_instruction_def, step_inst_base_opcode_eqs] >>
  gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    halt_state_def, revert_state_def, set_returndata_def, lookup_var_def,
    venom_state_component_equality]
QED


Theorem inline_mcopy_eval_list:
  inst.inst_opcode = MCOPY /\ LENGTH inst.inst_operands = 3 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => OK (mcopy (w2n (EL 0 ws)) (w2n (EL 1 ws)) (w2n (EL 2 ws)) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[] >>
  Cases_on `eval_operand h'' s` >> simp[]
QED

Theorem inline_returndatacopy_eval_list:
  inst.inst_opcode = RETURNDATACOPY /\ LENGTH inst.inst_operands = 3 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws =>
        if w2n (EL 1 ws) + w2n (EL 2 ws) > LENGTH s.vs_returndata
        then Abort ExHalt_abort (halt_state (set_returndata [] s))
        else OK (write_memory_with_expansion (w2n (EL 0 ws))
          (TAKE (w2n (EL 2 ws)) (DROP (w2n (EL 1 ws)) s.vs_returndata)) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[] >>
  Cases_on `eval_operand h'' s` >> simp[]
QED

Theorem inline_shared_frame_bulk_memory:
  (inline_shared_frame (mcopy dst src sz s) =
    mcopy dst src sz (inline_shared_frame s)) /\
  (inline_shared_frame (write_memory_with_expansion dst bytes s) =
    write_memory_with_expansion dst bytes (inline_shared_frame s)) /\
  (mcopy dst src sz s).vs_vars = s.vs_vars /\
  (write_memory_with_expansion dst bytes s).vs_vars = s.vs_vars
Proof
  simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    mcopy_def, write_memory_with_expansion_def]
QED

Theorem inline_opaque_frame_mcopy:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (mcopy dst src sz s) (mcopy dst src sz t)
Proof
  strip_tac >> irule inline_opaque_frame_shared_effect >> conj_tac
  >- (simp[inline_shared_frame_bulk_memory] >>
      metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def]) >>
  qexistsl [`s`, `t`] >> simp[inline_shared_frame_bulk_memory]
QED

Theorem inline_opaque_frame_write_memory:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (write_memory_with_expansion dst bytes s)
    (write_memory_with_expansion dst bytes t)
Proof
  strip_tac >> irule inline_opaque_frame_shared_effect >> conj_tac
  >- (simp[inline_shared_frame_bulk_memory] >>
      metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def]) >>
  qexistsl [`s`, `t`] >> simp[inline_shared_frame_bulk_memory]
QED

Theorem inline_mcopy_atomic_clone_result:
  inst.inst_opcode = MCOPY /\ LENGTH inst.inst_operands = 3 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = MCOPY /\
    LENGTH (clone_instruction p labels inst).inst_operands = 3` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke, inline_mcopy_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[inline_opaque_frame_mcopy]
QED

Theorem inline_returndatacopy_atomic_clone_result:
  inst.inst_opcode = RETURNDATACOPY /\ LENGTH inst.inst_operands = 3 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = RETURNDATACOPY /\
    LENGTH (clone_instruction p labels inst).inst_operands = 3` by
    simp[clone_instruction_def] >>
  `s.vs_returndata = t.vs_returndata` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  simp[step_inst_non_invoke, inline_returndatacopy_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  IF_CASES_TAC >>
  simp[inline_opaque_frame_exceptional_halt, inline_opaque_frame_write_memory]
QED

Theorem inline_copy_data_eval_list:
  MEM inst.inst_opcode [CALLDATACOPY; DLOADBYTES; CODECOPY] /\
  LENGTH inst.inst_operands = 3 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => OK (write_memory_with_expansion (w2n (EL 0 ws))
        (TAKE (w2n (EL 2 ws)) (DROP (w2n (EL 1 ws))
          (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
           else if inst.inst_opcode = DLOADBYTES then s.vs_data_section
           else s.vs_code) ++ REPLICATE (w2n (EL 2 ws)) 0w)) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[] >> simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[] >>
  Cases_on `eval_operand h'' s` >> simp[]
QED

Theorem inline_copy_data_atomic_clone_result:
  MEM inst.inst_opcode [CALLDATACOPY; DLOADBYTES; CODECOPY] /\
  LENGTH inst.inst_operands = 3 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `MEM (clone_instruction p labels inst).inst_opcode
      [CALLDATACOPY; DLOADBYTES; CODECOPY] /\
    LENGTH (clone_instruction p labels inst).inst_operands = 3` by
    gvs[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_data_section = t.vs_data_section /\
   s.vs_code = t.vs_code` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `inst.inst_opcode <> INVOKE /\
   (clone_instruction p labels inst).inst_opcode <> INVOKE` by gvs[] >>
  simp[step_inst_non_invoke, inline_copy_data_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[inline_opaque_frame_write_memory]
QED

Theorem inline_extcodecopy_eval_list:
  inst.inst_opcode = EXTCODECOPY /\ LENGTH inst.inst_operands = 4 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => OK (write_memory_with_expansion (w2n (EL 1 ws))
        (TAKE (w2n (EL 3 ws)) (DROP (w2n (EL 2 ws))
          (lookup_account (w2w (EL 0 ws)) s.vs_accounts).code ++
          REPLICATE (w2n (EL 3 ws)) 0w)) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[] >>
  Cases_on `eval_operand h'' s` >> simp[] >>
  Cases_on `eval_operand h''' s` >> simp[]
QED

Theorem inline_extcodecopy_atomic_clone_result:
  inst.inst_opcode = EXTCODECOPY /\ LENGTH inst.inst_operands = 4 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = EXTCODECOPY /\
    LENGTH (clone_instruction p labels inst).inst_operands = 4` by
    simp[clone_instruction_def] >>
  `s.vs_accounts = t.vs_accounts` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  simp[step_inst_non_invoke, inline_extcodecopy_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[inline_opaque_frame_write_memory]
QED

Theorem inline_istore_eval_list:
  inst.inst_opcode = ISTORE /\ LENGTH inst.inst_operands = 2 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => OK (istore (w2n (EL 0 ws)) (EL 1 ws) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[]
QED

Theorem inline_shared_frame_istore:
  inline_shared_frame (istore off w s) = istore off w (inline_shared_frame s) /\
  (istore off w s).vs_vars = s.vs_vars
Proof
  simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    istore_def, mstore_def]
QED

Theorem inline_opaque_frame_istore:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (istore off w s) (istore off w t)
Proof
  strip_tac >> irule inline_opaque_frame_shared_effect >> conj_tac
  >- (simp[inline_shared_frame_istore] >>
      metis_tac[inline_opaque_frame_rel_def, inline_frame_rel_def]) >>
  qexistsl [`s`, `t`] >> simp[inline_shared_frame_istore]
QED

Theorem inline_istore_atomic_clone_result:
  inst.inst_opcode = ISTORE /\ LENGTH inst.inst_operands = 2 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = ISTORE /\
    LENGTH (clone_instruction p labels inst).inst_operands = 2` by
    simp[clone_instruction_def] >>
  simp[step_inst_non_invoke, inline_istore_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >>
  simp[inline_opaque_frame_istore]
QED

Theorem inline_bulk_memory_opcode_success:
  MEM src.inst_opcode
    [MCOPY; RETURNDATACOPY; CALLDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY; ISTORE] /\
  inst_wf src /\ dst.inst_opcode = src.inst_opcode /\
  LENGTH dst.inst_operands = LENGTH src.inst_operands /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst fuel' ctx' dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_data_section = t.vs_data_section /\
   s.vs_code = t.vs_code /\ s.vs_accounts = t.vs_accounts /\
   s.vs_returndata = t.vs_returndata` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  gvs[inst_wf_def] >>
  simp[step_inst_non_invoke, inline_mcopy_eval_list,
    inline_returndatacopy_eval_list, inline_copy_data_eval_list,
    inline_extcodecopy_eval_list, inline_istore_eval_list] >>
  Cases_on `eval_operands src.inst_operands s` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[inline_opaque_frame_mcopy, inline_opaque_frame_write_memory,
    inline_opaque_frame_istore]
QED

Theorem inline_opaque_frame_jump:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (jump_to dst s) (jump_to (lab dst) t)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    jump_to_def, lookup_var_def]
QED

Theorem inline_jump_control:
  t.vs_current_bb = lab s.vs_current_bb ==>
  (jump_to (lab dst) t).vs_current_bb = lab (jump_to dst s).vs_current_bb /\
  (jump_to (lab dst) t).vs_prev_bb =
    OPTION_MAP lab (jump_to dst s).vs_prev_bb /\
  (jump_to dst s).vs_inst_idx = 0 /\ (jump_to (lab dst) t).vs_inst_idx = 0
Proof
  simp[jump_to_def]
QED

Theorem inline_jmp_clone_step:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label dst] ==>
  step_inst fuel ctx inst s = OK (jump_to dst s) /\
  step_inst fuel' ctx' (clone_instruction p labels inst) t =
    OK (jump_to (if MEM dst labels then STRCAT p dst else dst) t)
Proof
  Cases_on `MEM dst labels` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    clone_instruction_def, clone_operand_def]
QED

Theorem inline_jnz_clone_step:
  inst.inst_opcode = JNZ /\ inst.inst_operands = [test; Label yes; Label no] /\
  eval_operand test s = SOME w /\
  eval_operand (clone_operand p labels test) t = SOME w ==>
  step_inst fuel ctx inst s = OK (jump_to (if w <> 0w then yes else no) s) /\
  step_inst fuel' ctx' (clone_instruction p labels inst) t =
    OK (jump_to (if MEM (if w <> 0w then yes else no) labels
      then STRCAT p (if w <> 0w then yes else no)
      else (if w <> 0w then yes else no)) t)
Proof
  strip_tac >> Cases_on `w = 0w` >>
  Cases_on `MEM yes labels` >> Cases_on `MEM no labels` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    clone_instruction_def, clone_operand_def]
QED

Theorem inline_djmp_clone_step:
  inst.inst_opcode = DJMP /\ inst.inst_operands = test::ops /\
  eval_operand test s = SOME w /\
  eval_operand (clone_operand p labels test) t = SOME w /\
  extract_labels ops = SOME dests /\ w2n w < LENGTH dests ==>
  step_inst fuel ctx inst s = OK (jump_to (EL (w2n w) dests) s) /\
  step_inst fuel' ctx' (clone_instruction p labels inst) t =
    OK (jump_to (if MEM (EL (w2n w) dests) labels
      then STRCAT p (EL (w2n w) dests) else EL (w2n w) dests) t)
Proof
  strip_tac >>
  `clone_operand p labels = inline_rename_operand (STRCAT p)
    (\l. if MEM l labels then STRCAT p l else l)` by
    simp[FUN_EQ_THM, clone_operand_inline_rename] >>
  `extract_labels (MAP (clone_operand p labels) ops) =
    SOME (MAP (\l. if MEM l labels then STRCAT p l else l) dests)` by
    simp[inline_rename_extract_labels] >>
  qpat_x_assum `clone_operand p labels = _` kall_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    clone_instruction_def, listTheory.EL_MAP]
QED

Theorem inline_ordinary_halt_observations:
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (Halt s) result /\ s.vs_halted ==>
  ?t. result = Halt t /\ t.vs_halted /\
    s.vs_returndata = t.vs_returndata /\ s.vs_memory = t.vs_memory /\
    s.vs_accounts = t.vs_accounts /\
    s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests
Proof
  simp[inline_ordinary_result_def] >> rpt strip_tac >>
  drule inline_opaque_frame_observations >> simp[]
QED

Theorem inline_ordinary_abort_observations:
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (Abort reason s) result /\ s.vs_halted ==>
  ?t. result = Abort reason t /\ t.vs_halted /\
    s.vs_returndata = t.vs_returndata /\ s.vs_memory = t.vs_memory /\
    s.vs_accounts = t.vs_accounts /\
    s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests
Proof
  simp[inline_ordinary_result_def] >> rpt strip_tac >>
  drule inline_opaque_frame_observations >> simp[]
QED

Theorem inline_gas_clone_result:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[inline_opaque_frame_gas_readings] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, clone_instruction_def] >>
  Cases_on `t.vs_gas_readings` >> simp[exec_gas_def] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[] >>
  metis_tac[inline_opaque_frame_gas_readings]
QED

Theorem inline_sha3_eval_list:
  inst.inst_opcode = SHA3 /\ LENGTH inst.inst_operands = 2 /\
  LENGTH inst.inst_outputs = 1 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => OK (update_var (HD inst.inst_outputs)
        (word_of_bytes T (0w:bytes32)
          (Keccak_256_w64 (TAKE (w2n (EL 1 ws))
            (DROP (w2n (EL 0 ws)) s.vs_memory ++ REPLICATE (w2n (EL 1 ws)) 0w)))) s)
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
  rename1 `inst.inst_operands = [a; b]` >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand b s` >> simp[]
QED

Theorem inline_sha3_success:
  src.inst_opcode = SHA3 /\ dst.inst_opcode = SHA3 /\
  LENGTH src.inst_operands = 2 /\ LENGTH dst.inst_operands = 2 /\
  src.inst_outputs = [x] /\ dst.inst_outputs = [ren x] /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >>
  `s.vs_memory = t.vs_memory` by metis_tac[inline_opaque_frame_observations] >>
  gvs[step_inst_non_invoke, inline_sha3_eval_list, AllCaseEqs()] >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_sha3_clone_result:
  inst.inst_opcode = SHA3 /\ LENGTH inst.inst_operands = 2 /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = SHA3 /\
    LENGTH (clone_instruction p labels inst).inst_operands = 2 /\
    (clone_instruction p labels inst).inst_outputs = [STRCAT p x]` by
    simp[clone_instruction_def] >>
  `s.vs_memory = t.vs_memory` by metis_tac[inline_opaque_frame_observations] >>
  simp[step_inst_non_invoke, inline_sha3_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  qpat_assum `ren x = STRCAT p x` (fn th => rewrite_tac[GSYM th]) >>
  irule inline_opaque_frame_write_establish >> simp[]
QED

Theorem inline_selfdestruct_eval_list:
  inst.inst_opcode = SELFDESTRUCT /\ LENGTH inst.inst_operands = 1 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "selfdestruct: undefined operand"
    | SOME ws =>
        if s.vs_call_ctx.cc_static then
          Abort ExHalt_abort (halt_state (set_returndata [] s))
        else
          let self = s.vs_call_ctx.cc_address;
              accts = s.vs_accounts;
              ben = w2w (HD ws);
              sa = lookup_account self accts;
              ba = lookup_account ben accts in
          Halt (halt_state (set_returndata [] (s with vs_accounts :=
            (\a. if a = self then sa with balance := 0
                 else if a = ben then ba with balance := ba.balance + sa.balance
                 else accts a))))
Proof
  strip_tac >> Cases_on `inst.inst_operands` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[]
QED

Theorem inline_opaque_frame_accounts:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (s with vs_accounts := accts) (t with vs_accounts := accts)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    lookup_var_def, venom_state_component_equality]
QED

Theorem inline_selfdestruct_clone_result:
  inst.inst_opcode = SELFDESTRUCT /\ LENGTH inst.inst_operands = 1 /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = SELFDESTRUCT /\
    LENGTH (clone_instruction p labels inst).inst_operands = 1` by
    simp[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_accounts = t.vs_accounts` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  simp[step_inst_non_invoke, inline_selfdestruct_eval_list] >>
  simp[clone_instruction_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  IF_CASES_TAC >> simp[inline_opaque_frame_exceptional_halt,
    inline_opaque_frame_accounts]
QED

Theorem inline_log_eval_list:
  inst.inst_opcode = LOG /\
  (?tc rest. inst.inst_operands = Lit tc :: rest /\ LENGTH rest = w2n tc + 2) ==>
  step_inst_base inst s =
    if s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)
    then Abort ExHalt_abort (halt_state (set_returndata [] s))
    else case eval_operands (REVERSE (TL inst.inst_operands)) s of
      NONE => Error "log: undefined operand"
    | SOME ws => OK (s with vs_logs := s.vs_logs ++
        [<| logger := w2w s.vs_call_ctx.cc_address;
            topics := DROP 2 ws;
            data := TAKE (w2n (EL 1 ws))
              (DROP (w2n (EL 0 ws)) s.vs_memory ++ REPLICATE (w2n (EL 1 ws)) 0w) |>])
Proof
  strip_tac >>
  `2 <= LENGTH (REVERSE rest)` by simp[] >>
  Cases_on `REVERSE rest` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[] >>
  Cases_on `eval_operands t' s` >> simp[]
QED

Theorem inline_opaque_frame_logs:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_opaque_frame_rel ren V opaque saved P
    (s with vs_logs := logs) (t with vs_logs := logs)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    inline_shared_frame_def, stateFrameTheory.execution_frame_def,
    lookup_var_def, venom_state_component_equality]
QED

Theorem inline_log_success:
  src.inst_opcode = LOG /\ dst.inst_opcode = LOG /\
  src.inst_operands = Lit tc :: ops /\ dst.inst_operands = Lit tc :: tops /\
  LENGTH ops = w2n tc + 2 /\ LENGTH tops = LENGTH ops /\
  (!vs. eval_operands (REVERSE ops) s = SOME vs ==>
    eval_operands (REVERSE tops) t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren V opaque saved P s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_memory = t.vs_memory /\
    s.vs_logs = t.vs_logs` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `IS_SOME (eval_operands src.inst_operands s) =
   IS_SOME (eval_operands (REVERSE ops) s)` by
    (simp[venomExecProofsTheory.eval_operands_IS_SOME_EVERY,
      listTheory.EVERY_MEM] >> eq_tac >> rpt strip_tac >>
      gvs[eval_operand_def]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, inline_log_eval_list] >>
  Cases_on `eval_operands (REVERSE ops) s` >> simp[] >>
  IF_CASES_TAC >- simp[] >> strip_tac >> gvs[] >>
  simp[inline_opaque_frame_logs]
QED

Theorem inline_log_clone_result:
  inst.inst_opcode = LOG /\
  (?tc rest. inst.inst_operands = Lit tc :: rest /\ LENGTH rest = w2n tc + 2) /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  eval_operands (MAP (clone_operand p labels) (REVERSE (TL inst.inst_operands))) t =
    eval_operands (REVERSE (TL inst.inst_operands)) s /\
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = LOG /\
    (?tc rest. (clone_instruction p labels inst).inst_operands = Lit tc :: rest /\
      LENGTH rest = w2n tc + 2)` by
    (simp[clone_instruction_def, clone_operand_def] >> metis_tac[]) >>
  qpat_x_assum `(clone_instruction p labels inst).inst_operands = _` mp_tac >>
  simp[clone_instruction_def, clone_operand_def] >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_memory = t.vs_memory /\
    s.vs_logs = t.vs_logs` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  simp[step_inst_non_invoke, inline_log_eval_list] >>
  `REVERSE (TL (clone_instruction p labels inst).inst_operands) =
    MAP (clone_operand p labels) (REVERSE (TL inst.inst_operands))` by
    simp[clone_instruction_def, listTheory.MAP_REVERSE] >>
  gvs[clone_instruction_def, clone_operand_def, listTheory.MAP_REVERSE] >>
  IF_CASES_TAC >- simp[inline_opaque_frame_exceptional_halt] >>
  Cases_on `eval_operands (REVERSE rest) s` >>
  simp[inline_opaque_frame_logs]
QED

Theorem inline_opaque_frame_restrict:
  inline_opaque_frame_rel ren vars_set opaque saved P s t /\ V SUBSET vars_set ==>
  inline_opaque_frame_rel ren V opaque saved P s t
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

Theorem inline_ext_call_clone_result:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_ext_call inst s gas addr value ao az ro rz static)
    (exec_ext_call (clone_instruction p labels inst) t gas addr value ao az ro rz static)
Proof
  strip_tac >> Cases_on `exec_ext_call inst s gas addr value ao az ro rz static`
  >- (simp[] >> irule inline_ext_call_clone_frame >> metis_tac[]) >>
  gvs[exec_ext_call_def, clone_instruction_def, AllCaseEqs()]
QED

Theorem inline_create_clone_result:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (exec_create inst s value off sz salt)
    (exec_create (clone_instruction p labels inst) t value off sz salt)
Proof
  strip_tac >> Cases_on `w2n sz > 2 * max_code_size`
  >- simp[exec_create_def, clone_instruction_def, inline_opaque_frame_exceptional_halt] >>
  Cases_on `exec_create inst s value off sz salt`
  >- (simp[] >> drule_all inline_create_clone_frame >>
      disch_then (qspec_then `labels` strip_assume_tac) >>
      qexists `t'` >> simp[] >> irule inline_opaque_frame_restrict >>
      qexists `x INSERT V` >> simp[pred_setTheory.SUBSET_DEF]) >>
  gvs[exec_create_def, clone_instruction_def, AllCaseEqs()]
QED

Theorem inline_extract_result_none:
  inline_opaque_frame_rel ren V opaque saved P s t ==>
  (extract_venom_result s out ro rz rr = NONE <=>
   extract_venom_result t out ro rz rr = NONE)
Proof
  strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `extract_venom_result (inline_shared_frame s) out ro rz rr =
   extract_venom_result (inline_shared_frame t) out ro rz rr` by simp[] >>
  gvs[inline_extract_result_frame] >>
  Cases_on `extract_venom_result s out ro rz rr` >>
  Cases_on `extract_venom_result t out ro rz rr` >> gvs[]
QED

Theorem inline_delegatecall_clone_result:
  inst.inst_outputs = [x] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (exec_delegatecall inst s gas addr ao az ro rz)
    (exec_delegatecall (clone_instruction p labels inst) t gas addr ao az ro rz)
Proof
  strip_tac >>
  `inline_shared_frame s = inline_shared_frame t` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_accounts = t.vs_accounts /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao) (w2n az) t` by
    (gvs[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality, read_memory_def]) >>
  `!target gas data code static.
    make_venom_delegatecall_state s target gas data code static =
      make_venom_delegatecall_state t target gas data code static` by
    metis_tac[inline_shared_frame_delegate_state] >>
  Cases_on `exec_delegatecall inst s gas addr ao az ro rz`
  >- (simp[] >> irule inline_delegatecall_clone_frame >> metis_tac[]) >>
  gvs[exec_delegatecall_def, AllCaseEqs()] >>
  simp[exec_delegatecall_def, clone_instruction_def] >>
  metis_tac[inline_extract_result_none]
QED

Theorem inline_call_eval_list:
  inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws =>
        if s.vs_call_ctx.cc_static /\ EL 2 ws <> 0w then
          Abort ExHalt_abort (halt_state (set_returndata [] s))
        else exec_ext_call inst s (EL 0 ws) (EL 1 ws) (EL 2 ws)
          (EL 3 ws) (EL 4 ws) (EL 5 ws) (EL 6 ws) s.vs_call_ctx.cc_static
Proof
  strip_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [a;b;c;d;e;f;g]` >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand b s` >> simp[] >>
  Cases_on `eval_operand c s` >> simp[] >>
  Cases_on `eval_operand d s` >> simp[] >>
  Cases_on `eval_operand e s` >> simp[] >>
  Cases_on `eval_operand f s` >> simp[] >>
  Cases_on `eval_operand g s` >> simp[]
QED

Theorem inline_call6_eval_list:
  MEM inst.inst_opcode [STATICCALL; DELEGATECALL] /\
  LENGTH inst.inst_operands = 6 ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => if inst.inst_opcode = STATICCALL then
        exec_ext_call inst s (EL 0 ws) (EL 1 ws) 0w
          (EL 2 ws) (EL 3 ws) (EL 4 ws) (EL 5 ws) T
      else exec_delegatecall inst s (EL 0 ws) (EL 1 ws)
          (EL 2 ws) (EL 3 ws) (EL 4 ws) (EL 5 ws)
Proof
  strip_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [a;b;c;d;e;f]` >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand b s` >> simp[] >>
  Cases_on `eval_operand c s` >> simp[] >>
  Cases_on `eval_operand d s` >> simp[] >>
  Cases_on `eval_operand e s` >> simp[] >>
  Cases_on `eval_operand f s` >> simp[]
QED

Theorem inline_create_eval_list:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  LENGTH inst.inst_operands = (if inst.inst_opcode = CREATE then 3 else 4) ==>
  step_inst_base inst s =
    if s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s) then
      Abort ExHalt_abort (halt_state (set_returndata [] s))
    else case eval_operands inst.inst_operands s of
      NONE => Error "undefined operand"
    | SOME ws => exec_create inst s (EL 0 ws) (EL 1 ws) (EL 2 ws)
        (if inst.inst_opcode = CREATE then NONE else SOME (EL 3 ws))
Proof
  strip_tac >> gvs[listTheory.LENGTH_EQ_NUM_compute]
  >- (rename1 `inst.inst_operands = [a;b;c]` >>
      simp[step_inst_base_opcode_eqs, eval_operands_def] >>
      Cases_on `eval_operand a s` >> simp[] >>
      Cases_on `eval_operand b s` >> simp[] >>
      Cases_on `eval_operand c s` >> simp[]) >>
  rename1 `inst.inst_operands = [a;b;c;d]` >>
  simp[step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand b s` >> simp[] >>
  Cases_on `eval_operand c s` >> simp[] >>
  Cases_on `eval_operand d s` >> simp[]
QED

Theorem inline_external_opcode_success:
  MEM src.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  inst_wf src /\ src.inst_outputs = [x] /\
  dst.inst_opcode = src.inst_opcode /\ dst.inst_outputs = [ren x] /\
  LENGTH dst.inst_operands = LENGTH src.inst_operands /\
  (!vs. eval_operands src.inst_operands s = SOME vs ==>
    eval_operands dst.inst_operands t = SOME vs) /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  step_inst fuel ctx src s = OK s' ==>
  ?t'. step_inst tfuel tctx dst t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  gvs[inst_wf_def] >>
  simp[step_inst_non_invoke, inline_call_eval_list,
    inline_call6_eval_list, inline_create_eval_list] >>
  Cases_on `eval_operands src.inst_operands s` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[inline_ext_call_success, inline_create_success, inline_delegatecall_success]
QED

Theorem inline_ordinary_frame_restrict:
  inline_ordinary_result (inline_opaque_frame_rel ren vars_set opaque saved P) r q /\
  V SUBSET vars_set ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P) r q
Proof
  Cases_on `r` >> simp[] >> metis_tac[inline_opaque_frame_restrict]
QED

Theorem inline_call_clone_success:
  inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7 /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand pref labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT pref x /\ step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst tfuel tctx (clone_instruction pref labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >> irule inline_external_opcode_success >>
  simp[clone_instruction_def] >>
  qexistsl [`ctx`, `fuel`, `s`, `inst`] >> simp[inst_wf_def]
QED

Theorem inline_call_clone_result:
  inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7 /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = CALL /\
    LENGTH (clone_instruction p labels inst).inst_operands = 7` by
    simp[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `(clone_instruction p labels inst).inst_operands =
    MAP (clone_operand p labels) inst.inst_operands` by simp[clone_instruction_def] >>
  simp[step_inst_non_invoke, inline_call_eval_list] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  IF_CASES_TAC >- simp[inline_opaque_frame_exceptional_halt] >>
  irule inline_ordinary_frame_restrict >>
  qexists `x INSERT V` >> simp[pred_setTheory.SUBSET_DEF] >>
  irule inline_ext_call_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_call6_clone_result:
  MEM inst.inst_opcode [STATICCALL; DELEGATECALL] /\
  LENGTH inst.inst_operands = 6 /\ inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `MEM (clone_instruction p labels inst).inst_opcode [STATICCALL; DELEGATECALL] /\
    LENGTH (clone_instruction p labels inst).inst_operands = 6` by
    gvs[clone_instruction_def] >>
  `(clone_instruction p labels inst).inst_operands =
    MAP (clone_operand p labels) inst.inst_operands /\
    (clone_instruction p labels inst).inst_opcode = inst.inst_opcode` by
    simp[clone_instruction_def] >>
  Cases_on `inst.inst_opcode = STATICCALL` >>
  gvs[] >> simp[step_inst_non_invoke, inline_call6_eval_list] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  metis_tac[inline_ext_call_clone_result, inline_delegatecall_clone_result]
QED

Theorem inline_create_opcode_clone_result:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  LENGTH inst.inst_operands = (if inst.inst_opcode = CREATE then 3 else 4) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P)
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `MEM (clone_instruction p labels inst).inst_opcode [CREATE; CREATE2] /\
    LENGTH (clone_instruction p labels inst).inst_operands =
      (if (clone_instruction p labels inst).inst_opcode = CREATE then 3 else 4)` by
    gvs[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  `(clone_instruction p labels inst).inst_operands =
    MAP (clone_operand p labels) inst.inst_operands /\
    (clone_instruction p labels inst).inst_opcode = inst.inst_opcode` by
    simp[clone_instruction_def] >>
  Cases_on `inst.inst_opcode = CREATE` >> gvs[] >>
  simp[step_inst_non_invoke, inline_create_eval_list] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
  IF_CASES_TAC >> simp[inline_opaque_frame_exceptional_halt] >>
  irule inline_create_clone_result >> simp[] >> metis_tac[]
QED

(* Successful ordinary steps establish their declared outputs; early terminal
   paths need only preserve the incoming support. *)
Definition inline_ordinary_step_result_def:
  inline_ordinary_step_result ren V opaque saved P inst r q <=>
    lift_result
      (inline_opaque_frame_rel ren (V UNION set inst.inst_outputs) opaque saved P)
      (inline_opaque_frame_rel ren V opaque saved P)
      (inline_opaque_frame_rel ren V opaque saved P) r q /\
    (!ret st. r <> IntRet ret st)
End

Theorem inline_ordinary_step_result_cases[simp]:
  (inline_ordinary_step_result ren V opaque saved P inst (OK s) q <=>
    ?t. q = OK t /\
      inline_opaque_frame_rel ren (V UNION set inst.inst_outputs) opaque saved P s t) /\
  (inline_ordinary_step_result ren V opaque saved P inst (Halt s) q <=>
    ?t. q = Halt t /\ inline_opaque_frame_rel ren V opaque saved P s t) /\
  (inline_ordinary_step_result ren V opaque saved P inst (Abort a s) q <=>
    ?t. q = Abort a t /\ inline_opaque_frame_rel ren V opaque saved P s t) /\
  (inline_ordinary_step_result ren V opaque saved P inst (Error e) q <=>
    ?e'. q = Error e') /\
  (inline_ordinary_step_result ren V opaque saved P inst (IntRet ret s) q <=> F)
Proof
  Cases_on `q` >>
  simp[inline_ordinary_step_result_def, stateEquivTheory.lift_result_def] >>
  metis_tac[]
QED

Theorem inline_clone_eval_operands_restrict:
  !xs ops.
    (!op. MEM op ops ==>
      eval_operand (clone_operand p labels op) t = eval_operand op s) /\
    (!op. MEM op xs ==> MEM op ops) ==>
    eval_operands (MAP (clone_operand p labels) xs) t = eval_operands xs s
Proof
  Induct_on `xs` >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand (clone_operand p labels h) t = eval_operand h s` by metis_tac[MEM] >>
  `eval_operands (MAP (clone_operand p labels) xs) t = eval_operands xs s`
    by metis_tac[MEM] >>
  simp[]
QED

Theorem inline_clone_eval_operands_members:
  (!op. MEM op ops ==>
    eval_operand (clone_operand p labels op) t = eval_operand op s) ==>
  eval_operands (MAP (clone_operand p labels) ops) t = eval_operands ops s
Proof
  strip_tac >> irule inline_clone_eval_operands_restrict >>
  qexists_tac `ops` >> simp[]
QED

Theorem inline_clone_eval_operands_reverse_tail:
  (!op. MEM op ops ==>
    eval_operand (clone_operand p labels op) t = eval_operand op s) ==>
  eval_operands (MAP (clone_operand p labels) (REVERSE (TL ops))) t =
    eval_operands (REVERSE (TL ops)) s
Proof
  strip_tac >> irule inline_clone_eval_operands_restrict >>
  qexists_tac `ops` >> simp[] >> Cases_on `ops` >> simp[]
QED

(* Representative static shapes used by the ordinary-class dispatcher.
   In particular BUMP imposes no distinctness condition on its outputs. *)
Theorem inline_inst_wf_log_shape:
  inst_wf inst /\ inst.inst_opcode = LOG ==>
  (?tc rest. inst.inst_operands = Lit tc :: rest /\ LENGTH rest = w2n tc + 2) /\
  inst.inst_outputs = []
Proof
  strip_tac >> gvs[inst_wf_def] >> metis_tac[]
QED

Theorem inline_inst_wf_bump_shape:
  inst_wf inst /\ inst.inst_opcode = BUMP ==>
  LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 2
Proof
  strip_tac >> gvs[inst_wf_def]
QED

Theorem inline_inst_wf_getfmp_shape:
  inst_wf inst /\ inst.inst_opcode = GETFMP ==>
  inst.inst_operands = [] /\ LENGTH inst.inst_outputs = 1
Proof
  strip_tac >> gvs[inst_wf_def]
QED

Theorem inline_inst_wf_call_shape:
  inst_wf inst /\ inst.inst_opcode = CALL ==>
  LENGTH inst.inst_operands = 7 /\ LENGTH inst.inst_outputs = 1
Proof
  strip_tac >> gvs[inst_wf_def]
QED

Theorem inline_call_clone_ok:
  inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7 /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst fuel' ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >>
  `(clone_instruction p labels inst).inst_opcode = CALL /\
    LENGTH (clone_instruction p labels inst).inst_operands = 7 /\
    (clone_instruction p labels inst).inst_operands =
      MAP (clone_operand p labels) inst.inst_operands` by simp[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  gvs[step_inst_non_invoke, inline_call_eval_list, AllCaseEqs()] >>
  irule inline_ext_call_clone_frame >> simp[] >> metis_tac[]
QED

Theorem inline_create_opcode_clone_ok:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  LENGTH inst.inst_operands = (if inst.inst_opcode = CREATE then 3 else 4) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x /\ step_inst fuel ctx inst s = OK s' ==>
  ?t'. step_inst fuel' ctx' (clone_instruction p labels inst) t = OK t' /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P s' t'
Proof
  strip_tac >>
  `MEM (clone_instruction p labels inst).inst_opcode [CREATE; CREATE2] /\
    LENGTH (clone_instruction p labels inst).inst_operands =
      (if (clone_instruction p labels inst).inst_opcode = CREATE then 3 else 4) /\
    (clone_instruction p labels inst).inst_operands =
      MAP (clone_operand p labels) inst.inst_operands /\
    (clone_instruction p labels inst).inst_opcode = inst.inst_opcode` by
    gvs[clone_instruction_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality] >>
  Cases_on `inst.inst_opcode = CREATE` >> gvs[] >>
  gvs[step_inst_non_invoke, inline_create_eval_list, AllCaseEqs()] >>
  irule inline_create_clone_frame >> simp[] >> metis_tac[]
QED

Theorem inline_ordinary_step_result_from_strong:
  inline_ordinary_result
    (inline_opaque_frame_rel ren (V UNION set inst.inst_outputs) opaque saved P) r q ==>
  inline_ordinary_step_result ren V opaque saved P inst r q
Proof
  Cases_on `r` >> simp[] >>
  metis_tac[inline_opaque_frame_restrict, pred_setTheory.SUBSET_UNION]
QED

Theorem inline_ordinary_step_result_from_ok:
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P) r q /\
  (!s'. r = OK s' ==> ?t'. q = OK t' /\
    inline_opaque_frame_rel ren (V UNION set inst.inst_outputs) opaque saved P s' t') ==>
  inline_ordinary_step_result ren V opaque saved P inst r q
Proof
  Cases_on `r` >> simp[] >> metis_tac[]
QED

Theorem inline_call_clone_step_result:
  inst.inst_opcode = CALL /\ LENGTH inst.inst_operands = 7 /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_step_result ren V opaque saved P inst
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >> irule inline_ordinary_step_result_from_ok >>
  conj_tac >- (
    `V UNION set inst.inst_outputs = x INSERT V` by (simp[] >> SET_TAC[]) >>
    pop_assum (fn th => pure_rewrite_tac[th]) >> rpt strip_tac >>
    irule inline_call_clone_ok >> simp[] >> metis_tac[]) >>
  irule inline_call_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_create_opcode_clone_step_result:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  LENGTH inst.inst_operands = (if inst.inst_opcode = CREATE then 3 else 4) /\
  inst.inst_outputs = [x] /\
  eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  ren x = STRCAT p x ==>
  inline_ordinary_step_result ren V opaque saved P inst
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >> irule inline_ordinary_step_result_from_ok >>
  conj_tac >- (
    `V UNION set inst.inst_outputs = x INSERT V` by (simp[] >> SET_TAC[]) >>
    pop_assum (fn th => pure_rewrite_tac[th]) >> rpt strip_tac >>
    irule inline_create_opcode_clone_ok >> simp[] >> metis_tac[]) >>
  irule inline_create_opcode_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_inst_wf_value_output[local]:
  inst_wf inst /\
  (inline_pure1_opcode inst.inst_opcode \/ inline_pure2_opcode inst.inst_opcode \/
   inline_pure3_opcode inst.inst_opcode \/ inline_read0_opcode inst.inst_opcode \/
   inline_read1_opcode inst.inst_opcode) ==>
  LENGTH inst.inst_outputs = 1
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inst_wf_def, inline_pure1_opcode_def, inline_pure2_opcode_def,
    inline_pure3_opcode_def, inline_read0_opcode_def, inline_read1_opcode_def] >>
  metis_tac[]
QED

Theorem inline_ordinary_step_result_singleton:
  inst.inst_outputs = [x] /\
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P) r q ==>
  inline_ordinary_step_result ren V opaque saved P inst r q
Proof
  strip_tac >> irule inline_ordinary_step_result_from_strong >>
  `V UNION set inst.inst_outputs = x INSERT V` by (simp[] >> SET_TAC[]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> simp[]
QED

Theorem inline_ordinary_step_result_empty:
  inst.inst_outputs = [] /\
  inline_ordinary_result (inline_opaque_frame_rel ren V opaque saved P) r q ==>
  inline_ordinary_step_result ren V opaque saved P inst r q
Proof
  strip_tac >> irule inline_ordinary_step_result_from_strong >> simp[]
QED

Theorem inline_ordinary_result_singleton_support[local]:
  inline_ordinary_result (inline_opaque_frame_rel ren (x INSERT V) opaque saved P) r q ==>
  inline_ordinary_result
    (inline_opaque_frame_rel ren (V UNION {x}) opaque saved P) r q
Proof
  `V UNION {x} = x INSERT V` by SET_TAC[] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> simp[]
QED

Theorem inline_ordinary_clone_step_result:
  inst_wf inst /\ inline_ordinary_opcode inst.inst_opcode /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand (clone_operand p labels op) t = eval_operand op s) /\
  (!u v. u IN V UNION set inst.inst_outputs /\ v IN V UNION set inst.inst_outputs ==>
    (ren u = ren v <=> u = v)) /\
  (!x. MEM x inst.inst_outputs ==> ren x NOTIN P /\ ren x = STRCAT p x) ==>
  inline_ordinary_step_result ren V opaque saved P inst
    (step_inst fuel ctx inst s)
    (step_inst fuel' ctx' (clone_instruction p labels inst) t)
Proof
  strip_tac >>
  `eval_operands (MAP (clone_operand p labels) inst.inst_operands) t =
    eval_operands inst.inst_operands s` by
    (irule inline_clone_eval_operands_members >> simp[]) >>
  `eval_operands (MAP (clone_operand p labels) (REVERSE (TL inst.inst_operands))) t =
    eval_operands (REVERSE (TL inst.inst_operands)) s` by
    (irule inline_clone_eval_operands_reverse_tail >> simp[]) >>
  Cases_on `inline_pure2_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_outputs = 1` by
        (irule inline_inst_wf_value_output >> simp[] >> metis_tac[]) >>
      `?x. inst.inst_outputs = [x]` by gvs[listTheory.LENGTH_EQ_NUM_compute] >>
      pop_assum strip_assume_tac >>
      irule inline_ordinary_step_result_from_strong >>
      `V UNION set inst.inst_outputs = HD inst.inst_outputs INSERT V` by
        (simp[] >> SET_TAC[]) >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      irule inline_pure2_opcode_clone_result >> simp[] >> metis_tac[]) >>
  Cases_on `inline_pure1_opcode inst.inst_opcode \/ inline_pure3_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_outputs = 1` by
        (irule inline_inst_wf_value_output >> simp[] >> metis_tac[]) >>
      `?x. inst.inst_outputs = [x]` by gvs[listTheory.LENGTH_EQ_NUM_compute] >>
      pop_assum strip_assume_tac >>
      irule inline_ordinary_step_result_from_strong >>
      `V UNION set inst.inst_outputs = HD inst.inst_outputs INSERT V` by
        (simp[] >> SET_TAC[]) >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      irule inline_pure13_opcode_clone_result >> simp[] >> metis_tac[]) >>
  Cases_on `inline_read0_opcode inst.inst_opcode \/ inline_read1_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_outputs = 1` by
        (irule inline_inst_wf_value_output >> simp[] >> metis_tac[]) >>
      `?x. inst.inst_outputs = [x]` by gvs[listTheory.LENGTH_EQ_NUM_compute] >>
      pop_assum strip_assume_tac >>
      irule inline_ordinary_step_result_from_strong >>
      `V UNION set inst.inst_outputs = HD inst.inst_outputs INSERT V` by
        (simp[] >> SET_TAC[]) >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      irule inline_read_opcode_clone_result >> simp[] >> metis_tac[]) >>
  `inline_effect_opcode inst.inst_opcode \/ inline_special_opcode inst.inst_opcode` by
    metis_tac[inline_ordinary_opcode_coverage] >>
  qpat_x_assum `inline_ordinary_opcode _` kall_tac >>
  qpat_x_assum `~inline_pure2_opcode _` kall_tac >>
  qpat_x_assum `~(_ \/ _)` kall_tac >>
  qpat_x_assum `~(_ \/ _)` kall_tac >>
  gvs[inline_effect_opcode_def, inline_special_opcode_def]
  >~ [`inst.inst_opcode = CALL`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_call_clone_step_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = CREATE`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_create_opcode_clone_step_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = CREATE2`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_create_opcode_clone_step_result >> simp[] >> metis_tac[]) >>
  irule inline_ordinary_step_result_from_strong
  >~ [`inst.inst_opcode = INVALID`]
  >- (gvs[inst_wf_def] >> irule inline_simple_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = NOP`]
  >- (gvs[inst_wf_def] >> irule inline_simple_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = STOP`]
  >- (gvs[inst_wf_def] >> irule inline_simple_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = SINK`]
  >- (gvs[inst_wf_def] >> irule inline_simple_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = MSTORE`]
  >- (gvs[inst_wf_def] >> irule inline_write2_opcode_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = MSTORE8`]
  >- (gvs[inst_wf_def] >> irule inline_write2_opcode_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = SSTORE`]
  >- (gvs[inst_wf_def] >> irule inline_storage_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = TSTORE`]
  >- (gvs[inst_wf_def] >> irule inline_storage_opcode_clone_result >> simp[])
  >~ [`inst.inst_opcode = MCOPY`]
  >- (gvs[inst_wf_def] >> irule inline_mcopy_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = ISTORE`]
  >- (gvs[inst_wf_def] >> irule inline_istore_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = CALLDATACOPY`]
  >- (gvs[inst_wf_def] >> irule inline_copy_data_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = DLOADBYTES`]
  >- (gvs[inst_wf_def] >> irule inline_copy_data_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = CODECOPY`]
  >- (gvs[inst_wf_def] >> irule inline_copy_data_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = RETURNDATACOPY`]
  >- (gvs[inst_wf_def] >> irule inline_returndatacopy_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = EXTCODECOPY`]
  >- (gvs[inst_wf_def] >> irule inline_extcodecopy_atomic_clone_result >> simp[])
  >~ [`inst.inst_opcode = ASSERT`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_assert_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_assert_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = RETURN`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_return_revert_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = REVERT`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_return_revert_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = SELFDESTRUCT`]
  >- (gvs[inst_wf_def] >> irule inline_selfdestruct_clone_result >> simp[])
  >~ [`inst.inst_opcode = LOG`]
  >- (gvs[inst_wf_def] >> irule inline_log_clone_result >> simp[] >> metis_tac[]) >>
  all_tac
  >~ [`inst.inst_opcode = GETFMP`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_fmp_read_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = INITIAL_FMP`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_fmp_read_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = GAS`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_gas_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = SHA3`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_sha3_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = STATICCALL`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_call6_clone_result >> simp[] >> metis_tac[])
  >~ [`inst.inst_opcode = DELEGATECALL`]
  >- (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
      irule inline_ordinary_result_singleton_support >>
      irule inline_call6_clone_result >> simp[] >> metis_tac[]) >>
  gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  irule inline_bump_clone_result >> simp[] >> metis_tac[]
QED

Theorem inline_ordinary_step_result_ok:
  inline_ordinary_step_result ren V opaque saved P inst r q /\ r = OK s ==>
  ?t. q = OK t /\
    inline_opaque_frame_rel ren (V UNION set inst.inst_outputs) opaque saved P s t
Proof
  strip_tac >> gvs[]
QED

Theorem inline_ordinary_step_result_halt:
  inline_ordinary_step_result ren V opaque saved P inst r q /\ r = Halt s ==>
  ?t. q = Halt t /\ inline_opaque_frame_rel ren V opaque saved P s t
Proof
  strip_tac >> gvs[]
QED

Theorem inline_ordinary_step_result_abort:
  inline_ordinary_step_result ren V opaque saved P inst r q /\ r = Abort a s ==>
  ?t. q = Abort a t /\ inline_opaque_frame_rel ren V opaque saved P s t
Proof
  strip_tac >> gvs[]
QED

Theorem inline_ordinary_step_result_error:
  inline_ordinary_step_result ren V opaque saved P inst r q /\ r = Error e ==>
  ?e'. q = Error e'
Proof
  strip_tac >> gvs[]
QED

Theorem inline_ordinary_step_result_not_intret:
  inline_ordinary_step_result ren V opaque saved P inst r q ==>
  !ret s. r <> IntRet ret s
Proof
  simp[inline_ordinary_step_result_def]
QED
