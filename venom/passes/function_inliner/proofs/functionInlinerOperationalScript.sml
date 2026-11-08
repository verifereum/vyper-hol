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
