(* Zero-cost straight-line instruction followed by a branch.  The explicit
   endpoint lets consumers retain stronger posts than vv_post. *)
Theory bodyIntCallJointPureSuffix
Ancestors
  stmtSimDeclPath stmtSimProps emitHelperProps fragGasMode fragGasPath
  venomState venomInst venomExecSemantics exprSimUint2Str list

Theorem pure_instruction_jump_path:
  emit_inst opc args outs sa = ((),sb) /\
  emit_inst JMP [Label lbl] [] sb = ((),sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args outs) s = OK u ==>
  gas_path ctx func s 0
    (OK (jump_to lbl (u with vs_inst_idx := LENGTH sb.cs_current_insts)))
Proof
  strip_tac >>
  drule_all emit_inst_zero_marked_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule gas_marked_path_exec >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc args outs] /\
   sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_inst_extends] >>
  `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[] >>
  gvs[] >>
  `~u.vs_halted` by
    (drule gas_path_normal >> simp[]) >>
  `u.vs_current_bb = sa.cs_current_bb` by
    (`step_inst 0 ctx (mk_inst sa.cs_next_id opc args outs) s = OK u` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     drule venomInstProofsTheory.step_preserves_control_flow >>
     simp[mk_inst_def]) >>
  `gas_path ctx func (u with vs_inst_idx := LENGTH sb.cs_current_insts) 0
     (OK (jump_to lbl (u with vs_inst_idx := LENGTH sb.cs_current_insts)))` by
    (irule emit_jump_zero_path >> simp[] >> qexistsl [`sb`, `sc`] >>
     qpat_x_assum `emit_inst JMP _ _ _ = _` (mp_tac o MATCH_MP emit_inst_extends) >>
     simp[APPEND_ASSOC]) >>
  gvs[] >> drule_all gas_path_then >> simp[]
QED

(* An arbitrary property of the pointer word (in particular an authorized
   slot) survives the assignment and jump.  No positive footprint is needed. *)
Theorem pure_assign_jump_slot:
  emit_inst ASSIGN [op] [rv] sa = ((),sb) /\
  emit_inst JMP [Label lbl] [] sb = ((),sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand op s = SOME w /\ slot_ok w ==>
  ?v. gas_path ctx func s 0 (OK v) /\
      eval_operand (Var rv) v = SOME w /\ slot_ok w /\
      v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
      v.vs_alloca_next = s.vs_alloca_next /\
      (!x. x <> rv ==> lookup_var x v = lookup_var x s)
Proof
  strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ASSIGN [op] [rv]) s =
     OK (update_var rv w s)` by
    metis_tac[exprSimUint2StrTheory.u2s_step_assign] >>
  `ASSIGN <> INVOKE /\ ASSIGN <> GAS /\ ~is_terminator ASSIGN` by
    simp[is_terminator_def] >>
  drule_all pure_instruction_jump_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `jump_to lbl (update_var rv w s with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[eval_operand_def, jump_to_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
