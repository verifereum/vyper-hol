(* Fixed-length physical membership search after the linked RHS has landed. *)
Theory bodyMembershipArrayFixedRunMods
Ancestors
  bodyPtrBopInHeaderCode bodyFullBopRestWordFullControl venomState ptrDiscipline

Theorem membership_array_fixed_run_mods:
  let loc = case vv_location vv of SOME l => l | NONE => LocMemory in
  let width = if cenv.ce_is_ctor /\ loc = LocCode /\ IS_SOME cenv.ce_imm_alloca
              then 2 else 1 in
  let loaded = Var ("%" ++ toString (sm.cs_next_var + 4 + width)) in
  bd = Fixed n /\ LENGTH ws = n /\ n < dimword (:256) /\
  compile_var_array_membership cenv needle vv (ArrayT ety bd) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!x. needle = Var x ==> not_fresh_at sm x) /\
  (!H. guard H ==>
    eval_operand needle u = SOME needleword /\
    op_prov Gu needle = NONE /\ op_taint Tu needle = {}) /\
  (!i s Gs Ts. i < LENGTH ws /\
    (!H. guard H ==>
      membership_loop_frame sm Gu Tu u Gs Ts s /\
      membership_loop_registers sm i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sm.cs_next_label + 2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sm Gu Tu u Gt Tt t /\
      membership_loop_registers sm i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sm.cs_next_label + 2) /\
      t.vs_inst_idx = 2 + width /\
      eval_operand loaded t = SOME (EL i ws) /\
      op_prov Gt loaded = NONE /\ op_taint Tt loaded = {}) /\
  (!H. guard H ==> ~u.vs_halted /\ allocas_from lo u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  ?q Gt Tt. !H. guard H ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gu,Tu) [] (OK q,Gt,Tt) /\
    membership_loop_frame sm Gu Tu u Gt Tt q /\
    eval_operand out q = SOME
      (bool_to_word (if is_in then MEM needleword ws else ~MEM needleword ws)) /\
    op_prov Gt out = NONE /\ op_taint Tt out = {} /\
    ~q.vs_halted /\ allocas_from lo q /\
    q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [membership_fixed_compile_split]) >>
  irule rest_word_membership_loop_const_full_horizon_joint_all >>
  simp[] >>
  qpat_assum `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. guard H ==> eval_operand _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def]
QED
