(* Value boundary for actual successful expansion traces. *)
Theory lowerDloadExpansionExit
Ancestors
  lowerDloadCodeDataBytes lowerDloadSafetyKernel lowerDloadSafetyAllocation
  lowerDloadSafetyWriteBytes lowerDloadSafetyRelation
  venomExecSemantics venomState venomInst finite_map list words arithmetic

Theorem ld_alloca_value_frame[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [a] /\
  step_inst fuel C inst s = OK t ==>
  ?w. FLOOKUP t.vs_vars a = SOME w /\
    (!v. v <> a ==> FLOOKUP t.vs_vars v = FLOOKUP s.vs_vars v) /\
    t.vs_labels = s.vs_labels /\ t.vs_code = s.vs_code /\
    t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> drule_all ld_alloca_step >> strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  simp[FLOOKUP_UPDATE]
QED


Theorem ld_codecopy_value_frame[local]:
  inst.inst_opcode = CODECOPY /\ step_inst fuel C inst s = OK t ==>
  t.vs_vars = s.vs_vars /\ t.vs_code = s.vs_code /\
  t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> gvs[step_inst_non_invoke, Once step_inst_base_def,
    AllCaseEqs(), write_memory_with_expansion_def]
QED

Theorem ld_dload_expansion_value_exit:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a; Var z; Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ out <> a /\ out <> z /\ off <> Var a /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  eval_operand off s = SOME ow /\ eval_operand off t0 = SOME ow /\
  code_layout_valid s /\
  eval_operand (Label "code_end") s = SOME basew /\
  eval_operand (Label "code_end") t0 = SOME basew /\
  t0.vs_code = s.vs_code /\
  w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256) /\
  t0.vs_inst_idx = p /\ ld_prefix C' fn' X p 3 t0 t /\
  step_inst fuel C' (EL 3 X) t = OK u ==>
  ?ss. step_inst 0 C inst s = OK ss /\
    FLOOKUP u.vs_vars out = FLOOKUP ss.vs_vars out /\
    u.vs_inst_idx = p+3 /\
    (!v. v <> a /\ v <> z /\ v <> out ==>
      FLOOKUP u.vs_vars v = FLOOKUP t0.vs_vars v)
Proof
  strip_tac >>
  drule_all ld_prefix_position >> disch_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `2`] |> SRULE []) >>
  disch_then (qx_choose_then `t2` (qx_choose_then `u2` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `1`] |> SRULE []) >>
  disch_then (qx_choose_then `t1` (qx_choose_then `u1` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `tzero` (qx_choose_then `u0` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  qpat_assum `step_inst 0 _ _ _ = OK u0`
    (mp_then (Pos last) mp_tac ld_alloca_value_frame) >>
  simp[] >> strip_tac >>
  `eval_operand off (u0 with vs_inst_idx := SUC t0.vs_inst_idx) = SOME ow` by
    (Cases_on `off` >> gvs[eval_operand_def, lookup_var_def]) >>
  `eval_operand (Label "code_end")
    (u0 with vs_inst_idx := SUC t0.vs_inst_idx) = SOME basew` by
    gvs[eval_operand_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK u1` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[] >>
  `mload (w2n w) u2 = word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n ow) s.vs_data_section ++ REPLICATE 32 0w))` by
    (irule ld_codecopy_source_mload >>
     simp[] >> goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  qpat_assum `step_inst 0 _ _ _ = OK u2`
    (mp_then (Pos last) mp_tac ld_codecopy_value_frame) >>
  simp[update_var_def] >> strip_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = OK u` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  qexists_tac `update_var out
    (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n ow) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  simp[Once step_inst_base_def, exec_read1_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `mload _ u2 = _` mp_tac >> simp[mload_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "expansion exit theorem has hypotheses")
  [ld_alloca_value_frame, ld_codecopy_value_frame, ld_dload_expansion_value_exit];

Theorem ld_codecopy_memory_private:
  ld_memory lo A tn s t /\
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dest; src; len] /\
  eval_operand dest t = SOME dw /\ eval_operand src t = SOME sw /\
  eval_operand len t = SOME nw /\ lo <= w2n dw /\
  (!k b c n. FLOOKUP A k = SOME (b,c,n) /\ 0 < n ==>
     c+n <= w2n dw \/ w2n dw+w2n nw <= c) /\
  step_inst fuel C inst t = OK u ==>
  ld_memory lo A tn s u
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, Once step_inst_base_def] >>
  irule ld_memory_write_private >> simp[] >> metis_tac[]
QED

val _ = if null (hyp ld_codecopy_memory_private) then ()
  else raise Fail "private CODECOPY theorem has hypotheses";

Theorem ld_codecopy_owned_private:
  ld_global lo A (f::fs) /\ EVERY (ld_maps A) (f::fs) /\
  FDOM A = ld_slots A (f::fs) /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE /\
  FLOOKUP f.lf_tgt.vs_allocas ai = SOME (d,m) /\ 0 < m /\
  ld_memory lo A tn s t /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dest; src; len] /\
  eval_operand dest t = SOME dw /\ eval_operand src t = SOME sw /\
  eval_operand len t = SOME nw /\ w2n dw = d /\ w2n nw = m /\
  step_inst fuel C inst t = OK u ==>
  ld_memory lo A tn s u
Proof
  strip_tac >> drule_all ld_private_slot_separation >> strip_tac >>
  irule ld_codecopy_memory_private >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  gvs[] >> metis_tac[]
QED

val _ = if null (hyp ld_codecopy_owned_private) then ()
  else raise Fail "owned private CODECOPY theorem has hypotheses";
