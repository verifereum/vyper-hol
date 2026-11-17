(* Exceptional own-code opcode correspondence at arbitrary label offsets. *)
Theory asmSymExceptionalOwn
Ancestors asmSymOwnStep asmSymBridge asmSymOwnCode asmSymSem asmSem list

(* Existing closed-lambda interface, with no new logical definition. *)
val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem asm_sym_exceptional_op_own:
  asm_sym_rel_own lo p env own cs ss /\
  (name = "CODESIZE" \/ name = "CODECOPY") ==>
  bridge_result (asm_sym_rel_own lo p env own)
    (sym_step_op_own p env own name ss)
    (asm_step_op (build_offset_to_pc p) name cs)
Proof
  strip_tac
  >- (drule sym_codesize_own_sim >>
      disch_then (qspec_then `build_offset_to_pc p` strip_assume_tac) >>
      simp[]) >>
  simp[sym_step_op_own_def] >>
  `bridge_result (asm_sym_rel_own lo p env own)
     (sym_codecopy p env ss)
     (asm_step_op (build_offset_to_pc p) "CODECOPY" cs)` by
    (qspecl_then [`lo`, `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
       mp_tac sym_codecopy_sim_core >>
     simp[asm_sym_rel_core_own] >> disch_then irule >> simp[] >>
     `asm_data_env_lo_ok lo p env own /\ cs.as_code = own` by
       fs[asm_sym_rel_own_def] >>
     rpt strip_tac >> drule_all sym_codecopy_address_own >> simp[]) >>
  Cases_on `ss.sym_stack` >>
  gvs[sym_codecopy_def, sym_codecopy_own_def] >>
  Cases_on `t` >> gvs[sym_codecopy_def, sym_codecopy_own_def] >>
  Cases_on `t'`
  >- (Cases_on `h` >> Cases_on `h'` >>
      gvs[sym_codecopy_def, sym_codecopy_own_def]) >>
  rename1 `ss.sym_stack = a::b::c::stk` >>
  Cases_on `a` >> Cases_on `b` >> Cases_on `c` >>
  gvs[sym_codecopy_def, sym_codecopy_own_def] >>
  qspecl_then [`lo`, `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
    mp_tac sym_codecopy_own_value_sim_core >>
  disch_then (qspecl_then [`own`, `cs`, `ss`] mp_tac) >>
  `own = cs.as_code` by fs[asm_sym_rel_own_def] >>
  simp[asm_sym_rel_core_own, sym_codecopy_own_def]
QED
