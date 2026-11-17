(* Mode execution adapters with explicit instruction-bridge interfaces. *)
Theory asmSymModeInterfaceOwn
Ancestors asmSymForwardOwn codegenSymRel asmSymBridge asmSymOwnCode
  asmSymSem asmSem list finite_map

(* Reuse the bridge's closed-lambda result interface as parser syntax. *)
val result_rel = mk_var ("R", type_of ``asm_sym_rel p env``);
val result_body = subst [``asm_sym_rel p env`` |-> result_rel]
  (lhs (concl asm_sym_step_rel_core_canonical));
val result_vars = result_rel :: List.map (fn name =>
  List.find (fn v => fst (dest_var v) = name) (free_vars result_body)
  |> valOf) ["sr", "cr"];
val _ = Parse.temp_overload_on
  ("bridge_result", list_mk_abs (result_vars, result_body));

Theorem asm_sym_inst_step_mode_from_interfaces:
  (!l. MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p) ==>
    ?off. FLOOKUP lo l = SOME off) /\
  (!dest i w. sym_jump_dest p dest = SOME i /\
    sval_conc lo dest = SOME w ==>
    FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i) /\
  (!cs ss name. asm_sym_rel_own lo p env own cs ss /\
    (name = "CODESIZE" \/ name = "CODECOPY") ==>
    bridge_result (asm_sym_rel_own lo p env own)
      (sym_step_op_own p env own name ss)
      (asm_step_op (build_offset_to_pc p) name cs)) /\
  asm_sym_rel_own lo p env own cs ss /\ MEM ai p ==>
  bridge_result (asm_sym_rel_own lo p env own)
    (if allow_own then sym_step_own p env own ai ss
     else sym_step p env ai ss)
    (asm_step lo (build_offset_to_pc p) ai cs)
Proof
  strip_tac >>
  `bridge_result (asm_sym_rel_own lo p env own)
    (sym_step_own p env own ai ss)
    (asm_step lo (build_offset_to_pc p) ai cs)` by
    (irule asm_sym_inst_step_own_conditional >> metis_tac[]) >>
  Cases_on `allow_own` >> simp[] >>
  Cases_on `sym_step p env ai ss` >> simp[] >>
  `sym_step_own p env own ai ss = sym_step p env ai ss` by
    (irule sym_step_own_nonbad >> simp[]) >> gvs[]
QED

Theorem asm_sym_step_mode_replay_from_interfaces:
  (!l. MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p) ==>
    ?off. FLOOKUP lo l = SOME off) /\
  (!dest i w. sym_jump_dest p dest = SOME i /\
    sval_conc lo dest = SOME w ==>
    FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i) /\
  (!cs ss name. asm_sym_rel_own lo p env own cs ss /\
    (name = "CODESIZE" \/ name = "CODECOPY") ==>
    bridge_result (asm_sym_rel_own lo p env own)
      (sym_step_op_own p env own name ss)
      (asm_step_op (build_offset_to_pc p) name cs)) /\
  asm_sym_rel_own lo p env own cs ss /\
  asm_block_at p cs.as_pc [ai] /\
  asm_step lo (build_offset_to_pc p) ai cs = AsmOK cs' /\
  (!msg. (if allow_own then sym_step_own p env own ai ss
          else sym_step p env ai ss) <> SymBad msg) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
    asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >>
  `MEM ai p` by (fs[asm_block_at_def] >> (gvs[EL_MEM])) >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_own_pc] >>
  `bridge_result (asm_sym_rel_own lo p env own)
    (if allow_own then sym_step_own p env own ai ss
     else sym_step p env ai ss)
    (asm_step lo (build_offset_to_pc p) ai cs)` by
    (irule asm_sym_inst_step_mode_from_interfaces >> metis_tac[]) >>
  `sym_steps_mode allow_own p env own 1 ss =
    if allow_own then sym_step_own p env own ai ss
    else sym_step p env ai ss` by
    (irule sym_steps_mode_single >> simp[]) >>
  Cases_on `if allow_own then sym_step_own p env own ai ss
            else sym_step p env ai ss` >> gvs[]
QED

Theorem asm_sym_steps_mode_from_interfaces:
  (!l. MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p) ==>
    ?off. FLOOKUP lo l = SOME off) /\
  (!dest i w. sym_jump_dest p dest = SOME i /\
    sval_conc lo dest = SOME w ==>
    FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i) /\
  (!cs ss name. asm_sym_rel_own lo p env own cs ss /\
    (name = "CODESIZE" \/ name = "CODECOPY") ==>
    bridge_result (asm_sym_rel_own lo p env own)
      (sym_step_op_own p env own name ss)
      (asm_step_op (build_offset_to_pc p) name cs)) ==>
  !n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'
Proof
  strip_tac >> match_mp_tac asm_sym_steps_mode_lockstep_from_step >>
  rpt strip_tac >>
  `bridge_result (asm_sym_rel_own lo p env own)
    (if allow_own then sym_step_own p env own (EL cs.as_pc p) ss
     else sym_step p env (EL cs.as_pc p) ss)
    (asm_step lo (build_offset_to_pc p) (EL cs.as_pc p) cs)` by
    (irule asm_sym_inst_step_mode_from_interfaces >> simp[EL_MEM] >>
     metis_tac[]) >>
  gvs[]
QED
