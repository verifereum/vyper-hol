Theory o1CodeEndLowerReadTransport
Ancestors
  o1CodeEndLowerPacket o1CodeEndLowerBoundary codegenSymRel
  venomExecSemantics venomExecProofs venomState finite_map words
  lowerDloadDefs lowerDloadSafetyKernel list

(* The modular delta is observed immediately after the generated ADD. *)
Theorem code_end_add_read_delta[local]:
  a.inst_opcode = ADD /\ a.inst_operands = [op; Label "code_end"] /\
  a.inst_outputs = [x] /\ step_inst 0 C a s = OK u /\
  t = (u with vs_inst_idx := k) /\
  eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword /\
  (!off. eval_operand op s = SOME off ==>
         w2n off < dimword(:256) DIV 2) ==>
  ?off. w = bword + off /\ w2n off < dimword(:256) DIV 2 /\
        w2n (w - bword) < dimword(:256) DIV 2
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
      AllCaseEqs()] >>
  gvs[eval_operand_def, eval_operands_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[WORD_ADD_COMM, WORD_ADD_SUB]
QED

Theorem lower_dload_copy_predecessor[local]:
  lower_dload_inst_supply u inst = (xs,u') /\
  (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) /\
  ~MEM (Label "code_end") inst.inst_operands /\
  h < LENGTH xs /\ (EL h xs).inst_opcode = CODECOPY /\
  (EL h xs).inst_operands = [dst; Var x; sz] ==>
  ?j op. h = SUC j /\
    (EL j xs).inst_opcode = ADD /\
    (EL j xs).inst_operands = [op; Label "code_end"] /\
    (EL j xs).inst_outputs = [x] /\ op <> Label "code_end"
Proof
  rw[lower_dload_inst_supply_def, AllCaseEqs()] >> gvs[] >>
  `h = 0 \/ h = 1 \/ h = 2 \/ h = 3` by decide_tac >>
  gvs[] >> metis_tac[]
QED

Theorem lower_dload_codecopy_delta:
  lower_dload_inst_supply u inst = (xs,u') /\
  (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) /\
  ~MEM (Label "code_end") inst.inst_operands /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v u.irs_used_vars) /\
  inst_dload_in_section inst s /\
  LENGTH s.vs_data_section < dimword(:256) DIV 2 /\
  ld_prefix C fn xs p h s t /\
  (EL h xs).inst_opcode = CODECOPY /\
  (EL h xs).inst_operands = [dst; Var x; sz] /\
  eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword ==>
  ?off. w = bword + off /\ w2n off < dimword(:256) DIV 2 /\
        w2n (w - bword) < dimword(:256) DIV 2
Proof
  strip_tac >>
  `h < LENGTH xs` by metis_tac[ld_prefix_bound] >>
  `?j op. h = SUC j /\ (EL j xs).inst_opcode = ADD /\
    (EL j xs).inst_operands = [op; Label "code_end"] /\
    (EL j xs).inst_outputs = [x] /\ op <> Label "code_end"` by
    metis_tac[lower_dload_copy_predecessor] >> gvs[] >>
  drule ld_prefix_predecessor >>
  disch_then (qx_choose_then `before_add`
    (qx_choose_then `after_add` strip_assume_tac)) >>
  `!off. eval_operand op before_add = SOME off ==>
         w2n off < dimword(:256) DIV 2` by
    (metis_tac[lower_dload_prefix_code_end_bound, MEM]) >>
  metis_tac[code_end_add_read_delta]
QED
