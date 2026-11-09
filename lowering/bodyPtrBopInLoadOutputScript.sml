(* Scalar load output boundary. Content cleanliness is a separate premise;
   clean address taint alone does not imply clean loaded contents. *)
Theory bodyPtrBopInLoadOutput
Ancestors ptrDiscipline venomInst venomState finite_map pred_set

Theorem scalar_load_output_taint:
  !a s w opc id out t tn.
    eval_operand a s = SOME w /\
    (opc = MLOAD \/ opc = ILOAD \/ opc = SLOAD \/ opc = TLOAD \/
     opc = CALLDATALOAD \/ opc = DLOAD) ==>
    op_taint (step_taint (mk_inst id opc [a] [out]) s t tn) (Var out) =
      (if opc = MLOAD \/ opc = ILOAD then mem_word_taint tn.t_mem (w2n w)
       else if opc = SLOAD then key_taint tn.t_stor w
       else if opc = TLOAD then key_taint tn.t_trans w else {})
Proof
  rpt strip_tac >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem scalar_load_output_prov:
  !opc PG G id a out t.
    (opc = MLOAD \/ opc = ILOAD \/ opc = SLOAD \/ opc = TLOAD \/
     opc = CALLDATALOAD \/ opc = DLOAD) ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [a] [out]) t) out = NONE
Proof
  rpt strip_tac >>
  gvs[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
      FLOOKUP_DRESTRICT]
QED

Theorem scalar_load_output_clean:
  !a s w opc id out t tn.
    eval_operand a s = SOME w /\
    (opc = MLOAD \/ opc = ILOAD \/ opc = SLOAD \/ opc = TLOAD \/
     opc = CALLDATALOAD \/ opc = DLOAD) /\
    (opc = MLOAD \/ opc = ILOAD ==> mem_word_taint tn.t_mem (w2n w) = {}) /\
    (opc = SLOAD ==> key_taint tn.t_stor w = {}) /\
    (opc = TLOAD ==> key_taint tn.t_trans w = {}) ==>
    op_taint (step_taint (mk_inst id opc [a] [out]) s t tn) (Var out) = {}
Proof
  rpt strip_tac >>
  qspecl_then [`a`, `s`, `w`] mp_tac scalar_load_output_taint >>
  simp[]
QED
