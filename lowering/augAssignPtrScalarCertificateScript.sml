Theory augAssignPtrScalarCertificate
Ancestors venomInst pred_set list

(* A static dependency certificate is needed because straight_fresh tracks
   names, not clean inputs, and inst_seq_ptr is a dynamic execution judgment.
   INVALID is deliberately excluded: it is a terminal compiler fallback. *)
Definition scalar_binary_def:
  scalar_binary opc <=> MEM opc
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; AND; OR; XOR;
     SHL; SHR; SAR; SIGNEXTEND; LT; GT; SLT; SGT; EQ]
End

Definition scalar_unary_def:
  scalar_unary opc <=> MEM opc [NOT; ISZERO; ASSIGN]
End

Definition scalar_shape_def:
  scalar_shape i <=>
    (scalar_binary i.inst_opcode /\ LENGTH i.inst_operands = 2 /\
       LENGTH i.inst_outputs = 1) \/
    (scalar_unary i.inst_opcode /\ LENGTH i.inst_operands = 1 /\
       LENGTH i.inst_outputs = 1) \/
    (i.inst_opcode = ASSERT /\ LENGTH i.inst_operands = 1 /\
       i.inst_outputs = [])
End

Definition scalar_available_def:
  scalar_available A op <=>
    (?w. op = Lit w) \/ (?v. op = Var v /\ v IN A)
End

Definition scalar_code_def:
  scalar_code A [] = T /\
  scalar_code A (i::code) =
    (scalar_shape i /\ EVERY (scalar_available A) i.inst_operands /\
     scalar_code (A UNION set i.inst_outputs) code)
End

Theorem scalar_shape_control:
  scalar_shape i ==>
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVALID
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def] >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem scalar_code_singleton:
  scalar_code A [i] <=>
    scalar_shape i /\ EVERY (scalar_available A) i.inst_operands
Proof
  simp[scalar_code_def]
QED

Theorem scalar_available_mono:
  A SUBSET B /\ scalar_available A op ==> scalar_available B op
Proof
  simp[scalar_available_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem scalar_code_mono:
  !code A B. A SUBSET B /\ scalar_code A code ==> scalar_code B code
Proof
  Induct >> simp[scalar_code_def] >> rpt strip_tac
  >- (gvs[EVERY_MEM] >> metis_tac[scalar_available_mono]) >>
  first_x_assum irule >> qexists `A UNION set h.inst_outputs` >>
  simp[] >> ASM_SET_TAC[]
QED

Theorem scalar_code_append:
  !prefix A suffix.
    scalar_code A (prefix ++ suffix) <=>
    scalar_code A prefix /\
    scalar_code (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) prefix))) suffix
Proof
  Induct >> simp[scalar_code_def, UNION_ASSOC, CONJ_ASSOC]
QED

Theorem scalar_code_nonterminators:
  !code A. scalar_code A code ==>
    EVERY (\i. ~is_terminator i.inst_opcode) code
Proof
  Induct >> simp[scalar_code_def] >> metis_tac[scalar_shape_control]
QED

Theorem scalar_code_add_assert:
  scalar_available A x /\ scalar_available A y ==>
  scalar_code A [mk_inst id ADD [x;y] [z]; mk_inst aid ASSERT [Var z] []]
Proof
  simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
       scalar_available_def, mk_inst_def]
QED

Theorem scalar_code_binary:
  scalar_binary opc /\ scalar_available A x /\ scalar_available A y ==>
  scalar_code A [mk_inst id opc [x;y] [z]]
Proof
  simp[scalar_code_def, scalar_shape_def, mk_inst_def]
QED

Theorem scalar_code_assert:
  scalar_available A x ==> scalar_code A [mk_inst id ASSERT [x] []]
Proof
  simp[scalar_code_def, scalar_shape_def, mk_inst_def]
QED

Theorem scalar_shape_invalid:
  ~scalar_shape (mk_inst id INVALID ops outs)
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def, mk_inst_def]
QED

(* Coverage inventory for compile_binop and its helpers:
   binary: ADD SUB MUL Div SDIV Mod SMOD Exp AND OR XOR SHL SHR SAR
           SIGNEXTEND LT GT SLT SGT EQ;
   unary: NOT ISZERO (ASSIGN is useful for scalar result transport);
   checks: ASSERT, which may fail but is not an IR terminator.
   compile_select uses XOR/MUL/XOR. compile_clamp uses comparisons,
   ISZERO/AND/ASSERT. All safe_* and wrap_truncate use the above shapes.
   Terminal exception: the final branches of compile_binop_def and
   compile_compare_def emit_inst INVALID [] [] then return (Lit 0w).
   Those defining equations remain the fallback interface: no certificate
   is claimed for them. C1.2.2.8 must discharge their terminal behavior. *)
