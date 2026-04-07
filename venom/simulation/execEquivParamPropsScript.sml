(*
 * Parameterized Execution Equivalence — Properties (Statements Only)
 *
 * Re-exports from proofs/execEquivParamProofsScript.sml via ACCEPT_TAC.
 *)

Theory execEquivParamProps
Ancestors
  execEquivParamProofs
Libs
  pred_setTheory

Theorem step_inst_preserves_R:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  ACCEPT_TAC step_inst_preserves_R_proof
QED

Theorem run_block_preserves_R:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    (!fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2)) /\
    (!fuel ctx s1 s2.
       R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_function fuel ctx fn s1)
                                (run_function fuel ctx fn s2))
Proof
  ACCEPT_TAC run_block_preserves_R_proof
QED

Theorem run_block_same_preserves_RQ:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (Q : venom_state -> venom_state -> bool)
   bb fuel ctx s1 s2.
    valid_state_rel R_ok R_term /\
    R_ok s1 s2 /\ Q s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst bb.bb_instructions ==>
            inst.inst_opcode <> INVOKE) /\
    (!i s1' s2'. i < LENGTH bb.bb_instructions /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i ==>
       !x. MEM (Var x) (EL i bb.bb_instructions).inst_operands ==>
           lookup_var x s1' = lookup_var x s2') /\
    (!i s1' s2' v1 v2.
       i < LENGTH bb.bb_instructions /\
       ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i /\
       step_inst fuel ctx (EL i bb.bb_instructions) s1' = OK v1 /\
       step_inst fuel ctx (EL i bb.bb_instructions) s2' = OK v2 /\
       R_ok v1 v2 ==>
       Q (v1 with vs_inst_idx := SUC i)
         (v2 with vs_inst_idx := SUC i)) ==>
    lift_result R_ok R_term R_term
      (run_block fuel ctx bb s1)
      (run_block fuel ctx bb s2)
Proof
  ACCEPT_TAC run_block_same_preserves_RQ_proof
QED

Theorem state_equiv_execution_equiv_valid_state_rel:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  ACCEPT_TAC state_equiv_execution_equiv_valid_state_rel_proof
QED

Theorem valid_state_rel_mixed:
  !vars vars'. vars SUBSET vars' ==>
    valid_state_rel (state_equiv vars) (execution_equiv vars')
Proof
  ACCEPT_TAC valid_state_rel_mixed_proof
QED
