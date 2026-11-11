(* Selected parameter permissions travel with the same coverage frames.
   No semantic predicate is added: all boundaries expose the EVERY formula. *)
Theory lowerDloadSafetyOwnership
Ancestors
  lowerDloadSafetyArguments lowerDloadSafetyRelation ptrDiscipline
  venomInst list

Theorem ld_ownership_nil:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) []
Proof
  simp[]
QED

Theorem ld_ownership_cons:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) (f::fs) <=>
  (!j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
         j IN P f.lf_fn.fn_name) /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) fs
Proof
  simp[]
QED

Theorem ld_ownership_frame_cong:
  g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q ==>
  ((!j a. j < LENGTH g.lf_Q /\ EL j g.lf_Q = SOME a ==>
          j IN P g.lf_fn.fn_name) <=>
   (!j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
          j IN P f.lf_fn.fn_name))
Proof
  simp[]
QED

Theorem ld_ownership_replace:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) (f::fs) /\
  g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q ==>
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) (g::fs)
Proof
  simp[ld_ownership_cons] >> metis_tac[ld_ownership_frame_cong]
QED

Theorem ld_ownership_push:
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) fs /\
  ld_vars P A caller /\ ptr_use_ok P (fn_pv P caller.lf_fn) inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  callee.lf_fn.fn_name = nm /\
  callee.lf_Q = MAP (op_prov caller.lf_H) args ==>
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
                   j IN P f.lf_fn.fn_name) (callee::fs)
Proof
  simp[ld_ownership_cons] >> rpt strip_tac >>
  drule_all ld_arguments_permission >> simp[]
QED
