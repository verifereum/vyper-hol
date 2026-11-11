Theory cseWrapperProps
Ancestors venomExecSemantics

Theorem exec_pure1_singleton_shape:
 inst.inst_outputs = [x] ==>
 (?e. exec_pure1 f inst s = Error e) \/
 (?v. exec_pure1 f inst s = OK (update_var x v s))
Proof
 strip_tac >> simp[exec_pure1_def] >> rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem exec_pure2_singleton_shape:
 inst.inst_outputs = [x] ==>
 (?e. exec_pure2 f inst s = Error e) \/
 (?v. exec_pure2 f inst s = OK (update_var x v s))
Proof
 strip_tac >> simp[exec_pure2_def] >> rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem exec_pure3_singleton_shape:
 inst.inst_outputs = [x] ==>
 (?e. exec_pure3 f inst s = Error e) \/
 (?v. exec_pure3 f inst s = OK (update_var x v s))
Proof
 strip_tac >> simp[exec_pure3_def] >> rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem exec_read0_singleton_shape:
 inst.inst_outputs = [x] ==>
 (?e. exec_read0 f inst s = Error e) \/
 (?v. exec_read0 f inst s = OK (update_var x v s))
Proof
 simp[exec_read0_def] >> metis_tac[]
QED

Theorem exec_read1_singleton_shape:
 inst.inst_outputs = [x] ==>
 (?e. exec_read1 f inst s = Error e) \/
 (?v. exec_read1 f inst s = OK (update_var x v s))
Proof
 strip_tac >> simp[exec_read1_def] >> rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED
