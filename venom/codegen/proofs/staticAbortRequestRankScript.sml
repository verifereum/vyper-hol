(* Eliminate virtual ranks with a request-only exceptional observation. *)
Theory staticAbortRequestRank
Ancestors
  staticAbortTrace stackOpSim

Theorem ranked_request_silent_exception:
  (!(r:num) t. C r t ==>
     (?n u. (asm_steps lo o2pc p n t = AsmRevert u \/
             asm_steps lo o2pc p n t = AsmFault u) /\
            u.as_requests = t.as_requests) \/
     (?r' n u. r' < r /\
        static_abort_normal lo o2pc p n t u /\ C r' u)) ==>
  !r t. C r t ==>
    ?n u. (asm_steps lo o2pc p n t = AsmRevert u \/
           asm_steps lo o2pc p n t = AsmFault u) /\
          u.as_requests = t.as_requests
Proof
  strip_tac >> completeInduct_on `r` >> rpt strip_tac >>
  rename1 `C rank t` >>
  qpat_x_assum `!r t. C r t ==> _`
    (qspecl_then [`rank`, `t`] mp_tac) >>
  simp[] >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac) >>
  rename1 `lower < rank` >>
  qpat_x_assum `!m. m < rank ==> _`
    (qspec_then `lower` mp_tac) >>
  simp[] >> disch_then (qspec_then `u` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[static_abort_normal_def] >>
  metis_tac[asm_steps_add_ok]
QED
