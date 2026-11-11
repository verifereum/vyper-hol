(* Predicate propagation through context lookup and raw reachability.
   Block, instruction and active-instruction interfaces are reused from
   ctxLookupAgreeHelpers rather than duplicated here. *)
Theory ctxFmpMembershipHelpers
Ancestors
  ctxLookupAgreeHelpers contextRawReachable venomInst list

Theorem EVERY_lookup_function:
  EVERY P fns /\ lookup_function name fns = SOME fn ==> P fn
Proof
  simp[EVERY_MEM] >> metis_tac[lookup_function_MEM]
QED

Theorem EVERY_raw_reachable:
  !vs C fn inst s.
    raw_reachable vs C fn inst s ==>
    !P. EVERY (\fn. EVERY P (fn_insts fn)) C.ctx_functions ==>
      EVERY P (fn_insts fn) /\ P inst
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      drule_all EVERY_lookup_function >> disch_then (assume_tac o BETA_RULE) >>
      conj_tac >- simp[] >> drule_all EVERY_active_inst >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      conj_tac >- simp[] >> drule_all EVERY_active_inst >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      conj_tac >- simp[] >> drule_all EVERY_active_inst >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >>
      drule_all EVERY_lookup_function >> disch_then (assume_tac o BETA_RULE) >>
      conj_tac >- simp[] >> drule_all EVERY_active_inst >> simp[])
QED
