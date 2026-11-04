(* Reachable source obligations exposed to ordinary effect consumers. *)
Theory lowerDloadSafetyAssemblyPremises
Ancestors
  lowerDloadSafetyRelation ptrDiscipline

Theorem ld_sync_access_ok:
  ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  access_ok lo G fn inst s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_sync_taint_ok:
  ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  taint_ok fn tn inst s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_copy_byte_store_operands_untainted:
  taint_ok fn tn inst s /\
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = MSTORE8) /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  simp[taint_ok_def] >> rpt strip_tac >>
  spose_not_then assume_tac >> res_tac >> gvs[]
QED

(* Width audit (C1.11.5.35), not a proved invariant:
   ptrDisciplineScript.sml:239-249 initializes the variable masks to FEMPTY
   and reads them through op_taint.  mem_word_taint/key_taint (252-258) and
   shift_taint (319-329) explicitly restrict results to j<32; out_taint
   (332-354) additionally forwards ASSIGN's input mask.  set_var_taint and
   step_taint (356-361,403-412) update one output or restrict the old map.
   PHIs (415-437) copy masks from the pre-block state in parallel.

   The exact sufficient reachability invariant to prove separately is:
     frame_reachable vs0 C stk PG G tn fn inst s ==>
       (!v m. FLOOKUP tn.t_var v = SOME m ==>
               m SUBSET {j | j < 32}) /\
       (!f v m. MEM f stk /\ FLOOKUP f.cf_tvar v = SOME m ==>
                  m SUBSET {j | j < 32}).
   The saved-frame conjunct is needed by the ret rule (486-499), which
   restores a DRESTRICT of cf_tvar.  Calls save the current bounded map
   and clear callee t_var; entry starts empty.  The ordinary and block
   rules need out_taint/set_var_taint and parallel-PHI preservation.
   From its current-map conjunct, Cases_on op and op_taint_def give the
   mask bound required by MSTORE.  taint_within supplies no such bound.
   No width theorem or call-stack induction is asserted in this theory.
*)
