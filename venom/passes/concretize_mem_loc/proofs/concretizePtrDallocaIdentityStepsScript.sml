Theory concretizePtrDallocaIdentitySteps
Ancestors
  concretizePtrDallocaGhostInterface lowerDloadPtrScalar
  ptrDiscipline venomState venomInst
  finite_map pred_set list words

(* Geometry is local to the queried byte.  Stores transport the mask at
   the same relative offset; MCOPY transports its pre-state source mask,
   including for overlapping copies.  No middle-band identity is assumed. *)
Theorem ptr_dalloca_identity_written:
  (!a v dstT. inst.inst_operands = [a;v] /\
     (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) /\
     eval_operand a t = SOME dstT ==>
     ?dst. eval_operand a s = SOME dst /\
       op_taint un v SUBSET op_taint tn v /\
       (!k. i = w2n dstT + k /\ k IN op_taint un v ==>
            i = w2n dst + k)) /\
  (!d r n dstT srcT szT. inst.inst_operands = [d;r;n] /\
     inst.inst_opcode = MCOPY /\ eval_operand d t = SOME dstT /\
     eval_operand r t = SOME srcT /\ eval_operand n t = SOME szT ==>
     ?dst src sz. eval_operand d s = SOME dst /\
       eval_operand r s = SOME src /\ eval_operand n s = SOME sz /\
       (!k. k < w2n szT /\ i = w2n dstT + k ==>
         k < w2n sz /\ i = w2n dst + k /\
         (w2n srcT + k IN un.t_mem ==> w2n src + k IN tn.t_mem))) ==>
  (i IN written_taint un inst t ==> i IN written_taint tn inst s)
Proof
  strip_tac >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >>
  simp[written_taint_def] >>
  namedCases_on `rest` ["", "v tail"] >> simp[written_taint_def] >>
  namedCases_on `tail` ["", "n more"] >> simp[written_taint_def]
  >- (Cases_on `inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE` >>
      simp[] >> Cases_on `eval_operand a t` >> simp[] >>
      rename1 `eval_operand a t = SOME dstT` >>
      first_x_assum (qspecl_then [`a`,`v`,`dstT`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  Cases_on `more` >> simp[] >>
  Cases_on `inst.inst_opcode = MCOPY` >> simp[] >>
  Cases_on `eval_operand a t` >> simp[] >>
  Cases_on `eval_operand v t` >> simp[] >>
  Cases_on `eval_operand n t` >> simp[] >>
  rename1 `eval_operand a t = SOME dstT` >>
  rename1 `eval_operand v t = SOME srcT` >>
  rename1 `eval_operand n t = SOME szT` >>
  gvs[] >> metis_tac[]
QED

(* The two-sided coverage condition includes clearing writes.  This is a
   local boundary stronger than an ordinary matched-step application: the
   caller supplies actual step_writes (hence external-call truncation).
   The fixed/dynamic band is selected by the caller; all geometric and
   read-mask obligations remain explicit, not hidden in a history axiom. *)
Theorem ptr_dalloca_identity_next:
  (i < lo \/ dyn <= i) /\
  (i IN un.t_mem ==> i IN tn.t_mem) /\
  (i IN range_bytes (step_writes instT t postT) <=>
   i IN range_bytes (step_writes inst s post)) /\
  t.vs_allocas = FEMPTY /\ postT.vs_allocas = t.vs_allocas /\
  s.vs_fmp = t.vs_fmp /\ post.vs_fmp = postT.vs_fmp /\
  (instT = inst \/
   (inst.inst_opcode = ALLOCA /\ instT.inst_opcode = ASSIGN)) /\
  (!a v dstT. inst.inst_operands = [a;v] /\
     (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) /\
     eval_operand a t = SOME dstT ==>
     ?dst. eval_operand a s = SOME dst /\
       op_taint un v SUBSET op_taint tn v /\
       (!k. i = w2n dstT + k /\ k IN op_taint un v ==>
            i = w2n dst + k)) /\
  (!d r n dstT srcT szT. inst.inst_operands = [d;r;n] /\
     inst.inst_opcode = MCOPY /\ eval_operand d t = SOME dstT /\
     eval_operand r t = SOME srcT /\ eval_operand n t = SOME szT ==>
     ?dst src sz. eval_operand d s = SOME dst /\
       eval_operand r s = SOME src /\ eval_operand n s = SOME sz /\
       (!k. k < w2n szT /\ i = w2n dstT + k ==>
         k < w2n sz /\ i = w2n dst + k /\
         (w2n srcT + k IN un.t_mem ==> w2n src + k IN tn.t_mem))) ==>
  (i IN (step_taint instT t postT un).t_mem ==>
   i IN (step_taint inst s post tn).t_mem)
Proof
  strip_tac >>
  `new_site_bytes t postT SUBSET new_site_bytes s post` by
    metis_tac[ptr_dalloca_fresh_bytes] >>
  `i IN written_taint un instT t ==> i IN written_taint tn inst s` by
    (Cases_on `instT = inst`
     >- (gvs[] >> strip_tac >> irule ptr_dalloca_identity_written >>
         qexistsl [`t`,`un`] >> simp[] >> metis_tac[]) >>
     `written_taint un instT t = {}` by
       (irule written_taint_opcode_exclusion >> gvs[]) >> simp[]) >>
  gvs[step_taint_def, mem_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_identity_control:
  (i IN un.t_mem ==> i IN tn.t_mem) ==>
  ((i IN (un with t_var := tvT).t_mem ==>
    i IN (tn with t_var := tv).t_mem) /\
   (i IN (entry_taint_vars fnT t un).t_mem ==>
    i IN (entry_taint_vars fn s tn).t_mem))
Proof
  simp[entry_taint_vars_def] >> strip_tac >>
  Cases_on `lookup_block t.vs_current_bb fnT.fn_blocks` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
QED
