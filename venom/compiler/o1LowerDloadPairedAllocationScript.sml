(* Operational allocation boundaries shared by the LowerDload simulation. *)
Theory o1LowerDloadPairedAllocation
Ancestors
  venomExecSemantics venomState finite_map words

(* Allocation boundary equations: no memory is initialized by ALLOCA. *)
Theorem lower_dload_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s amount =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                    (inst.inst_id, (s.vs_alloca_next, w2n amount));
                vs_alloca_next := s.vs_alloca_next + w2n amount|>))
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (addr,sz) ==>
  exec_alloca inst s amount = OK (update_var out (n2w addr) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_merge_allocation_memory:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next /\
  (merge_callee_state caller callee).vs_memory = callee.vs_memory
Proof
  simp[venomExecSemanticsTheory.merge_callee_state_def]
QED

Theorem lower_dload_frontier_credit_bound:
  !n m k q. m = n + 32*k /\ k <= q /\
    n + 32*q < dimword (:256) ==> m < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem lower_dload_frontier_credit_step:
  !n m k a:num. m = n + 32*k ==>
    m+a = (n+a) + 32*k /\ m+32 = n + 32*(k+1)
Proof
  rpt strip_tac >> decide_tac
QED

(* One effect equation covers fresh, repeated and target-only scratch sites. *)
Theorem lower_dload_alloca_frontier:
  exec_alloca inst s amount = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next +
    (if FLOOKUP s.vs_allocas inst.inst_id = NONE then w2n amount else 0)
Proof
  Cases_on `inst.inst_outputs` >>
  simp[venomExecSemanticsTheory.exec_alloca_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[venomStateTheory.update_var_def] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[venomStateTheory.update_var_def] >>
  strip_tac >> gvs[]
QED

Theorem lower_dload_alloca_credit:
  exec_alloca i s (amount:bytes32) = OK t /\
  exec_alloca j s' amount = OK t' /\
  (FLOOKUP s.vs_allocas i.inst_id = NONE <=>
   FLOOKUP s'.vs_allocas j.inst_id = NONE) /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = t.vs_alloca_next + 32*k
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca i _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  qpat_x_assum `exec_alloca j _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id = NONE` >> gvs[] >> decide_tac
QED

Theorem lower_dload_scratch_credit:
  exec_alloca i s' (32w:bytes32) = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = NONE /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = s.vs_alloca_next + 32*(k+1)
Proof
  strip_tac >> drule lower_dload_alloca_frontier >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  simp[] >> strip_tac >> decide_tac
QED

Theorem lower_dload_merge_credit:
  caller'.vs_alloca_next = caller.vs_alloca_next + 32*k /\
  R caller.vs_allocas caller'.vs_allocas ==>
  (merge_callee_state caller' callee').vs_alloca_next =
    (merge_callee_state caller callee).vs_alloca_next + 32*k /\
  R (merge_callee_state caller callee).vs_allocas
    (merge_callee_state caller' callee').vs_allocas
Proof
  simp[lower_dload_merge_allocation_memory]
QED

(* Metadata and returned pointers, with independent source/target bases. *)
Theorem lower_dload_paired_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  t.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  ?s1 t1.
    exec_alloca inst s z = OK s1 /\ exec_alloca inst t z = OK t1 /\
    s1.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n z)) /\
    t1.vs_allocas = t.vs_allocas |+ (inst.inst_id,(t.vs_alloca_next,w2n z)) /\
    s1.vs_alloca_next = s.vs_alloca_next + w2n z /\
    t1.vs_alloca_next = t.vs_alloca_next + w2n z /\
    t1.vs_alloca_next = s1.vs_alloca_next + 32*k /\
    FLOOKUP s1.vs_vars out = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP t1.vs_vars out = SOME (n2w t.vs_alloca_next)
Proof
  strip_tac >> imp_res_tac lower_dload_alloca_fresh >>
  simp[update_var_def, FLOOKUP_UPDATE] >> decide_tac
QED

Theorem lower_dload_paired_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (c,sz) /\
  t.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  ?s1 t1.
    exec_alloca inst s z = OK s1 /\ exec_alloca inst t z = OK t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\
    t1.vs_alloca_next = t.vs_alloca_next /\
    t1.vs_alloca_next = s1.vs_alloca_next + 32*k /\
    FLOOKUP s1.vs_vars out = SOME (n2w b) /\
    FLOOKUP t1.vs_vars out = SOME (n2w c)
Proof
  strip_tac >> imp_res_tac lower_dload_alloca_repeated >> simp[update_var_def, FLOOKUP_UPDATE]
QED

(* ALLOCA accepts a literal, rather than an arbitrary evaluated operand. *)
Theorem lower_dload_step_alloca:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit z] ==>
  step_inst fuel C inst s = exec_alloca inst s z
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
