(* Ambient actual-site credit at instruction and sequential execution boundaries. *)
Theory entryReachBodyScratchExecution
Ancestors
  entryReachBodyScratchSet actualAllocExec fragExec venomExecSemantics
  venomState exprLoweringProps finite_map words arithmetic list

Theorem entry_scratch_ready_update_var[simp]:
  entry_scratch_ready sites b cap (update_var out w s) <=>
  entry_scratch_ready sites b cap s
Proof
  simp[entry_scratch_ready_def, entry_scratch_missing_def, update_var_def]
QED

Theorem entry_scratch_alloca_fresh[local]:
  entry_scratch_ready sites b cap s /\ inst.inst_id IN sites /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  ?t. exec_alloca inst s (32w:bytes32) = OK t /\
    entry_scratch_ready sites b cap t /\
    lookup_var out t = SOME (n2w s.vs_alloca_next) /\
    b <= s.vs_alloca_next /\ s.vs_alloca_next+32 <= b+cap
Proof
  strip_tac >> drule_all entry_scratch_ready_fresh >> strip_tac >>
  simp[exec_alloca_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  conj_tac >-
    (irule entry_scratch_ready_insert >> qexistsl_tac [`inst.inst_id`, `s`] >>
     simp[]) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  fs[entry_scratch_ready_def]
QED

Theorem entry_scratch_alloca_step:
  entry_scratch_ready sites b cap s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN sites /\ b+cap < dimword (:256) ==>
  ?t p. step_inst_base inst s = OK t /\ entry_scratch_ready sites b cap t /\
    lookup_var out t = SOME (n2w p) /\ b <= p /\ p+32 <= b+cap
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all entry_scratch_alloca_fresh >> strip_tac >>
      qexistsl_tac [`t`, `s.vs_alloca_next`] >>
      simp[step_inst_base_def]) >>
  PairCases_on `x` >> drule_all entry_scratch_ready_existing >> strip_tac >>
  qexistsl_tac [`update_var out (n2w x0) s`, `x0`] >>
  simp[step_inst_base_def, exec_alloca_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, entry_scratch_ready_def, entry_scratch_missing_def]
QED

Theorem entry_scratch_step_frame:
  entry_scratch_ready sites b cap s /\ step_inst_base inst s = OK t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  entry_scratch_ready sites b cap t
Proof
  metis_tac[entry_scratch_ready_frame]
QED

Theorem entry_scratch_sequence:
  (!inst. MEM inst insts /\ inst.inst_opcode = ALLOCA ==>
     inst.inst_operands = [Lit 32w] /\
     (?out. inst.inst_outputs = [out]) /\ inst.inst_id IN sites) /\
  (!inst u v. MEM inst insts /\ inst.inst_opcode <> ALLOCA /\
     step_inst_base inst u = OK v ==>
     v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next) /\
  entry_scratch_ready sites b cap s /\ b+cap < dimword (:256) /\
  run_inst_seq insts s = OK t ==>
  entry_scratch_ready sites b cap t
Proof
  qid_spec_tac `s` >> Induct_on `insts` >> simp[run_inst_seq_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `step_inst_base h s = OK u` >>
  `entry_scratch_ready sites b cap u` by
    (Cases_on `h.inst_opcode = ALLOCA`
     >- (qpat_assum `!inst. _ ==> inst.inst_operands = _ /\ _` (qspec_then `h` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
         drule_all entry_scratch_alloca_step >> strip_tac >> gvs[]) >>
     irule entry_scratch_step_frame >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  first_x_assum irule >> conj_tac >- metis_tac[] >>
  qexists_tac `u` >> simp[]
QED
