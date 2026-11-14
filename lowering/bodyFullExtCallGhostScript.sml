(* CALL/STATICCALL pointer checks and exact ghost effects at any floor. *)
Theory bodyFullExtCallGhost
Ancestors
  oracleCallOriginPtr oracleCallStepPtr memSafeRun
  bodyPtrEnvBuiltinsEdges bodyPtrBopRepresentationFrame
  decoderGhostFramePtr bodyPtrDefs ptrDiscipline
  unitTransformDefs contextCodegenRel codegenRel
  venomState venomInst venomExecSemantics finite_map
  pred_set words

Theorem extcall_call_storage_ghost:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  stor_taint_ok_at D tn s /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_immutables = s.vs_immutables /\
  (~(inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
      u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) ==>
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient) ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
    u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success` >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >> metis_tac[]
QED

Theorem extcall_call_pointer_conditions:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME rn /\
  (an <> 0w ==> ?p b sz. ao = Var p /\ FLOOKUP G p = SOME (b,sz) /\
                          b <= w2n aw /\ w2n aw + w2n an <= b + sz) /\
  (rn <> 0w ==> ?p b sz. ro = Var p /\ FLOOKUP G p = SOME (b,sz) /\
                          b <= w2n rw /\ w2n rw + w2n rn <= b + sz) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!i. w2n aw <= i /\ i < w2n aw + w2n an ==> i NOTIN tn.t_mem) /\
  (an <> 0w ==> w2n aw + w2n an <= s.vs_alloca_next) /\
  (rn <> 0w ==> w2n rw + w2n rn <= s.vs_alloca_next) /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  inst_mem_below_frontier inst s /\ allocas_from lo s /\
  stor_taint_ok_at D tn s
Proof
  strip_tac >>
  `access_ok 0 G fn inst s` by
    (irule call_access_ok_ptr >> metis_tac[]) >>
  `access_ok lo G fn inst s` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
      off <= i /\ i < off + len ==> i NOTIN tn.t_mem` by
    (Cases_on `eval_operand gas s` >> Cases_on `eval_operand addr s` >>
     Cases_on `eval_operand value s` >>
     gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
     metis_tac[]) >>
  `taint_ok fn tn inst s` by (irule call_taint_ok_ptr >> metis_tac[]) >>
  fs[ghost_inv_at_def] >>
  Cases_on `eval_operand gas s` >> Cases_on `eval_operand addr s` >>
  Cases_on `eval_operand value s` >>
  gvs[inst_mem_below_frontier_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, memory_range_of_operands_def] >>
  metis_tac[wordsTheory.w2n_eq_0]
QED

(* No new sites are allocated.  Only the returned prefix loses memory taint;
   all old variables except the success result retain their ghost entries. *)
Theorem extcall_call_ghost_frame:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  inst.inst_outputs = [out] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME dw /\
  (inst.inst_opcode = CALL ==> eval_operand value s = SOME vw) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME rn /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  step_prov PG G inst u = DRESTRICT G (COMPL {out}) /\
  (step_taint inst s u tn).t_mem =
    tn.t_mem DIFF {i | w2n rw <= i /\
      i < w2n rw + MIN (w2n rn) (LENGTH u.vs_returndata)} /\
  (step_taint inst s u tn).t_var = tn.t_var |+ (out,{}) /\
  (step_taint inst s u tn).t_imm = tn.t_imm /\
  (!x. x <> out ==>
    FLOOKUP (step_prov PG G inst u) x = FLOOKUP G x /\
    op_taint (step_taint inst s u tn) (Var x) = op_taint tn (Var x)) /\
  (step_taint inst s u tn).t_mem SUBSET tn.t_mem /\
  (!lo cenv es sa G0 tn0 s0.
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ ~not_fresh_at sa out ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0
      (step_prov PG G inst u) (step_taint inst s u tn))
Proof
  strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss] >>
  gvs[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      mem_taint_def, step_writes_def, written_taint_def,
      source_memory_write_ranges_def, memory_range_of_operands_def,
      set_var_taint_def, out_taint_def, imm_taint_def,
      range_bytes_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[SUBSET_DEF] >>
  simp[ghost_kept_at_def, FLOOKUP_DRESTRICT, op_taint_def,
       FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Protected defaults need only their actual value footprint framed, not an
   assertion that the entire CALL output buffer is disjoint from all memory. *)
Theorem extcall_call_protected_default:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  inst.inst_outputs = [out] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME dw /\
  (inst.inst_opcode = CALL ==> eval_operand value s = SOME vw) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME rn /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
  ptr_mem_ok cx ty dv default_op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv dv /\
  (!x. default_op = Var x ==> x <> out) /\
  eval_operand default_op u = eval_operand default_op s /\
  (!w. eval_operand default_op s = SOME w ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) u.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv dv) s.vs_memory) ==>
  ptr_mem_ok cx ty dv default_op (step_prov PG G inst u)
    (step_taint inst s u tn) u
Proof
  strip_tac >>
  `(step_taint inst s u tn).t_mem SUBSET tn.t_mem` by
    (irule (cj 6 extcall_call_ghost_frame) >> metis_tac[]) >>
  irule bop_ptr_mem_ok_frame >> simp[] >>
  qexistsl_tac [`G`, `s`, `tn`] >>
  simp[step_prov_other_output] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED
