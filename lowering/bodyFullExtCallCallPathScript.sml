(* Emission-aware checked CALL and continuation paths. *)
Theory bodyFullExtCallCallPath
Ancestors
  bodyFullExtCallFrames bodyFullExtCallGhost oracleCallOriginPtr
  bodyPtrMakeArrayEmission fragGasEmitCtrl fragGasSeqPtr
  venomExecSemantics venomInst venomState

Theorem extcall_checked_call_path:
  emit_op opc args sm = (Var out,sb) /\ fn_has_code sm sb func /\
  (opc = CALL \/ opc = STATICCALL) /\
  (args = [gas; addr; value; ao; az; ro; rz] /\ opc = CALL \/
   args = [gas; addr; ao; az; ro; rz] /\ opc = STATICCALL) /\
  inst = mk_inst sm.cs_next_id opc args [out] /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted /\
  access_ok lo G func inst s /\ taint_ok func tn inst s /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok_at D tn s /\
  inst_mem_below_frontier inst s /\ step_inst_base inst s = OK u /\ ~u.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn) /\
  sb.cs_current_bb = s.vs_current_bb /\
  LENGTH sb.cs_current_insts = SUC s.vs_inst_idx /\ ~not_fresh_at sm out
Proof
  strip_tac >> drule_all emit_op_fetch_boundary >> strip_tac >> fs[] >>
  `~not_fresh_at sm out` by metis_tac[] >> simp[] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sm.cs_next_id opc args [out]) u,
     step_taint (mk_inst sm.cs_next_id opc args [out]) s u tn)` by
    (irule call_origin_ptr_edge >> gvs[mk_inst_def] >> metis_tac[]) >>
  gvs[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >>
  irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]
QED

Theorem extcall_checked_success_path:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK v,G',tn') /\
  emit_inst JNZ [Var out; Label cont_lbl; Label fail_lbl] [] sj = ((),sk) /\
  fn_has_code sj sk func /\ ~ctx_has_dalloca ctx /\ allocas_from lo v /\
  eval_operand (Var out) v = SOME 1w /\ op_taint tn' (Var out) = {} /\
  v.vs_current_bb = sj.cs_current_bb /\
  v.vs_inst_idx = LENGTH sj.cs_current_insts /\ ~v.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to cont_lbl v),G',tn')
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G',tn') []
    (OK (jump_to cont_lbl v),G',tn')` by
    (irule (SRULE [] (Q.INST [`b` |-> `T`] (SPEC_ALL emit_jnz_origin_ptr))) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem extcall_checked_oracle_call:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas; addr; ao; az; ro; rz]
     else [gas; addr; value; ao; az; ro; rz]) sm = (Var out,sb) /\
  fn_has_code sm sb func /\
  inst = mk_inst sm.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas; addr; ao; az; ro; rz]
     else [gas; addr; value; ao; az; ro; rz]) [out] /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME dw /\
  eval_operand value s = SOME vw /\ eval_operand ao s = SOME aw /\
  eval_operand az s = SOME an /\ eval_operand ro s = SOME rw /\
  eval_operand rz s = SOME rn /\
  exec_ext_call inst s gw dw (if stat then 0w else vw) aw an rw rn stat = OK u /\
  access_ok lo G func inst s /\ taint_ok func tn inst s /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok_at D tn s /\
  inst_mem_below_frontier inst s ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn) /\
  sb.cs_current_bb = s.vs_current_bb /\
  LENGTH sb.cs_current_insts = SUC s.vs_inst_idx /\
  ~not_fresh_at sm out /\ ~u.vs_halted
Proof
  strip_tac >>
  `~u.vs_halted` by
    metis_tac[venomStepPropsTheory.exec_ext_call_ok_halted] >> simp[] >>
  `step_inst_base inst s = OK u` by
    (mp_tac (Q.INST [`inst` |-> `inst`, `s` |-> `s`, `stat` |-> `stat`]
       (SPEC_ALL oracleCallStepPtrTheory.call_step_exec_ext_call)) >>
     Cases_on `stat` >> gvs[mk_inst_def] >> metis_tac[]) >>
  Cases_on `stat` >> fs[] >> metis_tac[extcall_checked_call_path]
QED

Theorem extcall_call_result_observations:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  inst.inst_outputs = [out] ==>
  eval_operand (Var out) (next_inst (update_var out (if success then 1w else 0w) u)) =
    SOME (if success then 1w else 0w) /\
  op_taint (step_taint inst s (update_var out (if success then 1w else 0w) u) tn)
    (Var out) = {}
Proof
  strip_tac >>
  simp[eval_operand_def, next_inst_def, update_var_def, lookup_var_def] >>
  fs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.op_taint_def,
     ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
     ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt CASE_TAC >> simp[]
QED
