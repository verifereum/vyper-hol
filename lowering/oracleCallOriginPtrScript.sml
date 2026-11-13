(*
 * A CALL or STATICCALL step as a counted pointer-checked origin edge at
 * any dead-state map D and allocation floor lo: the (D, lo) form of
 * oracleCallStepPtr's call_gas_path_ptr_edge, which is stated at
 * (cx_dead H cx, 0).
 *
 * TOP-LEVEL:
 *   call_origin_ptr_edge
 *)
Theory oracleCallOriginPtr
Ancestors
  oracleCallStepPtr fragGasSeqPtr fragGasOriginPtr bodyPtrDefs ptrSafeRun
  ptrDiscipline memSafeRun venomExecSemantics venomInst venomState

Theorem call_origin_ptr_edge:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok_at D tn s /\
  inst_mem_below_frontier inst s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u ==>
  gas_origin_ptr_edge (D, lo, explicit, ctx, fn, PG) (s, G, tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn inst s` by
    (gvs[ptr_inst_ok_def, stor_taint_ok_at_def] >>
     metis_tac[call_step_not_Halt]) >>
  `inst_dload_in_section inst s` by
    gvs[inst_dload_in_section_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS` by
    gvs[is_terminator_def] >>
  drule_all straight_line_origin_ptr_edge >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[]
QED
