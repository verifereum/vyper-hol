Theory requestCutDloadOperands
Ancestors
  lowerDloadExternalInputs
  lowerDloadExternalBackward lowerDloadResidualRead lowerDloadResidualCopy
  lowerDloadReachableDiscipline ptrDiscipline pointerConfinedDefs list pred_set
  lowerDloadProvenanceSupport lowerDloadPairedBoundary lowerDloadNormalData
  lowerDloadFrameCertificate lowerDloadRelocation lowerDloadOwnership
  lowerDloadTargetGeometry venomInst codegenRel words finite_map
  contextCodegenRel o1PassContract lowerDloadCoverageInvariant memLocDefs
  lowerDloadSharedState lowerDloadParamProducer lowerDloadOpaqueExecution
  venomExecSemantics venomState

Theorem ld_normal_external_inputs_defined:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ((i.inst_opcode = CALL /\
      i.inst_operands = [g;a;v;off;sz;ro;rs] /\ scalars = [g;a;v;sz;rs]) \/
   (MEM i.inst_opcode [STATICCALL;DELEGATECALL] /\
      i.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz;rs]) \/
   (i.inst_opcode = CREATE /\
      i.inst_operands = [v;off;sz] /\ scalars = [v;sz]) \/
   (i.inst_opcode = CREATE2 /\
      i.inst_operands = [v;off;sz;salt] /\ scalars = [v;sz;salt])) /\
  ~in_revert_forward fn s /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (!op. MEM op i.inst_operands ==> ?w. eval_operand op t = SOME w) ==>
  (!op. MEM op scalars ==> eval_operand op s = eval_operand op t) /\
  (!op. MEM op i.inst_operands ==> ?x y.
    eval_operand op s = SOME x /\ eval_operand op t = SOME y) /\
  ?p q n. eval_operand off s = SOME p /\ eval_operand off t = SOME q /\
    eval_operand sz s = SOME n /\ eval_operand sz t = SOME n /\
    read_memory (w2n p) (w2n n) s = read_memory (w2n q) (w2n n) t
Proof
  strip_tac >>
  `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by gvs[MEM] >>
  drule_all ld_normal_external_operands >> strip_tac >>
  `!op. MEM op scalars ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `MEM op i.inst_operands /\
       (FILTER ($= op) i.inst_operands = [op] ==>
        !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
          ops.iao_ofst <> op)` by
       (mp_tac ld_external_layout_scalars >>
        (impl_tac >- simp[]) >>
        disch_then (qspec_then `op` mp_tac) >>
        asm_rewrite_tac[]) >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> ?x y.
    eval_operand op s = SOME x /\ eval_operand op t = SOME y` by
    (rpt strip_tac >>
     qpat_assum `!op. MEM op i.inst_operands ==> ?w. eval_operand op t = SOME w`
       (qspec_then `op` (drule_then strip_assume_tac)) >>
     qpat_assum `!op. MEM op i.inst_operands ==> (eval_operand op s = NONE <=> _)`
       (qspec_then `op` (drule_then assume_tac)) >>
     Cases_on `eval_operand op s` >> fs[]) >>
  simp[] >>
  `?p q n. eval_operand off s = SOME p /\ eval_operand off t = SOME q /\
    eval_operand sz s = SOME n /\ eval_operand sz t = SOME n` by
    (`MEM off i.inst_operands /\ MEM sz i.inst_operands /\ MEM sz scalars`
       by gvs[MEM] >>
     qpat_assum `!op. MEM op i.inst_operands ==> ?x y. _`
       (qspec_then `off` mp_tac) >>
     qpat_assum `!op. MEM op i.inst_operands ==> ?x y. _`
       (qspec_then `sz` mp_tac) >>
     qpat_assum `!op. MEM op scalars ==> _`
       (qspec_then `sz` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qexistsl [`p`,`q`,`n`] >> simp[] >>
  irule ld_normal_external_read >>
  goal_assum (drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `THE (mem_read_ops i)` >>
  qpat_x_assum `U = _` kall_tac >>
  `!v. off = Var v ==> v IN U` by
    (qx_gen_tac `z` >> strip_tac >>
     qpat_assum `!v. MEM (Var v) i.inst_operands ==> v IN U`
       (qspec_then `z` mp_tac) >>
     asm_rewrite_tac[] >> simp[MEM]) >>
  qpat_x_assum `!op. MEM op i.inst_operands ==> (eval_operand op s = NONE <=> _)` kall_tac >>
  qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
  qpat_x_assum `!op. MEM op scalars ==> _` kall_tac >>
  qpat_x_assum `!op. MEM op i.inst_operands ==> ?x y. _` mp_tac >>
  asm_rewrite_tac[] >> simp[MEM, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  qpat_x_assum `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` kall_tac >>
  TRY (qpat_x_assum `MEM i.inst_opcode [STATICCALL;DELEGATECALL]` mp_tac >>
       simp_tac bool_ss [MEM] >> strip_tac) >>
  simp[mem_read_ops_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, MEM] >>
  metis_tac[]
QED
