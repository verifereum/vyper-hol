Theory lowerDloadExternalInputs
Ancestors
  lowerDloadExternalBackward lowerDloadResidualRead lowerDloadResidualCopy
  lowerDloadReachableDiscipline ptrDiscipline pointerConfinedDefs list pred_set
  lowerDloadProvenanceSupport lowerDloadPairedBoundary lowerDloadNormalData
  lowerDloadFrameCertificate lowerDloadRelocation lowerDloadOwnership
  lowerDloadTargetGeometry venomInst codegenRel words finite_map
  contextCodegenRel o1PassContract lowerDloadCoverageInvariant memLocDefs
  lowerDloadSharedState lowerDloadParamProducer lowerDloadOpaqueExecution
  venomExecSemantics venomState

Theorem ld_annotated_external_clean:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  ~in_revert_forward fn s ==>
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  (!a n. MEM (a,n) (source_memory_read_ranges i s) ==>
    DISJOINT tn.t_mem {q | a <= q /\ q < a+n}) /\
  (MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] ==>
    tn.t_stor = {} /\ tn.t_trans = {})
Proof
  strip_tac >> drule_all ld_annotated_taint_ok >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> irule ld_taint_operand_clean >>
      goal_assum (drule_at Any) >>
      qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
      strip_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
  strip_tac >>
  simp[taint_ok_def, about_to_revert_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Single occurrence is essential: an operand spelling may alias an address
   position, but a scalar occurrence then makes its multiplicity exceed one. *)
Theorem ld_external_scalars_not_pointer:
  ptr_use_ok P pv i /\
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  MEM op i.inst_operands /\
  (FILTER ($= op) i.inst_operands = [op] ==>
    !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
      ops.iao_ofst <> op) ==>
  !v. op = Var v ==> v NOTIN pv
Proof
  strip_tac >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `ptr_use_ok P pv i` mp_tac >>
  pure_rewrite_tac[ptr_use_ok_def] >>
  disch_then (mp_tac o CONJUNCT2) >> disch_then (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem ld_annotated_external_scalar:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  ~in_revert_forward fn s /\ ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  MEM op i.inst_operands /\
  (FILTER ($= op) i.inst_operands = [op] ==>
    !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by
    (rpt strip_tac >> drule_all ld_external_scalars_not_pointer >> simp[]) >>
  `ld_op_prov AG op = NONE` by metis_tac[ld_annotated_scalar_prov] >>
  drule_all ld_annotated_external_clean >> strip_tac >>
  irule ld_owned_operand_clean >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_normal_external_read:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  ~in_revert_forward fn s /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  mem_read_ops i = SOME ops /\ MEM ops.iao_ofst i.inst_operands /\
  (!v. ops.iao_ofst = Var v ==> v IN U) /\
  MEM (w2n p,n) (source_memory_read_ranges i s) /\
  eval_operand ops.iao_ofst s = SOME p /\
  eval_operand ops.iao_ofst t = SOME q ==>
  venomState$read_memory (w2n p) n s = venomState$read_memory (w2n q) n t
Proof
  strip_tac >>
  drule_all ld_annotated_external_clean >> strip_tac >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (rpt strip_tac >>
     `owner IN live` by metis_tac[] >> simp[] >>
     `?bt. ld_site_entry E owner bs bt sz` by
       (qpat_x_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
        simp[ld_owned_selection_def] >> metis_tac[]) >> metis_tac[]) >>
  `!j. j < n ==>
    ((w2n p+j = w2n q+j /\ w2n p+j < lo) \/
      ld_site_bytes E live (w2n p+j) (w2n q+j))` by
    (mp_tac ld_owned_read_range_geometry >> asm_rewrite_tac[] >>
     impl_tac >- (metis_tac[ld_annotated_access_ok]) >> simp[]) >>
  irule ld_byte_rel_clean_read_memory >>
  qexistsl_tac [`(\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)`,
    `tn.t_mem`,`un.t_mem`] >> simp[] >>
  conj_tac >- (gvs[arithmeticTheory.ADD_COMM]) >>
  drule ld_normal_data_memory >> simp[]
QED

Theorem ld_external_layout_scalars:
  ((i.inst_opcode = CALL /\
      i.inst_operands = [g;a;v;off;sz;ro;rs] /\ scalars = [g;a;v;sz;rs]) \/
   (MEM i.inst_opcode [STATICCALL;DELEGATECALL] /\
      i.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz;rs]) \/
   (i.inst_opcode = CREATE /\
      i.inst_operands = [v;off;sz] /\ scalars = [v;sz]) \/
   (i.inst_opcode = CREATE2 /\
      i.inst_operands = [v;off;sz;salt] /\ scalars = [v;sz;salt])) ==>
  !op. MEM op scalars ==>
    MEM op i.inst_operands /\
    (FILTER ($= op) i.inst_operands = [op] ==>
      !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
        ops.iao_ofst <> op)
Proof
  strip_tac >> rpt strip_tac >>
  gvs[Excl "FILTER", MEM, mem_read_ops_def, mem_write_ops_def] >>
  rpt strip_tac >> gvs[Excl "FILTER"] >>
  qpat_x_assum `FILTER _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [FILTER] >> rpt IF_CASES_TAC >> simp[]
QED

(* Normal data supplies the oracle environment and operand definedness; the
   scalar test is discharged once by ld_external_layout_scalars. *)
Theorem ld_normal_external_operands:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  ~in_revert_forward fn s /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  (!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  (!op. MEM op i.inst_operands /\
    (FILTER ($= op) i.inst_operands = [op] ==>
      !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
        ops.iao_ofst <> op) ==> eval_operand op s = eval_operand op t) /\
  ld_shared_state tn un s t /\
  s.vs_outcomes = t.vs_outcomes /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (MEM i.inst_opcode [DELEGATECALL; CREATE; CREATE2] ==>
    tn.t_stor = {} /\ tn.t_trans = {})
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN U` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule_all ld_annotated_external_clean >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  rpt conj_tac >> simp[]
  >- (rpt strip_tac >> irule ld_owned_operand_defined >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> irule ld_annotated_external_scalar >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_external_target_operands_defined:
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst fuel CT i t = OK t' ==>
  !op. MEM op i.inst_operands ==> ?w. eval_operand op t = SOME w
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), Excl "consume_call_outcome_eq", Excl "consume_create_outcome_eq"] >>
  rpt strip_tac >> gvs[MEM] >> metis_tac[]
QED

Theorem ld_normal_external_input_correspondence:
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
  step_inst fuel CT i t = OK t' ==>
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
    (rpt strip_tac >> drule_all ld_external_target_operands_defined >>
     strip_tac >>
     qpat_x_assum `!op. MEM op i.inst_operands ==> (eval_operand op s = NONE <=> _)`
       (qspec_then `op` mp_tac) >>
     asm_rewrite_tac[] >>
     Cases_on `eval_operand op s` >> simp[] >> metis_tac[]) >>
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
