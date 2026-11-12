Theory lowerDloadStoreCertificate
Ancestors
  lowerDloadCertificateProbe lowerDloadMaskBounds
  lowerDloadFrameCertificate lowerDloadTargetGeometry lowerDloadOwnership
  lowerDloadAllocation ptrDiscipline venomExecSemantics venomState finite_map pred_set

(* A normal-mode local MSTORE boundary. No temporal alignment or completed
   source execution is assumed or produced. Only memory changes. *)
Theorem ld_mstore_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst;value] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN U) /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\ ld_stack_bound t.vs_alloca_next gstk /\
  lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\ un.t_imm SUBSET tn.t_imm /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ld_frame_embedding E L H s' t' /\ ld_alloc_account keys d A s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    d = 32 * SUM (MAP CARD suspended) /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_step_prov BP BH H i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\
    lo <= f /\ allocas_from f t' /\ f <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\ bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(bt,sz)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >> drule_all ld_reachable_mstore_state_backward >>
  disch_then (qspec_then `BP` (qx_choose_then `s'` (qx_choose_then `x`
    (qx_choose_then `v` (qx_choose_then `y` (qx_choose_then `w` strip_assume_tac)))))) >>
  qpat_x_assum `!v. op_taint tn (Var v) SUBSET count 32` mp_tac >>
  disch_then (assume_tac o SRULE [op_taint_def]) >>
  qpat_x_assum `!v. op_taint un (Var v) SUBSET count 32` mp_tac >>
  disch_then (assume_tac o SRULE [op_taint_def]) >>
  qexists_tac `s'` >> asm_rewrite_tac[] >>
  simp[ld_empty_outputs_prov_tvar, mstore_def] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >- (qpat_x_assum `allocas_from f t` mp_tac >> simp[allocas_from_def]) >>
  simp[op_taint_def, ld_empty_outputs_prov_tvar,
       step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       set_var_taint_def, DRESTRICT_UNIV] >>
  asm_rewrite_tac[]
QED
