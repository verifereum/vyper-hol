Theory lowerDloadBytesProducer
Ancestors
  lowerDloadBytesMemory lowerDloadBytesEffects lowerDloadCertificateProbe
  lowerDloadMacroBoundary lowerDloadOwnership lowerDloadBytesScalar
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline pointerConfinedDefs
  contextCodegenRel lowerDloadRelocation o1PassContract memLocDefs codegenRel
  lowerDloadMaskBounds lowerDloadVariableTransport
  lowerDloadFrameCertificate lowerDloadAllocation lowerDloadPairedBoundary
  venomExecSemantics venomState venomInst ptrDiscipline finite_map list pred_set

(* Source DLOADBYTES changes memory only. This boundary deliberately does not
   claim an aligned annotated successor (the execution layer owns alignment). *)
Theorem ld_bytes_source_nonmemory:
  inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dst;off;sz] /\
  step_inst fuel C inst s = OK z ==>
  (z with vs_memory := s.vs_memory) = s
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def]
QED

Theorem ld_bytes_completed_nonmemory:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  (t with <|vs_memory := t0.vs_memory; vs_vars := t0.vs_vars;
            vs_inst_idx := t0.vs_inst_idx|>) = t0
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def,
       update_var_def]
QED

(* One implementation boundary for original-name values and nonmemory taints. *)
Theorem ld_bytes_structural_values:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  inst.inst_outputs = [] /\ step_inst fuel CS inst s = OK z /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  av NOTIN V /\ ld_owned_vars V E AG BH tn u0 s t0 ==>
  ld_owned_vars V E AG BH (step_taint inst s z tn) u z t /\
  (!v. v IN V ==> lookup_var v z = lookup_var v s /\
                    lookup_var v t = lookup_var v t0) /\
  (step_taint inst s z tn).t_stor = tn.t_stor /\
  (step_taint inst s z tn).t_trans = tn.t_trans /\
  (step_taint inst s z tn).t_imm = tn.t_imm /\
  u.t_stor = u0.t_stor /\ u.t_trans = u0.t_trans /\ u.t_imm = u0.t_imm
Proof
  strip_tac >>
  drule_all ld_bytes_source_nonmemory >> strip_tac >>
  drule_all ld_bytes_completed_taint_effects >> strip_tac >>
  drule_all ld_bytes_completed_projections >> strip_tac >>
  `z = s with vs_memory := z.vs_memory` by
    (qpat_x_assum `z with vs_memory := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum `z = s with vs_memory := _` SUBST1_TAC >>
  gvs[ld_owned_vars_def, lookup_var_def, update_var_def, op_taint_def,
      step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, FLOOKUP_UPDATE, DRESTRICT_UNIV] >>
  metis_tac[]
QED

Theorem ld_bytes_structural_allocations:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  step_inst fuel CS inst s = OK z /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  ld_frame_embedding E L H s t0 /\ ld_alloc_account keys d A s t0 ==>
  ld_frame_embedding E L H z t /\ ld_alloc_account keys d A z t /\
  z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
  t.vs_allocas = t0.vs_allocas /\ t.vs_alloca_next = t0.vs_alloca_next /\
  z.vs_params = s.vs_params /\ t.vs_params = t0.vs_params
Proof
  strip_tac >> drule_all ld_bytes_source_nonmemory >> strip_tac >>
  drule_all ld_bytes_completed_projections >> strip_tac >>
  drule_all ld_bytes_completed_params >> strip_tac >>
  qpat_x_assum `z with vs_memory := _ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  gvs[ld_frame_embedding_def, ld_alloc_account_def]
QED

Theorem ld_bytes_provenance:
  inst.inst_outputs = [] /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\ c.inst_outputs = [] /\
  ld_op_prov BH off = NONE /\ av NOTIN FDOM BH ==>
  ld_step_prov AP AG L inst = AG /\
  ld_step_prov BP (ld_step_prov BP BH H a) H c = BH
Proof
  simp[ld_step_prov_def, ld_out_prov_def, ld_set_prov_def,
       ld_first_prov_def, ld_op_prov_def, DRESTRICT_UNIV] >>
  strip_tac >> simp[fmap_EXT, FDOM_DRESTRICT, DRESTRICT_DEF, EXTENSION] >>
  metis_tac[]
QED

Theorem ld_bytes_reachable_target_scalar:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) ==>
  ld_op_prov BH off = NONE
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by
    (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  drule_all ld_bytes_scalars_not_pointer >> strip_tac >>
  `ld_op_prov AG off = NONE` by metis_tac[ld_annotated_scalar_prov] >>
  Cases_on `off` >> gvs[ld_op_prov_def] >>
  qpat_x_assum `!v. ld_owned_selection _ _ _` (qspec_then `s'` mp_tac) >>
  simp[ld_owned_selection_def]
QED

(* Local backward production: source success is produced by the memory lemma,
   not supplied as a hypothesis. The original-name support U may exclude the
   opaque return-PC values; definedness still uses the full V. *)
Theorem ld_bytes_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  inst.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars U E AG BH tn u0 s t0 /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN U) /\
  (!v owner bs size. FLOOKUP AG v = SOME(owner,(bs,size)) ==> owner IN live) /\
  (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
    lo <= bs /\ lo <= bt /\ bs+size < dimword(:256) /\
    bt+size < dimword(:256)) /\
  (!owner other bs bt size cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt size /\ ld_site_entry E other cs ct cz ==>
    (bs+size <= cs \/ cs+cz <= bs) /\ (bt+size <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem u0.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t0) /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  dload_offset_ok CS fn inst s /\ av NOTIN U /\ av NOTIN V /\
  ld_frame_embedding E L H s t0 /\ ld_alloc_account keys d A s t0 /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  av NOTIN FDOM BH /\
  ld_frame_bound t0.vs_alloca_next H BP BH /\
  ld_stack_bound t0.vs_alloca_next gstk /\ lo <= t0.vs_alloca_next /\
  (!owner bs size. ld_live astk L AP AG (owner,(bs,size)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
    bs+size <= s.vs_alloca_next /\ bt+size <= t0.vs_alloca_next) /\
  (!owner bs bt size. ld_live astk L AP AG (owner,(bs,size)) /\
    ld_site_entry E owner bs bt size ==>
    bt+size <= f \/ ?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME(bt,size)) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint u0 (Var v) SUBSET count 32) /\
  u0.t_stor SUBSET tn.t_stor /\ u0.t_trans SUBSET tn.t_trans /\
  u0.t_imm SUBSET tn.t_imm ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint inst s z tn).t_mem u.t_mem
      (\a. read_memory a 1 z) (\b. read_memory b 1 t) /\
    ld_owned_vars U E AG BH (step_taint inst s z tn) u z t /\
    ld_frame_embedding E L H z t /\ ld_alloc_account keys d A z t /\
    ld_step_prov AP AG L inst = AG /\
    ld_step_prov BP (ld_step_prov BP BH H a) H c = BH /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
    ld_frame_bound t.vs_alloca_next H BP BH /\
    ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next /\
    (!owner bs size. ld_live astk L AP AG (owner,(bs,size)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
      lo <= bs /\ lo <= bt /\ bs+size <= z.vs_alloca_next /\
      bt+size <= t.vs_alloca_next) /\
    (!owner other bs bt size cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt size /\ ld_site_entry E other cs ct cz ==>
      (bs+size <= cs \/ cs+cz <= bs) /\ (bt+size <= ct \/ ct+cz <= bt)) /\
    (!owner bs bt size. ld_live astk L AP AG (owner,(bs,size)) /\
      ld_site_entry E owner bs bt size ==>
      bt+size <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,size)) /\
    (!v. v IN V ==> (lookup_var v z = NONE <=> lookup_var v t = NONE)) /\
    (!v. op_taint (step_taint inst s z tn) (Var v) SUBSET count 32) /\
    (!v. op_taint u (Var v) SUBSET count 32) /\
    u.t_stor SUBSET (step_taint inst s z tn).t_stor /\
    u.t_trans SUBSET (step_taint inst s z tn).t_trans /\
    u.t_imm SUBSET (step_taint inst s z tn).t_imm /\
    z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = t0.vs_allocas /\ t.vs_alloca_next = t0.vs_alloca_next /\
    z.vs_params = s.vs_params /\ t.vs_params = t0.vs_params /\
    (z with vs_memory := s.vs_memory) = s /\
    (t with <|vs_memory := t0.vs_memory; vs_vars := t0.vs_vars;
              vs_inst_idx := t0.vs_inst_idx|>) = t0
Proof
  strip_tac >> drule_all ld_reachable_bytes_memory >>
  disch_then (qspec_then `fuel` (qx_choose_then `z` strip_assume_tac)) >>
  drule_all ld_bytes_structural_values >> strip_tac >>
  drule_all ld_bytes_structural_allocations >> strip_tac >>
  drule_all ld_bytes_source_nonmemory >> strip_tac >>
  drule_all ld_bytes_completed_nonmemory >> strip_tac >>
  drule_all ld_bytes_reachable_target_scalar >> strip_tac >>
  drule_all ld_bytes_provenance >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  simp[ld_empty_outputs_prov_tvar] >>
  rpt conj_tac
  >- suspend "endpoints"
  >- suspend "definedness"
  >- (irule ld_step_taint_bound >> simp[])
  >- suspend "target_mask"
  >> simp[]
QED

Resume ld_bytes_certificate_backward[endpoints]:
  rpt strip_tac >> metis_tac[]
QED

Resume ld_bytes_certificate_backward[definedness]:
  rpt strip_tac >>
  `v <> av` by metis_tac[] >>
  `lookup_var v t = lookup_var v t0` by
    (irule ld_bytes_completed_lookup >>
     qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `lookup_var v z = lookup_var v s` by
    (qpat_x_assum `z with vs_memory := _ = s` (SUBST1_TAC o SYM) >>
     simp[lookup_var_def]) >>
  metis_tac[]
QED

Resume ld_bytes_certificate_backward[target_mask]:
  drule_all ld_bytes_completed_taint_effects >> strip_tac >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `av = v` >> simp[] >>
  fs[op_taint_def]
QED

Finalise ld_bytes_certificate_backward

(* Certificate audit for the complete local DLOADBYTES boundary above:
   C1 frame embedding; C2 unchanged AP/BP and AG/BH selection pairing;
   C3 owned values on U; C4 full definedness on V; C5 allocation account;
   C6 unchanged target frontier/frame/stack bounds; C7 unchanged live source
   selection; C8 natural endpoint bounds; C9 live separation; C10 masked bytes;
   C11 both variable-mask bounds; C12 the three nonmemory taint subsets.

   Actual original and macro provenance maps are proved unchanged, not assumed
   as postconditions. The fresh temporary is outside both supports and outside
   the target provenance domain. The source scalar classification derives the
   target ADD's lack of provenance, even for undefined original variables.

   E,L,H,AP,BP,keys,A,d,astk,gstk and the frame floor f are unchanged: hence
   all saved-table snapshot agreement and saved-frame/support/count clauses
   remain literally the pre-state clauses. Current representation at f is an
   explicit conclusion. Exact source/target parameter projections retain any
   pre paired-parameter-value relation. The two restoration equations retain
   every shared nonmemory observable (accounts/storage, transient, immutables,
   code, data, call context, outcomes, returndata), without equating memory or
   original instruction indices. In particular this does not restore saved
   memory on call return.

   This is local step/prefix production in the non-revert mode, NOT annotated
   successor alignment, a whole-call producer, or temporal certificate closure.
*)
