Theory lowerDloadLoadCertificate
Ancestors
  lowerDloadScratchProducer lowerDloadLoadProducer lowerDloadBytesProducer
  lowerDloadOwnership lowerDloadRelocation lowerDloadProvenanceSupport
  lowerDloadMacroBoundary lowerDloadPhaseBoundary lowerDloadCompletedOutput
  lowerDloadLoadValues lowerDloadMacroMemory lowerDloadFrameCertificate lowerDloadAllocation
  lowerDloadReachableDiscipline pointerConfinedDefs contextCodegenRel
  lowerDloadPairedBoundary lowerDloadMaskBounds o1PassContract
  ptrDiscipline venomInstProofs venomExecProofs codegenRel memLocDefs venomExecSemantics venomState venomInst finite_map list pred_set

(* The scratch allocation has no original owner. Its temporary is removed
   from provenance, not assigned a fabricated source allocation. *)
Theorem ld_load_macro_provenance:
  inst.inst_opcode = DLOAD /\ inst.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_outputs = [out] /\
  FLOOKUP H a.inst_id = NONE /\ av NOTIN FDOM BH /\
  (!v. off = Var v ==> v <> av) /\ ld_op_prov BH off = NONE ==>
  ld_step_prov AP AG L inst = ld_set_prov AG [out] NONE /\
  ld_step_prov BP
    (ld_step_prov BP (ld_step_prov BP (ld_step_prov BP BH H a) H b) H c) H d =
    ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE
Proof
  strip_tac >>
  `ld_set_prov BH [av] NONE = BH` by
    (simp[ld_set_prov_def, fmap_eq_flookup, FUN_EQ_THM, FLOOKUP_DRESTRICT] >>
     rpt strip_tac >> Cases_on `x = av` >> gvs[FLOOKUP_DEF]) >>
  `ld_step_prov BP BH H a = BH` by
    simp[ld_step_prov_def, ld_out_prov_def] >>
  `ld_op_prov BH (Label "code_end") = NONE` by simp[ld_op_prov_def] >>
  `ld_step_prov BP BH H b = ld_set_prov BH [bv] NONE` by
    simp[ld_step_prov_def, ld_out_prov_def, ld_first_prov_def] >>
  asm_rewrite_tac[] >>
  simp[ld_step_prov_def, ld_out_prov_def, ld_set_prov_def, DRESTRICT_UNIV]
QED

Theorem ld_load_completed_restoration:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u ==>
  ?t1. step_inst 0 C a t0 = OK t1 /\
    (t with <|vs_vars := t1.vs_vars; vs_memory := t1.vs_memory;
              vs_inst_idx := t1.vs_inst_idx|>) = t1
Proof
  strip_tac >>
  drule_all ld_load_fourth_prefix >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_third_prefix) >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_second_prefix) >> disch_then (fn th => gvs[th]) >>
  qpat_x_assum `ld_target_prefix _ _ _ _ 1 _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `0`] ld_target_prefix_step_iff)),
       ld_target_prefix_empty] >>
  strip_tac >> qexists_tac `z` >>
  gvs[is_terminator_def] >>
  simp[update_var_def, write_memory_with_expansion_def, expand_memory_def,
       write_memory_def] >>
  gvs[step_inst_non_invoke]
QED

Theorem ld_load_completed_taint_effects:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u ==>
  u.t_var = u0.t_var |+ (av,{}) |+ (bv,{}) |+ (out,{}) /\
  u.t_stor = u0.t_stor /\ u.t_trans = u0.t_trans /\ u.t_imm = u0.t_imm
Proof
  strip_tac >>
  `FLOOKUP u.t_var out = SOME {}` by
    (drule_all ld_load_completed_output_clean >> simp[]) >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once ld_target_prefix_step_iff] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `2`] ld_target_prefix_step_iff))] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `1`] ld_target_prefix_step_iff))] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `0`] ld_target_prefix_step_iff)),
       ld_target_prefix_empty] >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `FLOOKUP (step_taint d rd zd wd).t_var out` >>
  `out_taint wd d rd = {}` by
    (qpat_x_assum `FLOOKUP _ out = SOME {}` mp_tac >>
     simp[step_taint_def, set_var_taint_def, FLOOKUP_UPDATE]) >>
  `!tx sx. out_taint tx a sx = {}` by
    simp[out_taint_def, eval_operand_def] >>
  `!tx sx. out_taint tx b sx = {}` by
    (rpt gen_tac >> simp[out_taint_def] >>
     Cases_on `eval_operand off sx` >> simp[]) >>
  rpt conj_tac >>
  simp[Once step_taint_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def] >>
  simp[Abbr `wd`] >>
  simp[Once step_taint_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, DRESTRICT_UNIV] >>
  simp[Once step_taint_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def] >>
  simp[Once step_taint_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def]
QED

Theorem ld_load_source_effects:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK z ==>
  (z with vs_vars := s.vs_vars) = s /\
  (?w. lookup_var out z = SOME w) /\
  (step_taint inst s z tn).t_var = tn.t_var |+ (out,{}) /\
  (step_taint inst s z tn).t_mem = tn.t_mem /\
  (step_taint inst s z tn).t_stor = tn.t_stor /\
  (step_taint inst s z tn).t_trans = tn.t_trans /\
  (step_taint inst s z tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       step_taint_def, set_var_taint_def, out_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF] >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem ld_load_reachable_target_scalar:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
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
  `!v. off = Var v ==> v NOTIN fn_pv P fn` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  `ld_op_prov AG off = NONE` by metis_tac[ld_annotated_scalar_prov] >>
  Cases_on `off` >> gvs[ld_op_prov_def] >>
  qpat_x_assum `!v. ld_owned_selection _ _ _` (qspec_then `s'` mp_tac) >>
  simp[ld_owned_selection_def]
QED

(* A prefix cannot change a variable that is not an output of its code. *)
Theorem ld_target_prefix_lookup_frame:
  !C code t0 u0 n t u.
    ld_target_prefix C code t0 u0 n t u ==>
    !v. (!i. MEM i code ==> ~is_terminator i.inst_opcode /\ ~MEM v i.inst_outputs) ==>
      lookup_var v t = lookup_var v t0
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[] >> rpt strip_tac >>
  `~is_terminator (EL n code).inst_opcode /\ ~MEM v (EL n code).inst_outputs`
    by metis_tac[EL_MEM] >>
  drule_all step_preserves_non_output_vars >>
  simp[lookup_var_def] >> metis_tac[]
QED

Theorem ld_load_completed_defined:
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u ==>
  ?w. lookup_var out t = SOME w
Proof
  strip_tac >> drule_all ld_load_fourth_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_load_selection_pairing:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  bv NOTIN FDOM BH ==>
  !v. ld_owned_selection E (FLOOKUP (ld_set_prov AG [out] NONE) v)
    (FLOOKUP (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE) v)
Proof
  strip_tac >>
  `ld_set_prov BH [bv] NONE = BH` by
    (simp[ld_set_prov_def, fmap_eq_flookup, FUN_EQ_THM, FLOOKUP_DRESTRICT] >>
     rpt strip_tac >> Cases_on `x = bv` >> gvs[FLOOKUP_DEF]) >>
  simp[] >> irule ld_owned_set_selection >>
  simp[ld_owned_selection_def]
QED

Theorem ld_live_clear_outputs:
  ld_live astk L AP (ld_set_prov AG outs NONE) site ==>
  ld_live astk L AP AG site
Proof
  Cases_on `outs` >>
  simp[ld_set_prov_def, ld_live_def, ld_selected_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

Theorem ld_load_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ~in_revert_forward fn s /\ dload_offset_ok CS fn inst s /\
  ld_owned_vars U E AG BH tn u0 s t0 /\
  (!v. off = Var v ==> v IN U) /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [bv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> bv /\ av NOTIN U /\ bv NOTIN U /\ av NOTIN V /\ bv NOTIN V /\
  out IN U /\ out IN V /\ av NOTIN FDOM BH /\ bv NOTIN FDOM BH /\
  ld_target_prefix CT [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  ld_frame_embedding E L H s t0 /\ ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  lo <= f /\ allocas_non_overlapping t0 /\ alloca_next_valid t0 /\
  allocas_from f t0 /\ f <= t0.vs_alloca_next /\ t0.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t0.vs_alloca_next + 32 < dimword (:256)) /\
  ld_frame_bound t0.vs_alloca_next H BP BH /\ ld_stack_bound t0.vs_alloca_next gstk /\
  (!owner bs size. ld_live astk L AP AG (owner,(bs,size)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
    lo <= bs /\ lo <= bt /\ bs+size <= s.vs_alloca_next /\ bt+size <= t0.vs_alloca_next) /\
  (!owner other bs bt size cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt size /\ ld_site_entry E other cs ct cz ==>
    (bs+size <= cs \/ cs+cz <= bs) /\ (bt+size <= ct \/ ct+cz <= bt)) /\
  (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
    bt+size <= f \/ ?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME(bt,size)) /\
  ld_byte_rel (\aa bb. (aa=bb /\ aa<lo) \/ ld_site_bytes E live aa bb)
    tn.t_mem u0.t_mem (\aa. read_memory aa 1 s) (\bb. read_memory bb 1 t0) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint u0 (Var v) SUBSET count 32) /\
  u0.t_stor SUBSET tn.t_stor /\ u0.t_trans SUBSET tn.t_trans /\ u0.t_imm SUBSET tn.t_imm ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_owned_vars U E (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE)
      (step_taint inst s z tn) u z t /\
    ld_byte_rel (\aa bb. (aa=bb /\ aa<lo) \/ ld_site_bytes E live aa bb)
      (step_taint inst s z tn).t_mem u.t_mem
      (\aa. read_memory aa 1 z) (\bb. read_memory bb 1 t) /\
    ld_frame_embedding E L H z t /\ ld_alloc_account keys d0 (a.inst_id INSERT A) z t /\
    ld_step_prov AP AG L inst = ld_set_prov AG [out] NONE /\
    ld_step_prov BP (ld_step_prov BP (ld_step_prov BP (ld_step_prov BP BH H a) H b) H c) H d =
      ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_set_prov AG [out] NONE) v)
      (FLOOKUP (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE) v)) /\
    ld_frame_bound t.vs_alloca_next H BP
      (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE) /\
    ld_stack_bound t.vs_alloca_next gstk /\ f <= t.vs_alloca_next /\
    (!owner bs size. ld_live astk L AP (ld_set_prov AG [out] NONE) (owner,(bs,size)) ==>
      ld_live astk L AP AG (owner,(bs,size)) /\ owner IN live /\ lo <= bs) /\
    (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
      lo <= bs /\ lo <= bt /\ bs+size <= z.vs_alloca_next /\ bt+size <= t.vs_alloca_next) /\
    (!owner other bs bt size cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt size /\ ld_site_entry E other cs ct cz ==>
      (bs+size <= cs \/ cs+cz <= bs) /\ (bt+size <= ct \/ ct+cz <= bt)) /\
    (!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
      bt+size <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,size)) /\
    (!v. v IN V ==> (lookup_var v z = NONE <=> lookup_var v t = NONE)) /\
    (!v. op_taint (step_taint inst s z tn) (Var v) SUBSET count 32) /\
    (!v. op_taint u (Var v) SUBSET count 32) /\
    u.t_stor SUBSET (step_taint inst s z tn).t_stor /\
    u.t_trans SUBSET (step_taint inst s z tn).t_trans /\
    u.t_imm SUBSET (step_taint inst s z tn).t_imm /\
    (z with vs_vars := s.vs_vars) = s /\
    (t with <|vs_memory := t0.vs_memory; vs_vars := t0.vs_vars;
              vs_allocas := t0.vs_allocas; vs_alloca_next := t0.vs_alloca_next;
              vs_inst_idx := t0.vs_inst_idx|>) = t0
Proof
  strip_tac >>
  `!v. off = Var v ==> v <> av` by metis_tac[] >>
  drule_all ld_reachable_load_owned >>
  disch_then (qspec_then `fuel` (qx_choose_then `z` strip_assume_tac)) >>
  drule_all ld_load_source_effects >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  drule_all ld_load_completed_restoration >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all ld_scratch_certificate_structure >>
  disch_then (qx_choose_then `p` (map_every assume_tac o CONJUNCTS)) >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\aa bb. (aa=bb /\ aa<lo) \/ ld_site_bytes E live aa bb`]
    ld_load_completed_byte_rel)) >>
  disch_then (qspecl_then [`fuel`,`CS`] (qx_choose_then `z2` strip_assume_tac)) >>
  `z2 = z` by
    (qpat_x_assum `step_inst fuel CS inst s = OK z2` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `z2 = z` SUBST_ALL_TAC >>
  drule_all ld_load_completed_taint_effects >> strip_tac >>
  drule_all ld_load_reachable_target_scalar >> strip_tac >>
  `FLOOKUP H a.inst_id = NONE` by
    (drule ld_frame_embedding_domains >> drule ld_alloc_account_disjoint >>
     simp[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  drule_all ld_load_macro_provenance >> strip_tac >>
  drule_all ld_load_selection_pairing >> strip_tac >>
  qpat_assum `z with vs_vars := _ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = t1` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  qexists `z` >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qpat_x_assum `ld_frame_embedding E L H s t1` mp_tac >>
      simp[ld_frame_embedding_def])
  >- (qpat_x_assum `ld_alloc_account keys d0 (a.inst_id INSERT A) s t1` mp_tac >>
      simp[ld_alloc_account_def] >> metis_tac[])
  >- suspend "frame_bound"
  >- (rpt strip_tac >> drule ld_live_clear_outputs >> metis_tac[])
  >- suspend "definedness"
  >- (irule ld_step_taint_bound >> simp[])
  >- suspend "target_mask"
  >> (qpat_x_assum `t1 with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _|> = t0` mp_tac >>
      simp[venom_state_component_equality])
QED

Resume ld_load_certificate_backward[frame_bound]:
  simp[ld_frame_bound_def, ld_selected_def, ld_set_prov_def, FLOOKUP_DRESTRICT] >>
  metis_tac[ld_frame_bound_def, ld_selected_def]
QED

Resume ld_load_certificate_backward[definedness]:
  rpt strip_tac >> Cases_on `v = out`
  >- (drule_all ld_load_completed_defined >> strip_tac >> simp[])
  >> `v <> av /\ v <> bv` by metis_tac[] >>
  `lookup_var v t = lookup_var v t0` by
    (irule ld_target_prefix_lookup_frame >>
     qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >>
     simp[DISJ_IMP_THM, FORALL_AND_THM, is_terminator_def]) >>
  `lookup_var v z = lookup_var v s` by
    (irule step_preserves_non_output_vars >>
     qpat_assum `step_inst fuel CS inst s = OK z` (irule_at Any) >>
     simp[is_terminator_def]) >>
  metis_tac[]
QED

Resume ld_load_certificate_backward[target_mask]:
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `out = v` >> simp[] >>
  Cases_on `bv = v` >> simp[] >>
  Cases_on `av = v` >> simp[] >> fs[op_taint_def]
QED

Finalise ld_load_certificate_backward

(* Local DLOAD certificate audit:
   C1 frame embedding and C5 allocation account transport from the successful
   first scratch step; C2 paired selections and actual provenance remove out;
   C3 owned original values and C10 conservative-live masked memory are produced
   by the checked backward boundaries; C4 definedness uses successful output
   writes and nonoutput lookup framing, including opaque original names.
   C6 frame/stack/frontier bounds, C7 live deletion inclusion, C8 endpoints and
   representation, C9 separation, C11 masks and C12 nonmemory taint subsets
   are conclusions, not assumed successor clauses. The scratch site is not an
   original owner. Both cached and fresh allocation use the separate floor f.
   E,L,H,AP,BP,keys,d0,astk,gstk remain unchanged, so saved snapshot/support
   clauses are retained. The restoration equations project all other fields,
   including parameters and shared observables, without restoring target memory
   or equating instruction indices. This is a local non-revert producer only:
   annotated successor alignment, calls and temporal closure are not proved.
*)
