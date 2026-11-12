(* The DALLOCA step of the paired normal-data relation.  LowerDload keeps
   DALLOCA as it is: both sides bump the same free memory pointer by the
   same clean size and return the same word.  The region it taints lies at
   or above the free memory pointer, which sits above every target site, so
   the byte relation survives the new taint. *)
Theory lowerDloadNormalDalloca
Ancestors
  lowerDloadResidualNonmemory lowerDloadNormalExisting lowerDloadNormalData
  lowerDloadCoverageInvariant lowerDloadPairedBoundary lowerDloadSharedState
  lowerDloadLifetime lowerDloadRelocation lowerDloadOwnership
  lowerDloadObservationBounds lowerDloadTargetGeometry lowerDloadPtrDalloca
  lowerDloadProvenanceSupport lowerDloadOpaqueExecution lowerDloadFrameCertificate
  lowerDloadAllocation lowerDloadDefs ptrDiscipline o1PassContract codegenRel
  venomExecSemantics venomState venomInst list finite_map pred_set arithmetic words

Theorem ld_byte_rel_fresh_region[local]:
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b) Ts Tt ms mt /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
     bt + sz <= n) /\
  (!b. b IN R ==> n <= b) ==>
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    (Ts UNION R) (Tt UNION R) ms mt
Proof
  rewrite_tac[ld_byte_rel_def, IN_UNION] >> BETA_TAC >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  first_x_assum (qspecl_then [`a`,`b`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  reverse conj_tac >- metis_tac[] >>
  strip_tac >- metis_tac[] >>
  disj2_tac >>
  qpat_x_assum `_ \/ ld_site_bytes _ _ _ _` strip_assume_tac >- gvs[] >>
  gvs[ld_site_bytes_def] >>
  `bt + sz <= n` by metis_tac[] >>
  `n <= bt + d` by metis_tac[] >>
  decide_tac
QED

(* Moving both free memory pointers to the same word, and tainting the same
   region above the target frontier on both sides. *)
Theorem ld_normal_data_fmp_region[local]:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (!b. b IN R ==> t.vs_alloca_next <= b) ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH
    (tn with t_mem := tn.t_mem UNION R) (un with t_mem := un.t_mem UNION R)
    (s with vs_fmp := w) (t with vs_fmp := w)
    astk live keys d A suspended gstk f
Proof
  rewrite_tac[ld_normal_data_def] >> strip_tac >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
     (tn.t_mem UNION R) (un.t_mem UNION R)
     (\a. read_memory a 1 s) (\b. read_memory b 1 t)` by
    (irule ld_byte_rel_fresh_region >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `t.vs_alloca_next` >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_x_assum `!owner bs bt sz. _ ==> _ /\ _ /\ bs+sz <= _ /\ _`
       drule_all >> simp[]) >>
  qpat_x_assum `ld_frame_data _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_frame_data_def, ld_frame_embedding_def, ld_owned_vars_def,
       ld_shared_state_def, op_taint_def, lookup_var_def] >>
  strip_tac >>
  fs[ld_alloc_account_def, allocas_from_def, read_memory_def, op_taint_def,
     lookup_var_def] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, rpt strip_tac >> res_tac >> fs[]]
QED

Theorem ld_dalloca_taint_rebase[local]:
  i.inst_opcode = DALLOCA /\ i.inst_operands = [op] /\
  x'.vs_allocas = x.vs_allocas ==>
  step_taint i x x' tm =
  step_taint i (x with vs_fmp := x'.vs_fmp) x'
    (tm with t_mem := tm.t_mem UNION new_site_bytes x x')
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def, out_taint_def,
       taint_component_equality] >>
  Cases_on `eval_operand op x` >>
  Cases_on `eval_operand op (x with vs_fmp := x'.vs_fmp)` >>
  simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]
QED

(* The target frontier sits at or below the free memory pointer at a
   DALLOCA: the source's headroom covers every scratch site the target
   charged, and the source's ALLOCA sites lie below its initial free
   memory pointer. *)
Theorem ld_normal_dalloca_frontier[local]:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  i.inst_opcode = DALLOCA /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  t.vs_alloca_next <= w2n s.vs_fmp
Proof
  strip_tac >>
  `dload_headroom_ok CS fn i s` by metis_tac[ld_annotated_headroom] >>
  `ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended)` by
    (drule ld_normal_data_geometry >> simp[]) >>
  `t.vs_alloca_next <= s.vs_alloca_next + 32 * ctx_dload_count CS` by
    (drule_all ld_charged_frontier_budget >> simp[]) >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[contextCodegenRelTheory.active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ctx_has_dalloca CS` by
    (simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `allocas_below_fmp s` by
    (drule ld_annotated_erasure >> strip_tac >>
     qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> metis_tac[]) >>
  qpat_x_assum `dload_headroom_ok _ _ _ _` mp_tac >>
  qpat_x_assum `allocas_below_fmp _` mp_tac >>
  pure_rewrite_tac[dload_headroom_ok_def, allocas_below_fmp_def,
                   GSYM ctx_has_dalloca_def] >>
  qpat_x_assum `ctx_has_dalloca CS` (fn th => rewrite_tac[th]) >>
  rpt strip_tac >> decide_tac
QED

Theorem ld_normal_dalloca_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = DALLOCA /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `t.vs_alloca_next <= w2n s.vs_fmp` by
    (irule ld_normal_dalloca_frontier >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==>
    (!v. op = Var v ==> v IN U) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}` by
    (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)
       ld_annotated_residual_read_operands >>
     disch_then (qspecl_then [`lo`,`V`,`P`] mp_tac) >>
     strip_tac >> gen_tac >> disch_tac >>
     first_x_assum (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\ ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  simp[dalloca_step_success] >> strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (irule ld_owned_operand_clean >>
     qexistsl_tac [`AG`,`BH`,`E`,`U`,`tn`,`un`] >>
     qpat_x_assum `!op. MEM op _ ==> _` (qspec_then `op` mp_tac) >>
     simp[]) >>
  `s.vs_fmp = t.vs_fmp` by fs[ld_shared_state_def] >>
  `t.vs_alloca_next <= w2n t.vs_fmp` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `t' = update_var out t.vs_fmp (t with vs_fmp := w)` >>
  qexists_tac `update_var out s.vs_fmp (s with vs_fmp := w)` >>
  conj_tac >- simp[dalloca_step_success, Abbr`w`] >>
  suspend "data"
QED

Resume ld_normal_dalloca_backward[data]:
  qabbrev_tac `R = {k | w2n t.vs_fmp <= k /\ k < w2n w}` >>
  `new_site_bytes s (update_var out s.vs_fmp (s with vs_fmp := w)) = R` by
    (simp[new_site_bytes_def, update_var_def, Abbr `R`, EXTENSION, FLOOKUP_DEF] >>
     rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]) >>
  `new_site_bytes t (update_var out t.vs_fmp (t with vs_fmp := w)) = R` by
    (simp[new_site_bytes_def, update_var_def, Abbr `R`, EXTENSION, FLOOKUP_DEF] >>
     rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]) >>
  `step_taint i s (update_var out s.vs_fmp (s with vs_fmp := w)) tn =
     step_taint i (s with vs_fmp := w) (update_var out s.vs_fmp (s with vs_fmp := w))
       (tn with t_mem := tn.t_mem UNION R)` by
    (qpat_x_assum `new_site_bytes s _ = R` (fn th => rewrite_tac[GSYM th]) >>
     mp_tac (Q.INST [`x` |-> `s`,
       `x'` |-> `update_var out s.vs_fmp (s with vs_fmp := w)`, `tm` |-> `tn`]
       ld_dalloca_taint_rebase) >>
     simp[update_var_def]) >>
  `step_taint i t (update_var out t.vs_fmp (t with vs_fmp := w)) un =
     step_taint i (t with vs_fmp := w) (update_var out t.vs_fmp (t with vs_fmp := w))
       (un with t_mem := un.t_mem UNION R)` by
    (qpat_x_assum `new_site_bytes t _ = R` (fn th => rewrite_tac[GSYM th]) >>
     mp_tac (Q.INST [`x` |-> `t`,
       `x'` |-> `update_var out t.vs_fmp (t with vs_fmp := w)`, `tm` |-> `un`]
       ld_dalloca_taint_rebase) >>
     simp[update_var_def]) >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  qpat_assum `U = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `step_taint i s _ tn = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `step_taint i t _ un = _` (fn th => rewrite_tac[th]) >>
  `ld_normal_data CS fn V U lo E L H AP BP AG BH
     (tn with t_mem := tn.t_mem UNION R) (un with t_mem := un.t_mem UNION R)
     (s with vs_fmp := w) (t with vs_fmp := w)
     astk live keys d A suspended gstk f` by
    (irule ld_normal_data_fmp_region >>
     simp[Abbr `R`] >> rpt strip_tac >> decide_tac) >>
  qpat_x_assum `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ (tn with t_mem := _) _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_normal_step_vars_complete) >>
  disch_then irule >>
  qpat_x_assum `s.vs_fmp = t.vs_fmp` (fn th => rewrite_tac[th]) >>
  suspend "fields"
QED

(* Conjunct order follows ld_normal_step_vars_complete's premises:
   lookup agreement, selection, eight taint fields, two record frames,
   owned variables. *)
Resume ld_normal_dalloca_backward[fields]:
  `ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
   ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
    simp[ld_step_prov_def, ld_out_prov_def] >>
  rpt (qpat_x_assum `ld_step_prov _ _ _ _ = _` (fn th => rewrite_tac[th])) >>
  `!x x' tm. (step_taint i x x' tm).t_var = set_var_taint tm.t_var [out] {}` by
    (rpt gen_tac >> simp[step_taint_def, out_taint_def] >>
     rpt CASE_TAC >> simp[]) >>
  `(!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_owned_vars U E AG BH tn un (s with vs_fmp := w) (t with vs_fmp := w)` by
    (qpat_x_assum `ld_owned_vars _ _ _ _ _ _ s t` mp_tac >>
     rewrite_tac[ld_owned_vars_def, lookup_var_def] >>
     simp_tac (srw_ss()) []) >>
  rpt conj_tac
  >- (qpat_x_assum `!v. v IN V ==> (lookup_var v s = NONE <=> _)` mp_tac >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- (irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  FIRST [
    qpat_x_assum `ld_owned_vars _ _ _ _ _ _ (s with vs_fmp := _) _`
      (mp_then Any mp_tac ld_owned_vars_update_supported) >>
    disch_then irule >> qexistsl_tac [`{}`, `{}`] >>
    simp[ld_owned_value_def, lowerDloadOperandTheory.ld_mask_word_def],
    simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
         step_writes_def, source_memory_write_ranges_def,
         store_taint_def, imm_taint_def, adopt_reset_def,
         written_taint_def, range_bytes_def, FLOOKUP_DEF, EXTENSION] >>
    rpt CASE_TAC >> simp[venom_state_component_equality] >>
    rpt strip_tac >> eq_tac >> rpt strip_tac >> fs[]]
QED

Finalise ld_normal_dalloca_backward
