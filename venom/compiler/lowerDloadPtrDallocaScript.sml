Theory lowerDloadPtrDalloca
Ancestors
  lowerDloadPtrScalar lowerDloadPtrBlockEntry lowerDloadPtrAggregate
  lowerDloadPtrPhi lowerDloadPtrCall lowerDloadPtrRel venomExecSemantics
  venomState venomInst ptrDiscipline memLocDefs pointerConfinedDefs codegenRel finite_map list pred_set

(* LowerDload copies a DALLOCA unchanged.  Both sides bump the same free
   memory pointer by the same untainted size and return the same word, a
   DALLOCA pointer into a site at or above the floor. *)

Theorem dalloca_step_success:
  i.inst_opcode = DALLOCA ==>
  (step_inst fuel C i s = OK s' <=>
   ?op out sz. i.inst_operands = [op] /\ i.inst_outputs = [out] /\
     eval_operand op s = SOME sz /\
     s' = update_var out s.vs_fmp
            (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz))))
Proof
  strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[]
QED

Theorem dalloca_operand_clean:
  i.inst_opcode = DALLOCA /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  conj_tac
  >- (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
      Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >>
      metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dalloca_ghost_updates[local]:
  i.inst_opcode = DALLOCA /\ i.inst_outputs = [out] /\
  i.inst_operands = [op] /\ eval_operand op s = SOME sz ==>
  step_prov PG G i
    (update_var out s.vs_fmp (s with vs_fmp := m)) =
    set_prov G [out] (SOME (w2n s.vs_fmp, w2n m - w2n s.vs_fmp)) /\
  step_taint i s (update_var out s.vs_fmp (s with vs_fmp := m)) tn =
    tn with <|t_mem := tn.t_mem UNION {i | w2n s.vs_fmp <= i /\ i < w2n m};
              t_var := set_var_taint tn.t_var [out] {}|>
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, step_taint_def, out_taint_def] >>
  simp[mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, written_taint_def,
       taint_component_equality, EXTENSION] >>
  rw[] >> eq_tac >> rw[] >> gvs[FLOOKUP_DEF]
QED

(* The new site is the same on both sides, at or above the floor, and
   below dimword; the bytes it taints lie above the target frontier, so
   above every live site. *)
Theorem dload_boundary_core_dalloca:
  i.inst_opcode = DALLOCA /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ s.vs_labels = t.vs_labels /\
  fl <= w2n s.vs_fmp /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core fl lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core fl lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with <|vs_vars := s'.vs_vars; vs_fmp := s'.vs_fmp|> /\
    t' = t with <|vs_vars := t'.vs_vars; vs_fmp := t'.vs_fmp|>
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ Ct _ _ = _` mp_tac >>
  simp[dalloca_step_success] >> strip_tac >> gvs[] >>
  `dload_vars_match fl fs V G H tn un s t /\ dload_equal_environment s t` by
    gvs[dload_boundary_core_def] >>
  `t.vs_alloca_next <= w2n s.vs_fmp` by
    (`t.vs_alloca_next <= fl` by
       gvs[dload_boundary_core_def, dload_memory_match_def] >>
     decide_tac) >>
  `s.vs_fmp = t.vs_fmp` by
    gvs[dload_equal_environment_def, venom_state_component_equality] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (irule dalloca_operand_clean >> qexistsl [`P`,`f`,`i`,`s`] >> gvs[]) >>
  `eval_operand op s = eval_operand op t` by
    (irule scalar_operand_equal >> simp[] >>
     conj_tac
     >- (`eval_operand op s = NONE <=> eval_operand op t = NONE` by
           (irule eval_operand_definedness >> simp[] >>
            Cases_on `op` >> gvs[] >> metis_tac[]) >>
         gvs[]) >>
     qexistsl [`G`,`H`,`V`,`fl`,`fs`,`tn`,`un`] >> simp[] >>
     Cases_on `op` >> gvs[]) >>
  qexists `update_var out s.vs_fmp
             (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz)))` >>
  simp[dalloca_step_success] >>
  conj_tac
  >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rw[] >> gvs[lookup_var_def]) >>
  conj_tac >- suspend "core" >>
  simp[update_var_def, venom_state_component_equality]
QED

Resume dload_boundary_core_dalloca[core]:
  qmatch_goalsub_abbrev_tac `s with vs_fmp := m` >>
  `step_prov PG G i (update_var out s.vs_fmp (s with vs_fmp := m)) =
     set_prov G [out] (SOME (w2n s.vs_fmp, w2n m - w2n s.vs_fmp)) /\
   step_taint i s (update_var out s.vs_fmp (s with vs_fmp := m)) tn =
     tn with <|t_mem := tn.t_mem UNION {i | w2n s.vs_fmp <= i /\ i < w2n m};
               t_var := set_var_taint tn.t_var [out] {}|>` by
    (irule dalloca_ghost_updates >> metis_tac[]) >>
  `step_prov PH H i (update_var out t.vs_fmp (t with vs_fmp := m)) =
     set_prov H [out] (SOME (w2n t.vs_fmp, w2n m - w2n t.vs_fmp)) /\
   step_taint i t (update_var out t.vs_fmp (t with vs_fmp := m)) un =
     un with <|t_mem := un.t_mem UNION {i | w2n t.vs_fmp <= i /\ i < w2n m};
               t_var := set_var_taint un.t_var [out] {}|>` by
    (irule dalloca_ghost_updates >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_boundary_core_def] >> strip_tac >>
  rpt conj_tac
  >~ [`dload_table_stack _ _ _`]
  >- (qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
      simp[dload_table_stack_def, update_var_def] >> rpt strip_tac >>
      qpat_x_assum `!k. _ ==> (EL k fs).dr_source = _ /\ _`
        (qspec_then `k` mp_tac) >>
      Cases_on `k` >> gvs[])
  >~ [`dload_vars_match _ _ _ _ _ _ _ _ _`] >- suspend "vars"
  >~ [`dload_memory_match _ _ _ _ _ _ _`] >- suspend "memory" >>
  gvs[dload_live_layout_def, dload_param_values_def, dload_shared_store_def,
      dload_equal_environment_def, update_var_def,
      venom_state_component_equality]
QED

Resume dload_boundary_core_dalloca[vars]:
  `w2n t.vs_fmp + (w2n m - w2n t.vs_fmp) < dimword (:256)` by
    (`w2n m < dimword (:256) /\ w2n t.vs_fmp < dimword (:256)` by
       simp[wordsTheory.w2n_lt] >> decide_tac) >>
  qpat_x_assum `dload_vars_match _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_vars_match_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       set_prov_def, set_var_taint_def, op_taint_def] >>
  rpt strip_tac >> Cases_on `v = out` >> gvs[]
  >- simp[dload_value_word_def, word_agree_except_def] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[]
QED

Resume dload_boundary_core_dalloca[memory]:
  `lo <= s.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
   (!owner id b c n. dload_live_site fs owner id b c n ==>
      b + n <= s.vs_alloca_next /\ c + n <= t.vs_alloca_next)` by
    (gvs[dload_live_layout_def, dload_live_site_def] >> metis_tac[]) >>
  qpat_x_assum `dload_memory_match _ _ _ _ _ _ _` mp_tac >>
  simp[dload_memory_match_def, ld_dyn_agree_def, update_var_def] >>
  strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> rpt strip_tac >>
      `b + n <= s.vs_alloca_next /\ c + n <= t.vs_alloca_next` by metis_tac[] >>
      `~(w2n t.vs_fmp <= b + k) /\ ~(w2n t.vs_fmp <= c + k)` by decide_tac >>
      qpat_x_assum `!owner id b c n k. _` drule_all >> gvs[]) >>
  qx_gen_tac `a` >> rpt strip_tac >>
  qpat_x_assum `!i. fl <= i /\ i < dimword (:256) ==> _` (qspec_then `a` mp_tac) >>
  qpat_x_assum `!i. fl <= i /\ i < dimword (:256) /\ _ ==> _`
    (qspec_then `a` mp_tac) >>
  gvs[]
QED

Finalise dload_boundary_core_dalloca
