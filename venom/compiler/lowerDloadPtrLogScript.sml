Theory lowerDloadPtrLog
Ancestors
  lowerDloadPtrHash lowerDloadPtrMemoryRead lowerDloadPtrRegion lowerDloadPtrRel
  lowerDloadPtrAggregate lowerDloadPtrJointNext lowerDloadPtrBlockEntry
  lowerDloadPtrPhi lowerDloadPtrCall lowerDloadPtrStatic lowerDloadPtrScalar
  ptrDiscipline venomExecSemantics venomState venomInst venomWf
  pointerConfinedDefs contextCodegenRel codegenRel memLocDefs
  venomExecProofs
  finite_map list rich_list pred_set arithmetic words

Theorem dload_eval_operands_cong:
  (!op. MEM op ops ==> eval_operand op s = eval_operand op t) ==>
  eval_operands ops s = eval_operands ops t
Proof
  qid_spec_tac `t` >> qid_spec_tac `s` >> Induct_on `ops` >>
  simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by metis_tac[] >>
  `eval_operands ops s = eval_operands ops t` by metis_tac[] >> simp[]
QED

Theorem log_step_success[local]:
  i.inst_opcode = LOG ==>
  (step_inst fuel C i s = OK s' <=>
   ?tc rest x z topics.
     i.inst_operands = Lit tc::rest /\ LENGTH rest = w2n tc + 2 /\
     ~(s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands i.inst_operands s)) /\
     eval_operand (EL 0 (REVERSE rest)) s = SOME x /\
     eval_operand (EL 1 (REVERSE rest)) s = SOME z /\
     eval_operands (DROP 2 (REVERSE rest)) s = SOME topics /\
     s' = s with vs_logs := s.vs_logs ++
       [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w)|>])
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem log_tail_layout:
  LENGTH rest = n+2 ==>
  ?a sz ops. rest = REVERSE (a::sz::ops) /\ LENGTH ops = n
Proof
  strip_tac >>
  Cases_on `REVERSE rest` >- (gvs[] >> metis_tac[LENGTH_REVERSE]) >>
  Cases_on `t` >- (gvs[] >> metis_tac[LENGTH_REVERSE]) >>
  qexistsl [`h`,`h'`,`t'`] >>
  conj_tac >- metis_tac[REVERSE_REVERSE] >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:'a list -> num``) >> simp[]
QED

Theorem log_step_layout[local]:
  i.inst_opcode = LOG /\ step_inst fuel C i s = OK s' ==>
  ?tc a sz ops x z topics.
    i.inst_operands = Lit tc :: REVERSE (a::sz::ops) /\
    LENGTH ops = w2n tc /\
    ~(s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands i.inst_operands s)) /\
    eval_operand a s = SOME x /\ eval_operand sz s = SOME z /\
    eval_operands ops s = SOME topics /\
    s' = s with vs_logs := s.vs_logs ++
      [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
         data := TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w)|>]
Proof
  strip_tac >> drule log_step_success >>
  disch_then (qspecl_then [`s'`,`s`,`fuel`,`C`] mp_tac) >> simp[] >> strip_tac >>
  drule log_tail_layout >> strip_tac >> gvs[REVERSE_APPEND] >> metis_tac[]
QED

Theorem log_read_ops:
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc::REVERSE (a::sz::ops) ==>
  mem_read_ops i = SOME <|iao_ofst := a; iao_size := SOME sz; iao_max_size := SOME sz|> /\
  mem_write_ops i = NONE
Proof
  strip_tac >> Cases_on `ops` >> simp[mem_read_ops_def, mem_write_ops_def, REVERSE_APPEND]
QED

Theorem dload_log_scalar_clean:
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc::REVERSE (a::sz::ops) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s ==>
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  (!op. MEM op (sz::ops) ==> op_prov G op = NONE)
Proof
  strip_tac >> conj_tac
  >- (gvs[taint_ok_def] >> metis_tac[]) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  drule_all log_read_ops >> strip_tac >>
  `!v. MEM (Var v) (sz::ops) ==> v NOTIN fn_pv P f` by
    (rpt strip_tac >>
     `MEM (Var v) i.inst_operands` by (simp[MEM_REVERSE] >> metis_tac[MEM]) >>
     `FILTER ($= (Var v)) i.inst_operands = [Var v] /\ a = Var v` by
       (gvs[ptr_use_ok_def, is_pointer_preserving_op_def] >> metis_tac[]) >>
     `FILTER ($= (Var v)) (sz::ops) <> []` by
       (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[MEM]) >>
     qpat_x_assum `FILTER _ i.inst_operands = _` mp_tac >>
     simp[FILTER_REVERSE, FILTER_APPEND] >>
     Cases_on `sz = Var v` >> simp[] >>
     Cases_on `FILTER ($= (Var v)) ops` >> gvs[]) >>
  rpt strip_tac >> Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem dload_log_slice[local]:
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc::REVERSE (a::sz::ops) /\
  LENGTH ops = w2n tc /\ eval_operands ops s = SOME topics /\
  eval_operand a s = SOME x /\ eval_operand sz s = SOME z /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  taint_ok f tn i s /\ ~about_to_revert f i s /\
  dload_live_layout lo sf tf fs /\ dload_memory_match lo fs tn un s t /\
  dload_value_word fs {} (op_prov G a) q x y ==>
  TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w) =
  TAKE (w2n z) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n z) 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_read_ops >> strip_tac >>
  `source_memory_read_ranges i s = [(w2n x,w2n z)]` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  Cases_on `w2n z = 0` >- simp[] >>
  `(lo < w2n x + w2n z \/ op_prov G a <> NONE) ==>
    ?b n. op_prov G a = SOME (b,n) /\ b <= w2n x /\
      w2n x + w2n z <= b+n` by
    (gvs[access_ok_def] >>
     strip_tac >> qpat_x_assum `(_ ==> _) ==> _` drule >>
     strip_tac >> gvs[op_prov_def] >> metis_tac[]) >>
  `((w2n x = w2n y /\ w2n x + w2n z <= lo) \/
   (?owner id b c n d. dload_live_site fs owner id b c n /\
     w2n x = b+d /\ w2n y = c+d /\ d+w2n z <= n))` by
    (drule_all dload_value_contained_region >> simp[]) >>
  `!k. k < w2n z ==> w2n x+k NOTIN tn.t_mem` by
    (gvs[taint_ok_def] >>
     rpt strip_tac >> qpat_x_assum `!i'. _` (qspec_then `w2n x+k` mp_tac) >>
     simp[ADD_COMM]) >>
  match_mp_tac dload_memory_clean_slice >> metis_tac[]
QED

Theorem dload_log_ghosts[local]:
  i.inst_opcode = LOG /\ i.inst_outputs = [] ==>
  step_prov PG G i (s with vs_logs := logs) = G /\
  step_taint i s (s with vs_logs := logs) tn = tn
Proof
  strip_tac >>
  simp[step_prov_def, step_taint_def, set_prov_def, set_var_taint_def,
       mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       new_site_bytes_def, step_writes_def, source_memory_write_ranges_def,
       mem_write_ops_def, range_bytes_def, taint_component_equality] >>
  simp[EXTENSION, SF CONJ_ss, DRESTRICT_UNIV, FLOOKUP_DEF, written_taint_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem dload_boundary_core_logs[local]:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs V Ws PG PH G H tn un
    (s with vs_logs := logs) (t with vs_logs := logs) cs ds
Proof
  rewrite_tac[dload_boundary_core_def] >> strip_tac >>
  simp[dload_vars_match_def, dload_memory_match_def, dload_shared_store_def,
       dload_equal_environment_def, lookup_var_def, venom_state_component_equality] >>
  conj_tac
  >- (gvs[dload_table_stack_def] >> rpt strip_tac >>
      qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `k` mp_tac) >>
      Cases_on `k` >> gvs[]) >>
  gvs[dload_vars_match_def, lookup_var_def, dload_memory_match_def,
      dload_shared_store_def, dload_equal_environment_def,
      venom_state_component_equality] >> metis_tac[]
QED

Theorem dload_boundary_core_log:
  i.inst_opcode = LOG /\ i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  ~about_to_revert f i s /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_logs := s'.vs_logs /\ t' = t with vs_logs := t'.vs_logs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_step_layout >> strip_tac >> gnvs[] >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> simp[] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `eval_operand a s <> NONE /\ eval_operand sz s <> NONE` by
    (gvs[MEM_REVERSE] >> metis_tac[]) >>
  Cases_on `eval_operand a s` >- gvs[] >>
  Cases_on `eval_operand sz s` >- gvs[] >>
  rename1 `eval_operand a s = SOME xs` >>
  rename1 `eval_operand sz s = SOME zs` >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `(!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
   (!op. MEM op (sz::ops) ==> op_prov G op = NONE)` by
    (irule dload_log_scalar_clean >> simp[] >> metis_tac[]) >>
  `!op. MEM op (sz::ops) ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `MEM op i.inst_operands` by (simp[MEM_REVERSE] >> metis_tac[MEM]) >>
     irule scalar_operand_equal >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `zs = z` by (gvs[] >> metis_tac[MEM]) >> gnvs[] >>
  `eval_operands ops s = eval_operands ops t` by
    (irule dload_eval_operands_cong >> metis_tac[MEM]) >>
  `dload_value_word fs (op_taint tn a) (op_prov G a) (op_prov H a) xs x` by
    (irule dload_matched_operand >>
     qexistsl [`V`,`s`,`t`,`un`] >> simp[] >> metis_tac[MEM_REVERSE]) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `TAKE (w2n z) (DROP (w2n xs) s.vs_memory ++ REPLICATE (w2n z) 0w) =
   TAKE (w2n z) (DROP (w2n x) t.vs_memory ++ REPLICATE (w2n z) 0w)` by
    (irule dload_log_slice >> simp[] >> metis_tac[]) >>
  suspend "log_finish"
QED

Resume dload_boundary_core_log[log_finish]:
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_logs = t.vs_logs` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `EVERY (\op. IS_SOME (eval_operand op t)) ops` by
    (qspecl_then [`ops`,`t`] mp_tac eval_operands_IS_SOME_EVERY >> simp[]) >>
  `IS_SOME (eval_operands i.inst_operands t)` by
    simp[eval_operands_IS_SOME_EVERY, EVERY_APPEND, EVERY_REVERSE, eval_operand_def] >>
  `~s.vs_call_ctx.cc_static` by gvs[] >>
  qmatch_goalsub_abbrev_tac `t with vs_logs := logs` >>
  qexists `s with vs_logs := logs` >>
  conj_tac
  >- (simp[log_step_success, REVERSE_APPEND] >>
      qexistsl [`tc`,`REVERSE (a::sz::ops)`,`xs`,`z`,`topics`] >>
      simp[REVERSE_APPEND, Abbr `logs`]) >>
  conj_tac >- gvs[lookup_var_def] >>
  `step_prov PG G i (s with vs_logs := logs) = G /\
   step_taint i s (s with vs_logs := logs) tn = tn` by
    (irule dload_log_ghosts >> simp[]) >>
  `step_prov PH H i (t with vs_logs := logs) = H /\
   step_taint i t (t with vs_logs := logs) un = un` by
    (irule dload_log_ghosts >> simp[]) >>
  simp[] >> irule dload_boundary_core_logs >> simp[]
QED

Finalise dload_boundary_core_log
