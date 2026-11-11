(* Stage boundaries for the optional fresh immutable-base assignment. *)
Theory bodyIntCallEntryTransport
Ancestors
  intCallCallee moduleLoweringProps localPtrsProps immutableCopyExecution
  immutableWordExecution contextProps compileEnv loweringStateRelDefs venomState finite_map list

Theorem mat_pending_stage_transport:
  mat_pending ce env st s lo mr caps /\
  (!x. not_fresh_at st x ==>
    not_fresh_at st' x /\ lookup_var x s' = lookup_var x s) /\
  s'.vs_memory = s.vs_memory ==>
  mat_pending ce env st' s' lo mr caps
Proof
  simp[mat_pending_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem mat_frame_fresh_update:
  mat_frame st s (update_var (STRING #"%" (toString st.cs_next_var)) w s)
Proof
  simp[mat_frame_def, update_var_def, venom_state_component_equality] >>
  rpt strip_tac >>
  fs[lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def]
QED

Theorem mat_inv_fresh_update:
  mat_inv fn ce env st s lo mr /\
  x = STRING #"%" (toString st.cs_next_var) /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st.cs_next_id <= st'.cs_next_id /\
  (!n p z. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) z) ==>
    not_fresh_at st p) ==>
  mat_inv fn ce env st' (update_var x w s) lo mr
Proof
  strip_tac >> gvs[] >>
  `fresh_vars_wrt st' (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule emitHelperPropsTheory.fresh_vars_wrt_advance >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> fs[mat_inv_def]) >>
  `!p. not_fresh_at st p ==>
    lookup_var p (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
    lookup_var p s` by
    (rpt strip_tac >>
     irule moduleLoweringPropsTheory.lookup_var_update_not_fresh >>
     qexists_tac `st` >> simp[]) >>
  `local_ptrs_rel fn ce [env]
    (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule local_ptrs_rel_update_var >> fs[mat_inv_def] >>
     irule local_ptrs_rel_fresh_not_scope_ptr >>
     qexistsl_tac [`fn`, `s`, `st`] >> simp[]) >>
  `alloca_inv (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule alloca_inv_fields >> qexists_tac `s` >>
     fs[mat_inv_def, update_var_def]) >>
  fs[mat_inv_def, update_var_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
  >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` irule >>
  fs[local_region_def] >> metis_tac[]
QED

(* The fixed-region stage is exactly a fresh zero assignment. *)
Theorem mat_fixed_region_transport:
  compile_fixed_region_with_id nbytes st = ((id,buf),st') /\
  mat_inv fn ce env st s lo mr /\
  mat_pending ce env st s lo mr caps /\
  (!n p z. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) z) ==>
    not_fresh_at st p) ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand buf.buf_operand s' = SOME 0w /\
    mat_inv fn ce env st' s' lo mr /\
    mat_pending ce env st' s' lo mr caps /\
    mat_frame st s s'
Proof
  strip_tac >>
  drule compile_fixed_region_execution >> strip_tac >>
  drule contextTheory.compile_fixed_region_with_id_result >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) 0w s` >>
  simp[] >> conj_tac
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_asm1_tac
  >- (irule mat_inv_fresh_update >>
      qexists_tac `st` >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule mat_pending_stage_transport >>
      qexistsl_tac [`s`, `st`] >> simp[update_var_def] >>
      rpt strip_tac
      >- (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD])
      >> fs[lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def]) >>
  simp[mat_frame_fresh_update]
QED
