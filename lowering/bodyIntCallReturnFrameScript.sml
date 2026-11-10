Theory bodyIntCallReturnFrame
Ancestors
  intCallReturn intCallFrame exprLoweringProps compileEnv loweringStateRelDefs localPtrsProps
  finite_map option list rich_list
  venomExecSemantics venomState accountsRelProps

(* Global state comes from the callee; caller locals and execution contexts
   come from the saved caller. Runtime immutable reads use the data section. *)
Theorem state_rel_merge_callee:
  state_rel func cenv cx es s /\
  state_rel other cenv cx (ee with scopes := []) cs /\
  cs.vs_data_section = s.vs_data_section /\
  local_ptrs_rel func cenv prev (merge_callee_state s cs) ==>
  state_rel func cenv cx (ee with scopes := prev) (merge_callee_state s cs)
Proof
  simp[state_rel_def, merge_callee_state_def, storage_rel_def,
       transient_rel_def, accounts_rel_def, immutables_rel_def,
       logs_rel_def, contract_storage_def, contract_transient_def,
       call_ctx_rel_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!name' tv' v' byte_offset'. _`
    (drule_all_then strip_assume_tac) >> simp[]
QED

Theorem stmt_state_rel_merge_callee:
  stmt_state_rel ctx func cenv cx es s /\
  state_rel other cenv cx (ee with scopes := []) cs /\
  cs.vs_data_section = s.vs_data_section /\
  immutable_alloca_sep func cenv cx (ee with scopes := es.scopes) s /\
  (!id b sz. local_region cenv es.scopes s id b sz ==>
     mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  stmt_state_rel ctx func cenv cx (ee with scopes := es.scopes)
    (merge_callee_state s cs)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func cenv es.scopes (merge_callee_state s cs)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     simp[merge_callee_state_def, lookup_var_def] >> conj_tac
     >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     rpt strip_tac >> gvs[]) >>
  irule stmt_state_rel_allocas_frame >> conj_tac
  >- (fs[stmt_state_rel_def, immutable_base_zero_def, merge_callee_state_def] >>
      rpt strip_tac >> rename1 `cenv.ce_imm_alloca = SOME op` >>
      Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`,`ee with scopes := es.scopes`] >>
      simp[merge_callee_state_def] >> rpt strip_tac >> qexists_tac `id` >>
      gvs[local_region_def, merge_callee_state_def, lookup_var_def]) >>
  conj_tac
  >- (irule state_rel_merge_callee >> goal_assum (drule_at Any) >>
      fs[stmt_state_rel_def] >> metis_tac[]) >>
  qexistsl_tac [`es`,`s`] >> simp[merge_callee_state_def]
QED

(* Repeated writes retain the statement relation when their keys are not
   pointers of any live local (including the immutable base). *)
Theorem stmt_state_rel_foldl_update_var:
  !kvs s.
    stmt_state_rel ctx func cenv cx es s /\
    EVERY (not_local_ptr cenv es.scopes) (MAP FST kvs) ==>
    stmt_state_rel ctx func cenv cx es
      (FOLDL (\s' (k,v). update_var k v s') s kvs)
Proof
  Induct >> simp[] >> Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule stmt_state_rel_update_var >> simp[]
QED

Theorem stmt_state_rel_bind_outputs:
  stmt_state_rel ctx func cenv cx es s /\
  EVERY (not_local_ptr cenv es.scopes) outs /\
  bind_outputs outs vals s = SOME s' ==>
  stmt_state_rel ctx func cenv cx es s'
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  irule stmt_state_rel_foldl_update_var >> simp[MAP_ZIP]
QED
