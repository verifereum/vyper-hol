(* Source scopes for evaluated arbitrary-calldata argument values. *)
Theory calldataRegistrationLocals
Ancestors
  calldataRegistrationExec entryArgPtrs vyperInterpreter vyperTyping
  compileEnv venomMemDefs localPtrsProps entryLocals

Theorem decoded_arguments_bind:
  !args vals tenv.
    LIST_REL (\(name,ty) x.
      ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv x) args vals ==>
    ?env. bind_arguments tenv args vals = SOME env
Proof
  Induct_on `args` >- (Cases_on `vals` >> simp[bind_arguments_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `vals` >>
  simp[bind_arguments_def] >> rpt strip_tac >>
  drule safe_cast_well_typed >> strip_tac >> simp[] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem decoded_arguments_scope_lookup:
  bind_arguments tenv args vals = SOME env /\
  ALL_DISTINCT (MAP FST args) /\ FLOOKUP env name = SOME entry ==>
  ?i tv. i < LENGTH args /\ FST (EL i args) = name /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\
    entry = <| assignable := T; type := tv; value := EL i vals; popped := [] |>
Proof
  strip_tac >> drule vyperCallTheory.bind_arguments_fdom >> strip_tac >>
  `MEM name (MAP FST args)` by gvs[finite_mapTheory.FLOOKUP_DEF] >>
  gvs[listTheory.MEM_EL, listTheory.EL_MAP] >>
  drule_all bind_arguments_lookup_index >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem decoded_scope_local_ptrs:
  alloca_inv v /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cef st /\
  (!name entry ptr sz.
    FLOOKUP env name = SOME entry /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar (Var ptr) sz) ==>
    ?p ins. lookup_var ptr v = SOME (n2w p) /\ p < dimword (:256) /\
      MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
      ins.inst_outputs = [ptr] /\
      FLOOKUP v.vs_allocas ins.inst_id = SOME (p,sz) /\
      type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
      val_in_memory entry.type entry.value p v.vs_memory) ==>
  local_ptrs_rel fn cef [env] v
Proof
  strip_tac >> simp[local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >> simp[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      qmatch_asmsub_abbrev_tac `lookup_var p v = SOME result_word` >>
      qexists_tac `result_word` >> simp[Abbr `result_word`] >> conj_tac
      >- (simp[local_backed_def] >> disj1_tac >>
          goal_assum (drule_at Any) >> simp[]) >>
      gvs[alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> simp[]) >>
  rpt gen_tac >> simp[local_region_def, vyperStateTheory.lookup_scopes_def,
    AllCaseEqs()] >> strip_tac >>
  qpat_assum `!name entry ptr sz. _` (qspec_then `n1` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!name entry ptr sz. _` (qspec_then `n2` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  gvs[] >>
  `p <> p'` by (strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `ins.inst_id <> ins'.inst_id` by
    (strip_tac >> drule_all fn_inst_ids_distinct_inj >> strip_tac >> gvs[]) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, compileEnvTheory.regions_disjoint_def] >>
  metis_tac[]
QED

Theorem decoded_arguments_pointer_lookup:
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    P tv x dst p id) (ZIP (args,MAP SND tys)) outputs /\
  LENGTH tys = LENGTH args /\ i < LENGTH args ==>
  ?x dst p id.
    EL i outputs = (x,dst,p,id) /\
    FLOOKUP cef.ce_vars (FST (EL i args)) =
      SOME (PtrVar dst (type_memory_size (SND (EL i tys)))) /\
    P (SND (EL i tys)) x dst p id
Proof
  strip_tac >>
  `i < LENGTH (ZIP (args,MAP SND tys))` by simp[] >>
  gvs[listTheory.LIST_REL_EL_EQN] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[listTheory.EL_ZIP, listTheory.EL_MAP] >>
  Cases_on `EL i args` >>
  qspec_tac (`EL i outputs`,`out_entry`) >> gen_tac >>
  PairCases_on `out_entry` >> simp[]
QED

Theorem decoded_arguments_local_ptrs:
  bind_arguments tenv args (MAP (\(x,dst,p,id). x) outputs) = SOME env /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv). evaluate_type tenv ty = SOME tv) args tys /\
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
    eval_operand dst v = SOME (n2w p) /\ p < dimword (:256) /\
    FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
      ins.inst_id = id)) (ZIP (args,MAP SND tys)) outputs /\
  alloca_inv v /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cef st ==>
  local_ptrs_rel fn cef [env] v
Proof
  strip_tac >> irule decoded_scope_local_ptrs >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all decoded_arguments_scope_lookup >> strip_tac >>
  `LENGTH tys = LENGTH args` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  qpat_assum `LIST_REL _ (ZIP _) _`
    (mp_tac o REWRITE_RULE[listTheory.LIST_REL_EL_EQN]) >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[listTheory.EL_ZIP, listTheory.EL_MAP] >>
  Cases_on `EL i args` >>
  qabbrev_tac `out_entry = EL i outputs` >> PairCases_on `out_entry` >>
  gvs[markerTheory.Abbrev_def] >> strip_tac >>
  qpat_x_assum `LIST_REL _ args tys` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[] >> Cases_on `EL i args` >> Cases_on `EL i tys` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `(_,_,_,_) = EL i outputs` (fn th =>
    gvs[listTheory.EL_MAP, venomStateTheory.eval_operand_def] >>
    gvs[GSYM th, venomStateTheory.eval_operand_def]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem decoded_arguments_bind_typed:
  LIST_REL (\(name,ty) (ty',tv). evaluate_type tenv ty = SOME tv) args tys /\
  LIST_REL (\((name,ty),tv) (x,dst,p,id). value_has_type tv x)
    (ZIP (args,MAP SND tys)) outputs ==>
  ?env. bind_arguments tenv args (MAP (\(x,dst,p,id). x) outputs) = SOME env
Proof
  strip_tac >> irule decoded_arguments_bind >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  map_every qid_spec_tac [`outputs`,`tys`,`args`] >>
  Induct_on `args` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  namedCases_on `tys` ["", "head_ty tail_ty"] >- simp[] >>
  namedCases_on `outputs` ["", "head_out tail_out"] >- simp[] >>
  PairCases_on `head_ty` >> PairCases_on `head_out` >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED
