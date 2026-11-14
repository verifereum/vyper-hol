(* Terminal projection of the concrete, execution-free registration invariant. *)
Theory defaultConcreteRegistrationEnd
Ancestors defaultConcreteRegistrationDefs defaultRegistrationState
  defaultRegistrationFold loweringStateRelDefs list rich_list finite_map pair

Theorem default_registration_terminal_reserved:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off [] [] s G tn owners ==>
  local_ptrs_reserved ce st
Proof
  strip_tac >> drule default_registration_invariant_terminal_owners >> strip_tac >>
  gvs[default_registration_invariant_def, local_ptrs_reserved_def,
      default_registration_ptr_reservation_def] >>
  conj_tac >- (
    rpt strip_tac >>
    `MEM name (MAP FST args)` by (gvs[FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]) >>
    gvs[MEM_MAP] >> rename1 `MEM arg args` >> PairCases_on `arg` >> gvs[] >>
    `?tv. MEM ((arg0,arg1),tv) (ZIP (args,all_tvs))` by
      metis_tac[MEM_ZIP, MEM_EL] >>
    drule_all LIST_REL_MEM_IMP >> strip_tac >>
    PairCases_on `y` >> gvs[default_registration_owner_def]) >>
  metis_tac[]
QED

Theorem default_registration_terminal_state_owners:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off [] [] s G tn owners ==>
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    val_wf tv x /\ val_in_memory tv x p s.vs_memory /\
    eval_operand dst s = SOME (n2w p) /\ p < dimword (:256) /\
    FLOOKUP s.vs_allocas id = SOME (p,type_memory_size tv) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id))
      (ZIP (args,all_tvs)) owners
Proof
  strip_tac >> drule default_registration_invariant_terminal_owners >> strip_tac >>
  gvs[] >> irule LIST_REL_mono >>
  qexists `default_registration_owner fn ce sa s G tn` >> simp[] >>
  simp[FORALL_PROD] >> metis_tac[default_registration_owner_state_projection]
QED

Theorem default_registration_terminal_covers:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off [] [] s G tn owners ==>
  !name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz
Proof
  strip_tac >> drule default_registration_invariant_terminal_owners >> strip_tac >>
  gvs[default_registration_invariant_def] >> rpt strip_tac >>
  `MEM name (MAP FST args)` by (gvs[FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]) >>
  gvs[MEM_MAP] >> rename1 `MEM arg args` >> PairCases_on `arg` >> gvs[] >>
  `?tv. MEM ((arg0,arg1),tv) (ZIP (args,all_tvs))` by
    metis_tac[MEM_ZIP, MEM_EL] >>
  drule_all LIST_REL_MEM_IMP >> strip_tac >>
  PairCases_on `y` >> gvs[default_registration_owner_def]
QED

Theorem default_registration_terminal_state:
  default_registration_invariant tops cx ctx fn site k vs ce0 start
    args all_tvs specs cef sa ce st off [] [] s G tn owners /\
  initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
  send_call_value mut cx
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  MAP (\(x,dst,p,id). x) owners = tx.args /\ fn_inst_ids_distinct fn ==>
  alloca_history fn s /\ return_buf_frame NONE ce st s /\
  !st0 H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn s /\
    stmt_state_rel H ctx fn ce cx es s
Proof
  strip_tac >>
  drule default_registration_terminal_reserved >> strip_tac >>
  drule default_registration_terminal_covers >> strip_tac >>
  drule default_registration_terminal_state_owners >> strip_tac >>
  irule default_registration_endpoint_state >>
  fs[default_registration_invariant_def, default_registration_resources_def,
     default_registration_entry_frame_def] >>
  qexistsl [`am`,`args`,`env`,`mut`,`owners`,`tops`,
    `MAP (\tv. (ARB,tv)) all_tvs`,`vs`] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  qpat_x_assum `LIST_REL _ args all_tvs` mp_tac >>
  simp[LIST_REL_MAP2, combinTheory.o_DEF] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  pop_assum mp_tac >> simp[ELIM_UNCURRY]
QED
