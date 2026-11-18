(* Proof-only interface for a processed prefix of exact getter registration.
   There is no execution assertion in these predicates. In particular the
   compiler equations below describe code, not a runtime endpoint. *)
Theory defaultConcreteRegistrationDefs
Ancestors defaultRegistrationFold defaultRegistrationState defaultWordRegistration
  defaultBytesRegistration compileVyper abiDecoderCoherence abiAllocationHistory
  ctorDeployMemoryRunMemEntryShiftedFrame freshWrites exprLoweringProps
  loweringStateRelDefs moduleLowering compileEnv list rich_list finite_map words

Definition default_registration_entry_frame_def:
  default_registration_entry_frame initial s <=>
    s.vs_accounts = initial.vs_accounts /\
    s.vs_transient = initial.vs_transient /\
    s.vs_logs = initial.vs_logs /\
    s.vs_call_ctx = initial.vs_call_ctx /\
    s.vs_tx_ctx = initial.vs_tx_ctx /\
    s.vs_block_ctx = initial.vs_block_ctx /\
    s.vs_outcomes = initial.vs_outcomes /\
    s.vs_requests = initial.vs_requests /\
    s.vs_pending_deletions = initial.vs_pending_deletions /\
    s.vs_code = initial.vs_code /\ s.vs_labels = initial.vs_labels /\
    s.vs_data_section = initial.vs_data_section /\
    s.vs_gas_readings = initial.vs_gas_readings
End

(* Includes the extra facts needed to preserve this owner across a subsequent
   allocation. The four-tuple is the output format of the state boundary. *)
Definition default_registration_owner_def:
  default_registration_owner fn ce st s G tn ((name,ty),tv) (x,dst,p,id) <=>
    FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    val_wf tv x /\ val_in_memory tv x p s.vs_memory /\
    eval_operand dst s = SOME (n2w p) /\ p < dimword (:256) /\
    FLOOKUP s.vs_allocas id = SOME (p,type_memory_size tv) /\
    p + type_memory_size tv <= s.vs_alloca_next /\ id < st.cs_next_id /\
    ?vname ins. dst = Var vname /\ not_fresh_at st vname /\
      ptr_covers G tn vname s (type_memory_size tv) /\
      MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
      ins.inst_outputs = [vname] /\ ins.inst_id = id
End

(* Reservation permits the not-yet-registered MemLoc slots. At termination
   the owner relation and the exact environment domain eliminate those slots. *)
Definition default_registration_ptr_reservation_def:
  default_registration_ptr_reservation ce st <=>
    !n1 n2 p sz1 sz2.
      FLOOKUP ce.ce_vars n1 = SOME (PtrVar (Var p) sz1) ==>
      not_fresh_at st p /\
      (FLOOKUP ce.ce_vars n2 = SOME (PtrVar (Var p) sz2) ==> n1 = n2)
End

Definition default_registration_resources_def:
  default_registration_resources ctx fn site k st s tn <=>
    alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
    k + unit_alloca_budget ctx < dimword (:256) /\
    alloca_history fn s /\ abi_alloca_history (fn_insts fn) s /\
    alloca_room ctx fn s /\ fmp_room ctx fn s /\
    allocas_from 0 s /\ fresh_vars_wrt st s /\
    (!id r. FLOOKUP s.vs_allocas id = SOME r ==> id < st.cs_next_id) /\
    tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition default_registration_slot_def:
  default_registration_slot tops ce ((name,ty),tv) (n,prim,dyn,sz,info) <=>
    n = name /\ prim = is_word_type ty /\
    dyn = is_abi_dynamic ce.ce_struct_fields ty /\ sz = tv_abi_size tv /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (is_word_type ty \/ is_bytestring_type ty) /\
    ?p. FLOOKUP ce.ce_vars name = SOME (MemLoc p (type_memory_size tv))
End

(* Fixed parameters precede exactly the nine dynamic arguments expected by
   default_registration_joint_fold. Processed length is LENGTH owners: no
   second independently evolving prefix index needs to be synchronized. *)
Definition default_registration_invariant_def:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
      args all_tvs specs cef sa ce st off rest tvs s G tn owners <=>
    LENGTH owners <= LENGTH args /\
    LENGTH args = LENGTH all_tvs /\ LENGTH specs = LENGTH args /\
    MAP (\(name,prim,dyn,sz,info). sz) specs = MAP tv_abi_size all_tvs /\
    ALL_DISTINCT (MAP FST args) /\
    LIST_REL (\(name,ty) tv. evaluate_type (type_env tops) ty = SOME tv)
      args all_tvs /\
    rest = DROP (LENGTH owners) specs /\ tvs = DROP (LENGTH owners) all_tvs /\
    off = 4 + SUM (MAP tv_abi_size (TAKE (LENGTH owners) all_tvs)) /\
    SUM (MAP tv_abi_size all_tvs) <= LENGTH (DROP 4 initial.vs_call_ctx.cc_calldata) /\
    LENGTH initial.vs_call_ctx.cc_calldata < dimword (:256) /\
    compile_register_positional_args ce0 (TAKE (LENGTH owners) specs) 4 start = (ce,st) /\
    compile_register_positional_args ce rest off st = (cef,sa) /\
    fn_has_code st sa fn /\ cs_extends st sa /\
    LIST_REL (default_registration_slot tops ce)
      (ZIP (DROP (LENGTH owners) args,tvs)) rest /\
    LIST_REL (default_registration_owner fn ce st s G tn)
      (ZIP (TAKE (LENGTH owners) args,TAKE (LENGTH owners) all_tvs)) owners /\
    FDOM ce.ce_vars = set (MAP FST args) /\
    default_registration_ptr_reservation ce st /\
    default_registration_resources ctx fn site k st s tn /\
    default_registration_entry_frame initial s /\
    ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
    ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
    storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
    immutable_section_layout ce tops
End

Theorem default_registration_owners_empty:
  LIST_REL (default_registration_owner fn ce st s G tn) [] owners <=> owners = []
Proof
  simp[]
QED

Theorem default_registration_invariant_empty_owners:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off rest tvs s G tn [] ==>
  ce = ce0 /\ st = start /\ off = 4 /\ rest = specs /\ tvs = all_tvs
Proof
  simp[default_registration_invariant_def,
       compile_register_positional_args_def, comp_return_def] >> metis_tac[]
QED

Theorem default_registration_owner_state_projection:
  default_registration_owner fn ce st s G tn ((name,ty),tv) (x,dst,p,id) ==>
  FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
  val_wf tv x /\ val_in_memory tv x p s.vs_memory /\
  eval_operand dst s = SOME (n2w p) /\ p < dimword (:256) /\
  FLOOKUP s.vs_allocas id = SOME (p,type_memory_size tv) /\
  (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
    ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id)
Proof
  simp[default_registration_owner_def] >> metis_tac[]
QED

Theorem default_registration_invariant_terminal_owners:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off [] [] s G tn owners ==>
  LENGTH owners = LENGTH args /\ ce = cef /\ st = sa /\
  LIST_REL (default_registration_owner fn cef sa s G tn)
    (ZIP (args,all_tvs)) owners
Proof
  simp[default_registration_invariant_def,
       compile_register_positional_args_def, comp_return_def] >>
  strip_tac >>
  `LENGTH owners = LENGTH args` by decide_tac >>
  gvs[TAKE_LENGTH_TOO_LONG]
QED

Theorem default_registration_slot_sizes:
  !args tvs specs.
  LENGTH args = LENGTH tvs /\
  LIST_REL (default_registration_slot tops ce) (ZIP (args,tvs)) specs ==>
  MAP (\(name,prim,dyn,sz,info). sz) specs = MAP tv_abi_size tvs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `specs` >> simp[] >>
  gen_tac >> rename1 `default_registration_slot _ _ (arg,tv) spec` >>
  PairCases_on `arg` >> PairCases_on `spec` >>
  simp[default_registration_slot_def] >> metis_tac[]
QED

(* A genuine empty-prefix construction: every hypothesis is a source/compiler
   or state resource, and none is a runtime execution or endpoint assertion. *)
Theorem default_registration_invariant_initial:
  LENGTH args = LENGTH all_tvs /\ LENGTH specs = LENGTH args /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) tv. evaluate_type (type_env tops) ty = SOME tv) args all_tvs /\
  SUM (MAP tv_abi_size all_tvs) <= LENGTH (DROP 4 initial.vs_call_ctx.cc_calldata) /\
  LENGTH initial.vs_call_ctx.cc_calldata < dimword (:256) /\
  compile_register_positional_args ce specs 4 st = (cef,sa) /\
  fn_has_code st sa fn /\ cs_extends st sa /\
  LIST_REL (default_registration_slot tops ce) (ZIP (args,all_tvs)) specs /\
  FDOM ce.ce_vars = set (MAP FST args) /\
  default_registration_ptr_reservation ce st /\
  default_registration_resources ctx fn site k st s tn /\
  default_registration_entry_frame initial s /\
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
  immutable_section_layout ce tops ==>
  default_registration_invariant tops cx ctx fn site k initial ce st
    args all_tvs specs cef sa ce st 4 specs all_tvs s G tn []
Proof
  simp[default_registration_invariant_def,
       compile_register_positional_args_def, comp_return_def] >>
  metis_tac[default_registration_slot_sizes]
QED

(* Type-check the exact partial application supplied as R to the list fold.
   This is only an interface projection, not an admitted head step. *)
Theorem default_registration_fold_cursor:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off rest tvs s G tn owners ==>
  4 <= off /\ ~s.vs_halted /\ LENGTH rest = LENGTH tvs /\
  compile_register_positional_args ce rest off st = (cef,sa)
Proof
  simp[default_registration_invariant_def, default_registration_resources_def] >>
  rpt strip_tac >> simp[LENGTH_DROP]
QED

Theorem default_registration_invariant_prefix_size:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off rest tvs s G tn owners ==>
  off = 4 + SUM (MAP (\(name,prim,dyn,sz,info). sz)
    (TAKE (LENGTH owners) specs))
Proof
  simp[default_registration_invariant_def] >> strip_tac >>
  `TAKE (LENGTH owners) (MAP (\(name,prim,dyn,sz,info). sz) specs) =
   TAKE (LENGTH owners) (MAP tv_abi_size all_tvs)` by simp[] >>
  gvs[MAP_TAKE]
QED
