Theory lowerDloadPtrDelegateInterfaces
Ancestors lowerDloadPtrCall lowerDloadPtrRel ptrDiscipline venomExecSemantics
  venomState finite_map pred_set list pointerConfinedDefs memLocDefs
  lowerDloadPtrResidualInterfaces lowerDloadPtrPhi

(* With empty source masks the concrete EVM sees identical shared stores. *)
Theorem dload_delegate_full_stores:
  dload_shared_store tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  `!a b:bytes32. word_agree_except {} a b <=> a = b` by
    simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
  strip_tac >> fs[dload_shared_store_def] >>
  `!a. (s.vs_accounts a).storage = (t.vs_accounts a).storage /\
       s.vs_transient a = t.vs_transient a` by
    (gen_tac >> first_x_assum (qspec_then `a` strip_assume_tac) >>
     gvs[storage_agree_except_def, key_taint_def, FUN_EQ_THM]) >>
  conj_tac
  >- (simp[FUN_EQ_THM] >> gen_tac >>
      first_x_assum (qspec_then `x` strip_assume_tac) >>
      qpat_x_assum `!a. _ with storage := _ = _ /\ _`
        (qspec_then `x` strip_assume_tac) >>
      qpat_x_assum `(s.vs_accounts x).storage = _` (fn th => fs[GSYM th])) >>
  simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem dload_delegate_evm_input:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} ==>
  make_venom_delegatecall_state s target gas calldata code st =
  make_venom_delegatecall_state t target gas calldata code st
Proof
  strip_tac >> drule_all dload_delegate_full_stores >> strip_tac >>
  gvs[make_venom_delegatecall_state_def, venom_to_tx_params_def,
      dload_equal_environment_def, venom_state_component_equality]
QED

(* All varying caller data observed by concrete delegation is explicit here.
   Return-buffer addresses are deliberately absent from the constructed state. *)
Theorem dload_delegate_run_input:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t ==>
  make_venom_delegatecall_state s (w2w addr) (w2n gas)
    (read_memory (w2n ao) (w2n az) s)
    (lookup_account (w2w addr) s.vs_accounts).code s.vs_call_ctx.cc_static =
  make_venom_delegatecall_state t (w2w addr) (w2n gas)
    (read_memory (w2n bo) (w2n az) t)
    (lookup_account (w2w addr) t.vs_accounts).code t.vs_call_ctx.cc_static
Proof
  strip_tac >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_delegate_full_stores, dload_equal_environment_call_ctx] >>
  simp[] >> irule dload_delegate_evm_input >> metis_tac[]
QED

Theorem dload_delegate_scalar_safety:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;addr;a;sz;r;rs] /\ MEM op [gas;addr;sz;rs] /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. op = Var v ==> v NOTIN pv` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
     qpat_x_assum `!v. _` (qspec_then `v` mp_tac) >> simp[] >>
     Cases_on `a = Var v` >> Cases_on `r = Var v` >> gvs[] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >>
  qmatch_goalsub_abbrev_tac `op_taint tn arg` >>
  qpat_x_assum `!op'. _ \/ op_taint tn op' = {}`
    (qspec_then `arg` mp_tac) >> simp[Abbr `arg`]
QED

Theorem dload_delegate_scalar_equal:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gas;addr;a;sz;r;rs] /\ MEM op [gas;addr;sz;rs] /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    (drule_all dload_delegate_scalar_safety >> simp[]) >>
  `MEM op i.inst_operands` by gvs[] >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (irule eval_operand_definedness >> metis_tac[]) >>
  drule scalar_operand_equal >> disch_then irule >> metis_tac[]
QED

(* The result footprint uses one common concrete run.  The only caller-local
   effect is the relocated return-buffer write; no EVM induction is needed. *)
Theorem dload_delegate_extract:
  dload_equal_environment s t /\ s.vs_accounts = t.vs_accounts /\
  s.vs_transient = t.vs_transient /\
  extract_venom_result s value ro rz rr = SOME (output,s') ==>
  extract_venom_result t value toff rz rr =
    SOME (output, t with <|
      vs_returndata := s'.vs_returndata;
      vs_accounts := s'.vs_accounts;
      vs_logs := s'.vs_logs;
      vs_memory := (write_memory_with_expansion toff
                       (TAKE rz s'.vs_returndata) t).vs_memory;
      vs_transient := s'.vs_transient;
      vs_pending_deletions := s'.vs_pending_deletions |>)
Proof
  strip_tac >>
  `s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[dload_equal_environment_def, venom_state_component_equality] >>
  Cases_on `rr` >> gvs[extract_venom_result_def] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `x1.contexts` >> gvs[] >>
  Cases_on `h` >> Cases_on `t'` >> gvs[] >>
  Cases_on `x0` >> gvs[] >>
  Cases_on `y` >> gvs[venom_state_component_equality]
QED

Theorem dload_delegate_exec_success:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  exec_delegatecall i s gas addr ao az ro rz = OK s' ==>
  ?output u out.
    i.inst_outputs = [out] /\ s' = update_var out output u /\
    exec_delegatecall i t gas addr bo az tr rz =
      OK (update_var out output (t with <|
        vs_returndata := u.vs_returndata;
        vs_accounts := u.vs_accounts;
        vs_logs := u.vs_logs;
        vs_memory := (write_memory_with_expansion (w2n tr)
                         (TAKE (w2n rz) u.vs_returndata) t).vs_memory;
        vs_transient := u.vs_transient;
        vs_pending_deletions := u.vs_pending_deletions |>))
Proof
  strip_tac >>
  `make_venom_delegatecall_state s (w2w addr) (w2n gas)
     (read_memory (w2n ao) (w2n az) s)
     (lookup_account (w2w addr) s.vs_accounts).code s.vs_call_ctx.cc_static =
   make_venom_delegatecall_state t (w2w addr) (w2n gas)
     (read_memory (w2n bo) (w2n az) t)
     (lookup_account (w2w addr) t.vs_accounts).code t.vs_call_ctx.cc_static` by
    (irule dload_delegate_run_input >> metis_tac[]) >>
  drule_all dload_delegate_full_stores >> strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = OK _` mp_tac >>
  simp[exec_delegatecall_def] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s 1w _ _ rr` >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rz) rr` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `i.inst_outputs` >> simp[] >>
  Cases_on `t'` >> simp[] >> strip_tac >>
  drule_all dload_delegate_extract >>
  disch_then (qspec_then `w2n tr` assume_tac) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx] >>
  qexistsl [`x0`,`x1`] >> gvs[Abbr `rr`] >>
  gvs[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "delegate interface: nonempty hypotheses")
  [dload_delegate_full_stores, dload_delegate_evm_input, dload_delegate_run_input,
   dload_delegate_scalar_safety, dload_delegate_scalar_equal,
   dload_delegate_extract, dload_delegate_exec_success];
