(* Concrete EVM input equality and extraction, without unfolding EVM run. *)
Theory o1LowerDloadConcreteExternal
Ancestors
  o1LowerDloadJointRelation o1LowerDloadShared venomExecSemantics
  venomState ptrDiscipline list pred_set

Theorem ld_shared_clean_accounts:
  ld_shared_agree D A tn s t /\ tn.t_stor = {} ==>
  s.vs_accounts = t.vs_accounts
Proof
  strip_tac >>
  `!a. (s.vs_accounts a).storage = (t.vs_accounts a).storage` by
    (simp[FUN_EQ_THM] >> rpt gen_tac >>
     drule ld_shared_storage_word >>
     simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[] >> metis_tac[]) >>
  drule ld_shared_accounts_fields >>
  `!a. (t.vs_accounts a).storage = (s.vs_accounts a).storage` by metis_tac[] >>
  qpat_x_assum `!a. (s.vs_accounts a).storage = _` kall_tac >>
  simp[FUN_EQ_THM]
QED

Theorem ld_shared_clean_transient:
  ld_shared_agree D A tn s t /\ tn.t_trans = {} ==>
  s.vs_transient = t.vs_transient
Proof
  strip_tac >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  drule ld_shared_transient_word >>
  simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[] >> metis_tac[]
QED

Theorem ld_concrete_constructors:
  ld_joint_local_fields s t /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient ==>
  venom_to_tx_params s = venom_to_tx_params t /\
  make_venom_call_state s target gas value data code static =
    make_venom_call_state t target gas value data code static /\
  make_venom_delegatecall_state s target gas data code static =
    make_venom_delegatecall_state t target gas data code static /\
  make_venom_create_state s target gas value data =
    make_venom_create_state t target gas value data
Proof
  simp[ld_joint_local_fields_def, venom_to_tx_params_def,
       make_venom_call_state_def, make_venom_delegatecall_state_def,
       make_venom_create_state_def]
QED

(* The common concrete result determines shared effects. The output buffer
   is deliberately written at each side's own offset, even at size zero. *)
Theorem ld_extract_concrete_transport:
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  extract_venom_result s v ro rs rr = SOME (w,s1) ==>
  extract_venom_result t v ro' rs rr =
    SOME (w, t with <|
      vs_returndata := s1.vs_returndata;
      vs_accounts := s1.vs_accounts;
      vs_logs := s1.vs_logs;
      vs_transient := s1.vs_transient;
      vs_pending_deletions := s1.vs_pending_deletions;
      vs_memory := (write_memory_with_expansion ro'
        (TAKE rs s1.vs_returndata) t).vs_memory |>)
Proof
  Cases_on `rr` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >>
  Cases_on `x1.contexts` >> simp[] >>
  PairCases_on `h` >> Cases_on `t'` >> simp[] >>
  Cases_on `x0` >- (strip_tac >> gvs[]) >>
  rename1 `INR result` >> Cases_on `result` >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
QED

(* Equal concrete inputs execute the identical opaque EVM computation. *)
Theorem ld_exec_delegatecall_transport:
  ld_joint_local_fields s t /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n off') (w2n sz) t /\
  exec_delegatecall inst s gas addr off sz ro rs = OK s1 ==>
  ?out w r. inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    exec_delegatecall inst t gas addr off' sz ro' rs =
      OK (update_var out w (t with <|
        vs_returndata := r.vs_returndata;
        vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
        vs_transient := r.vs_transient;
        vs_pending_deletions := r.vs_pending_deletions;
        vs_memory := (write_memory_with_expansion (w2n ro')
          (TAKE (w2n rs) r.vs_returndata) t).vs_memory |>)) /\
    extract_venom_result s 1w (w2n ro) (w2n rs)
      (run (make_venom_delegatecall_state s (w2w addr) (w2n gas)
        (read_memory (w2n off) (w2n sz) s)
        (lookup_account (w2w addr) s.vs_accounts).code
        s.vs_call_ctx.cc_static)) = SOME (w,r)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[ld_joint_local_fields_def] >>
  `make_venom_delegatecall_state s (w2w addr) (w2n gas)
     (read_memory (w2n off) (w2n sz) s)
     (lookup_account (w2w addr) s.vs_accounts).code s.vs_call_ctx.cc_static =
   make_venom_delegatecall_state t (w2w addr) (w2n gas)
     (read_memory (w2n off') (w2n sz) t)
     (lookup_account (w2w addr) t.vs_accounts).code t.vs_call_ctx.cc_static` by
    (drule_all ld_concrete_constructors >> simp[]) >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all ld_extract_concrete_transport >>
  disch_then (qspec_then `w2n ro'` assume_tac) >>
  simp[exec_delegatecall_def] >> metis_tac[]
QED

Theorem ld_extract_concrete_shape:
  extract_venom_result s v ro rs rr = SOME (w,r) ==>
  r = s with <|
    vs_returndata := r.vs_returndata;
    vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
    vs_transient := r.vs_transient;
    vs_pending_deletions := r.vs_pending_deletions;
    vs_memory := (write_memory_with_expansion ro
      (TAKE rs r.vs_returndata) s).vs_memory |>
Proof
  Cases_on `rr` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> Cases_on `x1.contexts` >> simp[] >>
  PairCases_on `h` >> Cases_on `t` >> simp[] >>
  Cases_on `x0` >- (strip_tac >> gvs[]) >>
  rename1 `INR result` >> Cases_on `result` >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
QED
