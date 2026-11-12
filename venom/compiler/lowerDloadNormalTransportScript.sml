Theory lowerDloadNormalTransport
Ancestors
  lowerDloadNormalData lowerDloadScalarClosure lowerDloadEffectTransport
  lowerDloadVariableTransport lowerDloadFrameCertificate lowerDloadAllocation
  lowerDloadCoverageInvariant lowerDloadPairedBoundary
  ptrDiscipline venomState

(* Companion completion is deliberately independent of execution and of the
   changed byte/ownership relations. The entry alternative is preserved. *)
Theorem ld_normal_data_companion_transport:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  s'.vs_params = s.vs_params /\ t'.vs_params = t.vs_params /\
  s'.vs_call_ctx = s.vs_call_ctx /\ t'.vs_call_ctx = t.vs_call_ctx /\
  s'.vs_accounts = s.vs_accounts /\ t'.vs_accounts = t.vs_accounts /\
  s'.vs_transient = s.vs_transient /\ t'.vs_transient = t.vs_transient /\
  s'.vs_gas_readings = s.vs_gas_readings /\
  t'.vs_gas_readings = t.vs_gas_readings ==>
  ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
      entry_fn_no_params fn) \/
   (LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params)))) /\
  s'.vs_gas_readings = t'.vs_gas_readings /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==> s'.vs_transient a = t'.vs_transient a)
Proof
  strip_tac >>
  drule ld_normal_data_envelope >>
  drule ld_normal_data_companions >>
  simp[] >> rpt strip_tac >> asm_rewrite_tac[]
QED

Theorem ld_normal_data_vars_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t /\
  ld_owned_vars U E AG' BH' tn' un' s' t' /\
  (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
  (!v. ld_owned_selection E (FLOOKUP AG' v) (FLOOKUP BH' v)) /\
  (!v owner bs sz. FLOOKUP AG' v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs sz. ld_live astk L AP AG' (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  ld_frame_bound t'.vs_alloca_next H BP BH' /\
  (!v. op_taint tn' (Var v) SUBSET count 32) /\
  (!v. op_taint un' (Var v) SUBSET count 32) /\
  tn'.t_mem = tn.t_mem /\ un'.t_mem = un.t_mem /\
  tn'.t_stor = tn.t_stor /\ un'.t_stor = un.t_stor /\
  tn'.t_trans = tn.t_trans /\ un'.t_trans = un.t_trans /\
  tn'.t_imm = tn.t_imm /\ un'.t_imm = un.t_imm ==>
  ld_normal_data CS fn V U lo E L H AP BP AG' BH' tn' un' s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_shared_state tn' un' s' t'` by
    (drule_all ld_shared_state_vars_transport >> simp[]) >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  gvs[ld_normal_data_def, ld_frame_data_def, ld_frame_embedding_def,
      ld_alloc_account_def, allocas_from_def, read_memory_def] >>
  asm_rewrite_tac[]
QED

(* The byte premise is the writer's obligation, not a source-success premise.
   No memory relation is inferred merely from a memory-only footprint. *)
Theorem ld_normal_data_memory_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (s' with vs_memory := s.vs_memory) = s /\
  (t' with vs_memory := t.vs_memory) = t /\
  ld_owned_vars U E AG' BH' tn' un' s' t' /\
  (!v. ld_owned_selection E (FLOOKUP AG' v) (FLOOKUP BH' v)) /\
  (!v owner bs sz. FLOOKUP AG' v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs sz. ld_live astk L AP AG' (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  ld_frame_bound t'.vs_alloca_next H BP BH' /\
  (!v. op_taint tn' (Var v) SUBSET count 32) /\
  (!v. op_taint un' (Var v) SUBSET count 32) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn'.t_mem un'.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
  tn'.t_stor = tn.t_stor /\ un'.t_stor = un.t_stor /\
  tn'.t_trans = tn.t_trans /\ un'.t_trans = un.t_trans /\
  tn'.t_imm = tn.t_imm /\ un'.t_imm = un.t_imm ==>
  ld_normal_data CS fn V U lo E L H AP BP AG' BH' tn' un' s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_shared_state tn' un' s' t'` by
    (drule_all ld_shared_state_memory_transport >> simp[]) >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  gvs[ld_normal_data_def, ld_frame_data_def, ld_frame_embedding_def,
      ld_alloc_account_def, allocas_from_def, lookup_var_def] >>
  asm_rewrite_tac[]
QED

Theorem ld_storage_restore_normalize:
  (s' with <|vs_accounts := s.vs_accounts; vs_transient := s.vs_transient|>) = s ==>
  s' = (s with <|vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient|>)
Proof
  strip_tac >> pop_assum (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem ld_normal_data_storage_transport:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (s' with <|vs_accounts := s.vs_accounts; vs_transient := s.vs_transient|>) = s /\
  (t' with <|vs_accounts := t.vs_accounts; vs_transient := t.vs_transient|>) = t /\
  tn'.t_var = tn.t_var /\ un'.t_var = un.t_var /\
  tn'.t_mem = tn.t_mem /\ un'.t_mem = un.t_mem /\
  ld_shared_state tn' un' s' t' /\
  un'.t_stor SUBSET tn'.t_stor /\ un'.t_trans SUBSET tn'.t_trans /\
  un'.t_imm SUBSET tn'.t_imm /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==> s'.vs_transient a = t'.vs_transient a) ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn' un' s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_storage_restore_normalize >> disch_then SUBST_ALL_TAC >>
  gvs[ld_normal_data_def, ld_frame_data_def, ld_frame_embedding_def,
      ld_alloc_account_def, allocas_from_def, read_memory_def,
      ld_owned_vars_def, lookup_var_def, op_taint_def] >>
  asm_rewrite_tac[]
QED
