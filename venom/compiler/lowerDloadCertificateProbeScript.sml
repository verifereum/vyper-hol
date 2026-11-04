Theory lowerDloadCertificateProbe
Ancestors
  lowerDloadStoreProducer lowerDloadFrameCertificate lowerDloadTargetGeometry
  lowerDloadPairedBoundary lowerDloadOperand lowerDloadOwnership
  lowerDloadAllocation lowerDloadOpaqueExecution
  ptrDiscipline venomExecSemantics venomState finite_map pred_set

Theorem ld_owned_empty_initial:
  !V E tn s. ld_owned_vars V E FEMPTY FEMPTY tn tn s s
Proof
  simp[ld_owned_vars_def, ld_owned_value_def] >>
  rpt strip_tac >> gvs[ld_mask_word_identity]
QED

Theorem ld_certificate_initial_boundary:
  s.vs_allocas = FEMPTY /\ FINITE keys /\ lo <= s.vs_alloca_next ==>
  ld_frame_embedding FEMPTY FEMPTY FEMPTY s s /\
  ld_owned_vars V FEMPTY FEMPTY FEMPTY entry_taint entry_taint s s /\
  (!v:string. v IN V ==> (lookup_var v s = NONE <=> lookup_var v s = NONE)) /\
  ld_alloc_account keys 0 {} s s /\
  ld_frame_bound s.vs_alloca_next FEMPTY [] FEMPTY /\
  ld_stack_bound s.vs_alloca_next [] /\ lo <= s.vs_alloca_next
Proof
  strip_tac >> drule_all ld_geometry_initial_charge >>
  simp[ld_owned_empty_initial, ld_frame_embedding_def,
       ld_owned_selection_def, ld_erase_def]
QED

Theorem ld_owned_vars_mstore:
  ld_owned_vars V E AG BH tn un (mstore p x s) (mstore q y t) <=>
  ld_owned_vars V E AG BH tn un s t
Proof
  simp[ld_owned_vars_def, mstore_def, lookup_var_def]
QED

Theorem ld_frame_embedding_mstore:
  ld_frame_embedding E L H (mstore p x s) (mstore q y t) <=>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_embedding_def, mstore_def]
QED

Theorem ld_alloc_account_mstore:
  ld_alloc_account keys d A (mstore p x s) (mstore q y t) <=>
  ld_alloc_account keys d A s t
Proof
  simp[ld_alloc_account_def, mstore_def]
QED

Theorem ld_mstore_lookup:
  lookup_var v (mstore p x s) = lookup_var v s
Proof
  simp[mstore_def, lookup_var_def]
QED

Theorem ld_empty_outputs_prov_tvar:
  i.inst_outputs = [] ==>
  ld_step_prov AP AG L i = AG /\
  (step_taint i s s' tn).t_var = tn.t_var
Proof
  simp[ld_step_prov_def, ld_set_prov_def, step_taint_def, set_var_taint_def,
       DRESTRICT_DEF, fmap_EXT, FLOOKUP_DEF]
QED

Theorem ld_owned_vars_mstore_step:
  i.inst_outputs = [] /\ ld_owned_vars V E AG BH tn un s t ==>
  ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s (mstore p x s) tn) (step_taint i t (mstore q y t) un)
    (mstore p x s) (mstore q y t)
Proof
  strip_tac >> drule ld_empty_outputs_prov_tvar >> strip_tac >>
  simp[ld_empty_outputs_prov_tvar] >>
  irule (iffRL ld_owned_vars_tvar_cong) >>
  simp[ld_empty_outputs_prov_tvar, ld_owned_vars_mstore] >>
  qexistsl_tac [`tn`,`un`] >> simp[]
QED

(* Restoring only memory characterizes every unchanged nonmemory projection. *)
Theorem ld_mstore_nonmemory:
  (mstore p x s) with vs_memory := s.vs_memory = s
Proof
  simp[mstore_def]
QED

Theorem ld_reachable_mstore_state_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst;value] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN V) /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\
    bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  (!v:string. v IN full_names ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel CT i t = OK t' ==>
  ?s' x v y w.
    step_inst fuel CS i s = OK s' /\
    s' = mstore (w2n x) v s /\ t' = mstore (w2n y) w t /\
    eval_operand dst s = SOME x /\ eval_operand dst t = SOME y /\
    eval_operand value s = SOME v /\ eval_operand value t = SOME w /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ld_frame_embedding E L H s' t' /\ ld_alloc_account keys d A s' t' /\
    (!v:string. v IN full_names ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >> drule_all ld_reachable_mstore_backward >>
  disch_then (qx_choose_then `s'` (qx_choose_then `x`
    (qx_choose_then `v` (qx_choose_then `y` (qx_choose_then `w` strip_assume_tac))))) >>
  qexistsl_tac [`s'`,`x`,`v`,`y`,`w`] >>
  asm_rewrite_tac[] >>
  simp[ld_frame_embedding_mstore, ld_alloc_account_mstore, ld_mstore_lookup,
       ld_mstore_nonmemory] >>
  irule ld_owned_vars_mstore_step >> simp[]
QED
