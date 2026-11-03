(* Exact successful DFT swaps, including external-call instructions. *)
Theory dftSuccessSwap
Ancestors
  dftGuards dftPermSim dftIndexedExec dftExternalFrame venomCallOracleDefs
  venomExecSemantics venomEffects venomInst venomState list
Libs
  stepInstBaseLib

Theorem dft_extract_result_fmp[local]:
  extract_venom_result s value off sz result = SOME (v,t) ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `case res of INL _ => _ | INR NONE => _ | INR (SOME _) => _` >>
  Cases_on `res` >> gvs[AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `case opt of NONE => _ | SOME _ => _` >>
  Cases_on `opt` >> gvs[]
QED

Theorem dft_external_ok_fmp_fields[local]:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  fs[is_ext_call_op_def] >> fs[Once step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  with_opcode_clause simp >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  drule dft_extract_result_fmp >> simp[update_var_def]
QED

Theorem dft_external_ok_fmp:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  metis_tac[dft_external_ok_fmp_fields]
QED

Theorem dft_external_ok_initial_fmp:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  metis_tac[dft_external_ok_fmp_fields]
QED

Definition dft_ok_swap_pair_def:
  dft_ok_swap_pair x y <=>
    DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
    DISJOINT (set (inst_defs y)) (set (inst_uses x)) /\
    DISJOINT (set (inst_defs x)) (set (inst_defs y)) /\
    effects_independent x.inst_opcode y.inst_opcode /\
    abort_compatible x.inst_opcode y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    ~is_alloca_op x.inst_opcode /\ ~is_alloca_op y.inst_opcode /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode
End

Theorem dft_ok_swap_pair_sym:
  dft_ok_swap_pair x y <=> dft_ok_swap_pair y x
Proof
  rw[dft_ok_swap_pair_def, effects_independent_def, abort_compatible_def] >>
  metis_tac[pred_setTheory.DISJOINT_SYM]
QED

Theorem dft_ok_swap_pair_nonexternal:
  dft_ok_swap_pair x y /\ ~is_ext_call_op x.inst_opcode /\
  ~is_ext_call_op y.inst_opcode ==> ext_bi_independent x y
Proof
  simp[dft_ok_swap_pair_def, ext_bi_independent_def]
QED

Theorem dft_external_partner_empty_write[local]:
  dft_ok_swap_pair x y /\ is_ext_call_op y.inst_opcode ==>
  write_effects x.inst_opcode = empty_effects
Proof
  strip_tac >> irule dft_all_read_independent_empty_write >>
  qexists_tac `y` >> gvs[dft_ok_swap_pair_def] >>
  Cases_on `y.inst_opcode` >> gvs[is_ext_call_op_def, read_effects_def]
QED

Theorem dft_external_partner_operand[local]:
  dft_ok_swap_pair x y /\ step_inst fuel C y s = OK t /\
  MEM op x.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_ok_swap_pair_def, inst_defs_def, inst_uses_def] >>
  rpt strip_tac >> gvs[] >>
  drule dftBlockSimTheory.mem_var_operand_vars >> strip_tac >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem dft_external_partner_operands[local]:
  dft_ok_swap_pair x y /\ step_inst fuel C y s = OK t ==>
  !ops. EVERY (\op. MEM op x.inst_operands) ops ==>
    eval_operands ops t = eval_operands ops s
Proof
  strip_tac >> Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h t = eval_operand h s` by
    metis_tac[dft_external_partner_operand] >> simp[]
QED

Theorem dft_external_read_memory[local]:
  dft_ok_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_memory >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_ok_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_external_read_storage[local]:
  dft_ok_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_STORAGE IN read_effects x.inst_opcode ==>
  contract_storage t = contract_storage s
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_storage >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_ok_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_external_read_transient[local]:
  dft_ok_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_TRANSIENT IN read_effects x.inst_opcode ==>
  t.vs_transient = s.vs_transient
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_transient >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_ok_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_external_read_accounts[local]:
  dft_ok_swap_pair x y /\ is_ext_call_op y.inst_opcode /\
  step_inst fuel C y s = OK t /\
  (Eff_BALANCE IN read_effects x.inst_opcode \/
   Eff_EXTCODE IN read_effects x.inst_opcode) ==>
  t.vs_accounts = s.vs_accounts
Proof
  strip_tac >>
  `y.inst_opcode = STATICCALL` by
    (Cases_on `y.inst_opcode` >>
     gvs[dft_ok_swap_pair_def, is_ext_call_op_def, effects_independent_def,
         write_effects_def, all_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  irule venomInstProofsTheory.write_effects_sound_accounts >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[is_alloca_op_def, is_terminator_def, write_effects_def]
QED


Theorem dft_pure1_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure1 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure1 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_pure2_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure2 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure2 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_pure3_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure3 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure3 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_read0_replay[local]:
  f t = f s /\ exec_read0 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_read0 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qexists_tac `[(out,f s)]` >> simp[]
QED

Theorem dft_read1_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  (!op v. MEM op x.inst_operands /\ eval_operand op s = SOME v ==>
           f v t = f v s) /\
  exec_read1 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_read1 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_empty_write_replay[local]:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\
  write_effects x.inst_opcode = empty_effects /\
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
  (Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory) /\
  (Eff_STORAGE IN read_effects x.inst_opcode ==>
     contract_storage t = contract_storage s) /\
  (Eff_TRANSIENT IN read_effects x.inst_opcode ==> t.vs_transient = s.vs_transient) /\
  ((Eff_BALANCE IN read_effects x.inst_opcode \/
    Eff_EXTCODE IN read_effects x.inst_opcode) ==> t.vs_accounts = s.vs_accounts) /\
  Eff_RETURNDATA NOTIN read_effects x.inst_opcode /\
  step_inst_base x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       step_inst_base x t =
         OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  strip_tac >> Cases_on `x.inst_opcode` >>
  qpat_x_assum `write_effects _ = empty_effects` mp_tac >>
  simp[NoAsms, write_effects_def, empty_effects_def, all_effects_def] >>
  fs[is_pseudo_def, is_terminator_def, read_effects_def] >>
  with_opcode_clause (fn cs => gvs cs) >>
  all_tac
  >>~- ([`exec_pure1 f x t`], irule dft_pure1_replay >> simp[])
  >>~- ([`exec_pure2 f x t`], irule dft_pure2_replay >> simp[])
  >>~- ([`exec_pure3 f x t`], irule dft_pure3_replay >> simp[])
  >>~- ([`exec_read0 _ _ _`], irule dft_read0_replay >> simp[empty_effects_def])
  >>~- ([`exec_read1 _ _ _`], irule dft_read1_replay >> simp[empty_effects_def, mload_def, sload_def, tload_def, contract_transient_def])
  >> gvs[AllCaseEqs(), empty_effects_def]
  >>~- ([`EVERY (\p. FST p = out) _`],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`x.inst_opcode = BUMP`],
    qexists_tac `[(ptr_out,base_val); (next_out,base_val + sz)]` >> simp[])
  >> qexists_tac `[]` >> simp[]
QED

Theorem dft_external_replay_both[local]:
  dft_ok_swap_pair x y /\ is_ext_call_op y.inst_opcode /\
  step_inst fuel C y s = OK t ==>
  (!r. step_inst fuel C x s = OK r ==>
    ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
         r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
         step_inst fuel C x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)) /\
  (!r. step_inst fuel C x t = OK r ==>
    ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
         r = FOLDL (\u p. update_var (FST p) (SND p) u) t us /\
         step_inst fuel C x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us))
Proof
  strip_tac >>
  `write_effects x.inst_opcode = empty_effects` by
    metis_tac[dft_external_partner_empty_write] >>
  `x.inst_opcode <> INVOKE` by
    (Cases_on `x.inst_opcode` >> gvs[write_effects_def, all_effects_def, empty_effects_def]) >>
  `Eff_RETURNDATA NOTIN read_effects x.inst_opcode` by
    (Cases_on `y.inst_opcode` >>
     gvs[dft_ok_swap_pair_def, effects_independent_def, is_ext_call_op_def,
         write_effects_def, all_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all venomInstProofsTheory.step_ext_call_preserves >> strip_tac >>
  drule_all dft_external_ok_fmp_fields >> strip_tac >>
  `!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s` by
    metis_tac[dft_external_partner_operand] >>
  `Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory` by
    metis_tac[dft_external_read_memory] >>
  `Eff_STORAGE IN read_effects x.inst_opcode ==> contract_storage t = contract_storage s` by
    metis_tac[dft_external_read_storage] >>
  `Eff_TRANSIENT IN read_effects x.inst_opcode ==> t.vs_transient = s.vs_transient` by
    metis_tac[dft_external_read_transient] >>
  `(Eff_BALANCE IN read_effects x.inst_opcode \/ Eff_EXTCODE IN read_effects x.inst_opcode) ==>
    t.vs_accounts = s.vs_accounts` by metis_tac[dft_external_read_accounts] >>
  fs[dft_ok_swap_pair_def, is_alloca_op_def] >>
  conj_tac >> rpt strip_tac >> fs[step_inst_non_invoke] >>
  irule dft_empty_write_replay >> simp[] >>
  metis_tac[step_inst_non_invoke, is_alloca_op_def]
QED

Theorem dft_external_replay_forward:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  is_ext_call_op y.inst_opcode /\ step_inst fuel C y s = OK t /\
  step_inst fuel C x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       step_inst fuel C x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  strip_tac >> drule_all dft_external_replay_both >> metis_tac[]
QED

Theorem dft_external_replay_backward:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  is_ext_call_op y.inst_opcode /\ step_inst fuel C y s = OK t /\
  step_inst fuel C x t = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) t us /\
       step_inst fuel C x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us)
Proof
  strip_tac >> drule_all dft_external_replay_both >> metis_tac[]
QED

Theorem dft_swap_updates_disjoint[local]:
  dft_ok_swap_pair x y /\
  EVERY (\p. MEM (FST p) x.inst_outputs) us ==>
  EVERY (\p. ~MEM (Var (FST p)) y.inst_operands /\
              ~MEM (FST p) y.inst_outputs) us
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  fs[dft_ok_swap_pair_def, inst_defs_def, inst_uses_def,
     pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[dftBlockSimTheory.mem_var_operand_vars]
QED

Theorem dft_step_swap_ok_external_first:
  dft_ok_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  is_ext_call_op a.inst_opcode /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  `dft_ok_swap_pair b a` by metis_tac[dft_ok_swap_pair_sym] >>
  drule_all dft_external_replay_backward >> strip_tac >>
  qexists_tac `FOLDL (\u p. update_var (FST p) (SND p) u) s us` >>
  simp[] >>
  `EVERY (\p. ~MEM (Var (FST p)) a.inst_operands /\
              ~MEM (FST p) a.inst_outputs) us` by
    metis_tac[dft_swap_updates_disjoint] >>
  simp[dft_external_ok_fold_iff] >> metis_tac[]
QED

Theorem dft_step_swap_ok_external_second:
  dft_ok_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  is_ext_call_op b.inst_opcode /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  `write_effects a.inst_opcode = empty_effects` by
    metis_tac[dft_external_partner_empty_write] >>
  `?us. EVERY (\p. MEM (FST p) a.inst_outputs) us /\
        sa = FOLDL (\u p. update_var (FST p) (SND p) u) s us` by
    (irule dft_empty_write_ok_updates >>
     gvs[dft_ok_swap_pair_def] >>
     metis_tac[is_alloca_op_def]) >>
  `EVERY (\p. ~MEM (Var (FST p)) b.inst_operands /\
              ~MEM (FST p) b.inst_outputs) us` by
    metis_tac[dft_swap_updates_disjoint] >>
  `?sb. step_inst fuel C b s = OK sb /\
        sab = FOLDL (\u p. update_var (FST p) (SND p) u) sb us` by
    metis_tac[dft_external_ok_fold_iff] >>
  qexists_tac `sb` >> simp[] >>
  drule_all dft_external_replay_forward >> strip_tac >>
  `EVERY (\p. ~MEM (Var (FST p)) b.inst_operands /\
              ~MEM (FST p) b.inst_outputs) us'` by
    metis_tac[dft_swap_updates_disjoint] >>
  `step_inst fuel C b sa =
     OK (FOLDL (\u p. update_var (FST p) (SND p) u) sb us')` by
    metis_tac[dft_external_ok_fold_iff] >>
  gvs[]
QED

Theorem dft_step_swap_ok:
  dft_ok_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  Cases_on `is_ext_call_op a.inst_opcode`
  >- (drule_all dft_step_swap_ok_external_first >> simp[]) >>
  Cases_on `is_ext_call_op b.inst_opcode`
  >- (drule_all dft_step_swap_ok_external_second >> simp[]) >>
  `ext_bi_independent a b` by metis_tac[dft_ok_swap_pair_nonexternal] >>
  drule_all step_swap_ok_ext >> simp[]
QED

Theorem dft_indexed_step_swap_ok:
  dft_ok_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  step_inst fuel C a s = OK sa /\
  step_inst fuel C b (sa with vs_inst_idx := SUC s.vs_inst_idx) = OK sab ==>
  ?sb sba.
    step_inst fuel C b s = OK sb /\
    step_inst fuel C a (sb with vs_inst_idx := SUC s.vs_inst_idx) = OK sba /\
    (sab with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (sba with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    gvs[dft_ok_swap_pair_def] >>
  `step_inst fuel C b sa = OK (sab with vs_inst_idx := sa.vs_inst_idx)` by
    (drule_all dft_step_ok_idx >>
     disch_then (qspec_then `sa.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all dft_step_swap_ok >> strip_tac >>
  qexistsl_tac [`sb`, `sab with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >>
  qpat_x_assum `step_inst _ _ a s = _` kall_tac >>
  qpat_x_assum `step_inst _ _ b s = _` kall_tac >>
  qpat_x_assum `step_inst _ _ b sa = _` kall_tac >>
  qpat_x_assum `step_inst _ _ b (_ with vs_inst_idx := _) = _` kall_tac >>
  drule_all dft_step_ok_idx >>
  disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[]
QED
