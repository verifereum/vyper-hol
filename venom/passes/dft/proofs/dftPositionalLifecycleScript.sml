Theory dftPositionalLifecycle
Ancestors
  dftPositionalCrossing dftPositionalReturn dftIndexedOriginalRuntime
  dftIndexedReverseCut dftPositionalPhase dftPositionalRuntime dftPositionalEdit
  dftRecursiveActivePhase dftRecursiveReturnPhase dftRecursiveCallProvenance
  dftOccurrenceReturn dftOpenErase
  dftOriginalScheduleRuntime dftProtectedRuntime
  dftOriginalRuntime dftOccurrenceOrdinaryClosure dftOccurrenceReplay
  dftOccurrenceMachine dftOpenMachine dftRunRel unitLabelMapIdentity
  venomInst venomState finite_map list arithmetic

Theorem dft_pos_root_crossing_ready:
  dft_original_context Corig C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D fi bi f g b b' /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  l = FUNPOW (dft_occ_oracle_next w C) m
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  s.vs_inst_idx = LENGTH pre /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE ==>
  dft_recursive_crossing_ready (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks) b pre x call post s
Proof
  strip_tac >>
  `dft_all_original_ready l` by
    metis_tac[dft_all_original_root, dft_all_original_iter] >>
  `dft_source_provenance C L l` by
    metis_tac[dft_source_root, dft_source_run] >>
  `s.vs_labels = L` by metis_tac[dft_source_active_at] >>
  `dft_original_cut (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks) b s` by
    (gvs[dft_pos_slot_def] >> irule dft_all_original_indexed_at >>
     simp[] >> metis_tac[]) >>
  `dft_original_function (EL fi Corig.ctx_functions) f` by
    (fs[dft_pos_slot_def, dft_original_context_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dft_original_block (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks) b` by
    (fs[dft_pos_slot_def, dft_original_function_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `b.bb_instructions = pre ++ [x;call] ++ post` by
    fs[dft_pos_runtime_ready_def, dft_pos_slot_def] >>
  `EVERY inst_wf b.bb_instructions` by
    (drule dft_original_block_perm >> strip_tac >>
     drule sortingTheory.PERM_EVERY >>
     fs[dft_original_block_def, dft_original_schedule_def]) >>
  `!lab. MEM (Label lab) x.inst_operands ==> lab IN FDOM s.vs_labels` by
    (drule_all dft_original_context_labels >> strip_tac >>
     fs[ctx_labels_bound_def] >> rpt strip_tac >>
     `MEM f C.ctx_functions` by
       (fs[dft_pos_slot_def] >> metis_tac[MEM_EL]) >>
     `MEM x (fn_insts f)` by
       (simp[fn_insts_MEM] >> qexists_tac `b` >>
        fs[dft_pos_slot_def] >> metis_tac[MEM_EL]) >> metis_tac[]) >>
  simp[dft_recursive_crossing_ready_def] >> fs[EVERY_MEM]
QED

(* A phase with fixed endpoints of origin.  The orbit witnesses are extended,
   not reselected independently of the phase endpoints. *)
Definition dft_pos_rooted_phase_def:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r <=>
    dft_pos_phase C D fi bi pre x call post l r /\
    (?a. l = FUNPOW (dft_occ_oracle_next w C) a rootL) /\
    (?b. r = FUNPOW (dft_occ_oracle_next w D) b rootR)
End

Theorem dft_pos_rooted_phase_project:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r ==>
  dft_pos_phase C D fi bi pre x call post l r /\
  (?a. l = FUNPOW (dft_occ_oracle_next w C) a rootL) /\
  (?b. r = FUNPOW (dft_occ_oracle_next w D) b rootR)
Proof
  simp[dft_pos_rooted_phase_def]
QED

Theorem dft_pos_rooted_phase_extend:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r /\
  dft_pos_phase C D fi bi pre x call post
    (FUNPOW (dft_occ_oracle_next w C) i l)
    (FUNPOW (dft_occ_oracle_next w D) j r) ==>
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
    (FUNPOW (dft_occ_oracle_next w C) i l)
    (FUNPOW (dft_occ_oracle_next w D) j r)
Proof
  simp[dft_pos_rooted_phase_def] >> rpt strip_tac >>
  metis_tac[FUNPOW_ADD]
QED

Theorem dft_pos_root_crossing_next:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r /\
  dft_pos_slot C D fi bi f g b b' /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  s.vs_inst_idx = LENGTH pre /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE ==>
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = nL /\
  dft_occ_count (dft_occ_oracle_next w D r) = nR
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `dft_recursive_crossing_ready (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks) b pre x call post s` by
    (irule dft_pos_root_crossing_ready >> goal_assum drule >> simp[] >> metis_tac[]) >>
  drule_all dft_pos_crossing_next >> disch_then (qspec_then `w` strip_assume_tac) >>
  conj_tac
  >- metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1] >>
  asm_rewrite_tac[]
QED

Theorem dft_pos_root_crossing_enter:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r /\
  dft_pos_slot C D fi bi f g b b' /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  s.vs_inst_idx = LENGTH pre /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  eval_operands ops s = SOME args /\ setup_callee calleeR args s = SOME cs ==>
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  (?calleeL cert certs t.
    step_inst_base x s = OK t /\
    dft_pos_functions C D calleeL calleeR /\
    dft_pos_frame C D fi bi pre x call post (SOME cert)
      (DftCaller f 0 b call (t with vs_inst_idx := SUC s.vs_inst_idx))
      (DftCaller g 0 b' call s) /\
    dft_pos_stack C D fi bi pre x call post certs ls rs /\
    (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_core =
      DftOpen (DftEnter calleeL 0 cs)
        (DftCaller f 0 b call (t with vs_inst_idx := SUC s.vs_inst_idx)::ls) nL /\
    (dft_occ_oracle_next w D r).dft_occ_core =
      DftOpen (DftEnter calleeR 0 cs) (DftCaller g 0 b' call s::rs) nR) /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_path =
    l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
  (dft_occ_oracle_next w D r).dft_occ_path =
    l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w D r).dft_occ_visit = 0 /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_saved =
    (l.dft_occ_path,l.dft_occ_visit)::l.dft_occ_saved /\
  (dft_occ_oracle_next w D r).dft_occ_saved =
    (l.dft_occ_path,l.dft_occ_visit)::r.dft_occ_saved
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `dft_recursive_crossing_ready (EL fi Corig.ctx_functions)
    (EL bi (EL fi Corig.ctx_functions).fn_blocks) b pre x call post s` by
    (irule dft_pos_root_crossing_ready >> goal_assum drule >> simp[] >> metis_tac[]) >>
  drule_all dft_pos_crossing_enter >> disch_then (qspec_then `w` strip_assume_tac) >>
  conj_tac >- metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem dft_pos_rooted_pending_return_success:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  LENGTH l.dft_occ_saved = SUC (LENGTH certs) /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r)
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `dft_pos_frame C D fi bi pre x call post (SOME z) lf rf` by
    fs[dft_pos_stack_cons] >>
  `?a. dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a` by
    metis_tac[dft_restore_pair_failure, optionTheory.option_CASES, optionTheory.NOT_NONE_SOME] >>
  drule_all dft_pos_pending_return_success >>
  disch_then (qspec_then `w` assume_tac) >>
  metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]
QED

Theorem dft_pos_rooted_pending_return_failure:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = NONE ==>
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nL;
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nR;
      dft_occ_saved := []|>
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `dft_pos_frame C D fi bi pre x call post (SOME z) lf rf` by
    fs[dft_pos_stack_cons] >>
  drule_all dft_pos_pending_failure >> disch_then (qspec_then `w` strip_assume_tac) >>
  conj_tac
  >- (`dft_pos_phase C D fi bi pre x call post
        (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
        (irule dft_pos_cleared_phase >> metis_tac[]) >>
      metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]) >>
  asm_rewrite_tac[]
QED

Theorem dft_pos_rooted_pending_nonreturn:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone result) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone result) (rf::rs) nR /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  (!ret cs. result <> IntRet ret cs) ==>
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r) /\
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  conj_tac
  >- (`dft_pos_phase C D fi bi pre x call post
        (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)` by
        (irule dft_pos_cleared_phase >> metis_tac[]) >>
      metis_tac[dft_pos_rooted_phase_extend, FUNPOW_1]) >>
  asm_rewrite_tac[]
QED

Theorem dft_pos_phase_done_right[local]:
  dft_pos_phase C D fi bi pre x call post l r /\
  r.dft_occ_core = DftOpen (DftDone result) [] nR /\
  dft_occ_count l = nL ==>
  l.dft_occ_core = DftOpen (DftDone result) [] nL
Proof
  simp[dft_pos_phase_def, dft_pos_control_def, dft_occ_count_def] >>
  rpt strip_tac >> gvs[dft_pos_stack_def] >>
  Cases_on `certs` >> gvs[dft_pos_stack_def]
QED

Theorem dft_pos_invoke_no_entry[local]:
  r.dft_occ_core = DftOpen (DftAt g 0 b s) rs n /\
  get_instruction b s.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE /\
  ~(?nm ops callee args cs. decode_invoke call = SOME (nm,ops) /\
    lookup_function nm D.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs) ==>
  ?result. (dft_occ_oracle_next w D r).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def, dft_open_invoke_def] >>
  Cases_on `decode_invoke call` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `decode_invoke call = SOME pair` >> PairCases_on `pair` >>
  simp[] >> Cases_on `lookup_function pair0 D.ctx_functions` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_erase_def, dft_fill_def, dft_fill_control_def] >> metis_tac[]
QED

Theorem dft_pos_root_crossing_no_entry:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r /\
  dft_pos_slot C D fi bi f g b b' /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  s.vs_inst_idx = LENGTH pre /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  ~(?nm ops callee args cs. decode_invoke call = SOME (nm,ops) /\
    lookup_function nm D.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs) ==>
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  ?result.
    (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_core =
      DftOpen (DftDone result) [] nL /\
    (dft_occ_oracle_next w D r).dft_occ_core = DftOpen (DftDone result) [] nR
Proof
  strip_tac >> drule_all dft_pos_root_crossing_next >> strip_tac >>
  `get_instruction b' s.vs_inst_idx = SOME call` by
    (gvs[dft_pos_slot_def, dft_pos_runtime_ready_def] >>
     simp[dft_pos_edit_ctx_selected, dft_pos_edit_fn_selected,
          get_instruction_def, EL_APPEND_EQN]) >>
  `?result. (dft_occ_oracle_next w D r).dft_occ_core =
    DftOpen (DftDone result) [] nR` by
    (irule dft_pos_invoke_no_entry >> goal_assum drule >> metis_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >> qexists_tac `result` >>
  conj_tac >- (irule dft_pos_phase_done_right >>
               metis_tac[dft_pos_rooted_phase_project]) >> asm_rewrite_tac[]
QED

Theorem dft_pos_rooted_pending_resume:
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  l.dft_occ_saved = (path,visit)::saved /\ LENGTH saved = LENGTH certs /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r) /\
  dft_pos_stack C D fi bi pre x call post certs ls rs /\
  ?a.
    dft_restore z.dft_cert_call.inst_outputs ret cs
      (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
    dft_occ_oracle_next w C l = l with
      <|dft_occ_core := DftOpen (DftAt z.dft_cert_ordinary_fn 0 z.dft_cert_before
          (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) ls nL;
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|> /\
    FUNPOW (dft_occ_oracle_next w D) 2 r = r with
      <|dft_occ_core := DftOpen (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
          (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) rs nR;
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>
Proof
  strip_tac >>
  `LENGTH l.dft_occ_saved = SUC (LENGTH certs)` by simp[] >>
  drule_all dft_pos_rooted_pending_return_success >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  `dft_pos_frame C D fi bi pre x call post (SOME z) lf rf /\
   dft_pos_stack C D fi bi pre x call post certs ls rs` by fs[dft_pos_stack_cons] >>
  conj_tac >- asm_rewrite_tac[] >>
  `r.dft_occ_saved = (path,visit)::saved` by fs[dft_pos_rooted_phase_def, dft_pos_phase_def] >>
  `?a. dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a` by
    metis_tac[dft_restore_pair_failure, optionTheory.option_CASES, optionTheory.NOT_NONE_SOME] >>
  qexists_tac `a` >> conj_tac >- asm_rewrite_tac[] >>
  drule_all dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `z.dft_cert_forward` by fs[dft_pos_frame_def, dft_pos_certificate_def] >>
  fs[dft_pos_frame_def, dft_certificate_saved_def] >> gvs[] >>
  drule_all dft_certificate_done_segment >> simp[]
QED
