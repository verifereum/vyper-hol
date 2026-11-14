(* Conditional, source-only consequences of the paired inherited histories.
   In particular these results neither produce histories at selected calls nor
   claim preservation of the occurrence/alignment channels. *)
Theory readonlyInvokeCopyFwdProtectionInherited
Ancestors
  readonlyInvokeCopyFwdProtection readonlyInvokeCopyFwdReadonlyReach
  list finite_map pred_set

Theorem ricf_protection_inherited_no_write:
  ricf_protection_inherited vs C RO p stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract RO V) C.ctx_functions /\
  mem_write_ops inst = SOME ops ==>
  op_prov G ops.iao_ofst <> SOME (p.rpe_db,p.rpe_size) /\
  op_prov G ops.iao_ofst <> SOME (p.rpe_sb,p.rpe_size)
Proof
  simp[ricf_protection_inherited_def] >> rpt strip_tac >>
  metis_tac[readonly_call_reachable_no_write]
QED

Theorem ricf_protection_inherited_call_position:
  ricf_protection_inherited vs C RO p stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract RO V) C.ctx_functions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  k < LENGTH args /\
  (op_prov G (EL k args) = SOME (p.rpe_db,p.rpe_size) \/
   op_prov G (EL k args) = SOME (p.rpe_sb,p.rpe_size)) ==>
  RO nm k
Proof
  simp[ricf_protection_inherited_def] >> rpt strip_tac >>
  metis_tac[readonly_call_reachable_call_position]
QED

Theorem ricf_protection_inherited_next:
  ricf_protection_inherited vs C RO p stk PG G tn fn inst s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_protection_inherited vs C RO p stk PG
    (step_prov PG G inst s') (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[ricf_protection_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_next >> metis_tac[]
QED

Theorem ricf_protection_inherited_block:
  ricf_protection_inherited vs C RO p stk PG G tn fn inst s /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
  ricf_protection_inherited vs C RO p stk PG
    (entry_prov fn s' G) (entry_taint_vars fn s' tn) fn inst' s1
Proof
  simp[ricf_protection_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_block >> metis_tac[]
QED

Theorem ricf_protection_inherited_call:
  ricf_protection_inherited vs C RO p stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_protection_inherited vs C RO p
    (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
Proof
  simp[ricf_protection_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`,
    `<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre`, `atn`] >>
  simp[] >> conj_tac >> irule readonly_call_reachable_call >> metis_tac[]
QED

(* The nonempty prefix is explicit: f is inside the protected activation,
   and is not the anchor belonging to the owner. *)
Theorem ricf_protection_inherited_nested_ret:
  atn.t_var = anchor.cf_tvar /\
  ricf_protection_cursor vs C p [] anchor.cf_params anchor.cf_prov
    atn anchor.cf_fn anchor.cf_state /\
  readonly_call_reachable vs C RO anchor tail (SND p.rpe_dst)
    p.rpe_db p.rpe_size (f::pre) PG G tn fn rinst s /\
  readonly_call_reachable vs C RO anchor tail (SND p.rpe_src)
    p.rpe_sb p.rpe_size (f::pre) PG G tn fn rinst s /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_protection_inherited vs C RO p (pre ++ anchor::tail) f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> simp[ricf_protection_inherited_def] >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_ret >> metis_tac[]
QED

(* Returning to the owner is instead justified by its actual visit prefix.
   No readonly history is popped past its anchor. *)
Theorem ricf_protection_cursor_owner_ret:
  ricf_protection_cursor vs C p [f] PG G tn fn s /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' ==>
  ricf_protection_cursor vs C p [] f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  simp[ricf_protection_cursor_def] >> metis_tac[ricf_visit_prefix_ret]
QED
