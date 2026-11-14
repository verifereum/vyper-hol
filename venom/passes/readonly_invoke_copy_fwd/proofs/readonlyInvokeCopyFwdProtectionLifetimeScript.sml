(* Relevance is a syntactic lifetime, not a memory exclusion.  Inherited
   translation maps are deliberately not arguments of this predicate. *)
Theory readonlyInvokeCopyFwdProtectionLifetime
Ancestors
  readonlyInvokeCopyFwdProtection readonlyInvokeCopyFwdProtectionInherited
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdDefs
  invokeCopyFwdCommonDefs list rich_list pred_set

Definition ricf_selected_position_def:
  ricf_selected_position e bb j <=>
    ?inst pos. MEM (inst,pos) e.rfe_sites /\
      findi (\el. el.inst_id = inst.inst_id) bb.bb_instructions = SOME j
End

Definition ricf_remaining_selected_use_def:
  ricf_remaining_selected_use p s <=>
    s.vs_current_bb = p.rpe_block.bb_label /\
    ?j. ricf_selected_position p.rpe_event p.rpe_block j /\
        s.vs_inst_idx <= j
End

Definition ricf_outstanding_selected_def:
  ricf_outstanding_selected p pre <=>
    ?f. MEM f pre /\ f.cf_state.vs_current_bb = p.rpe_block.bb_label /\
      ricf_selected_position p.rpe_event p.rpe_block f.cf_state.vs_inst_idx /\
      f.cf_inst.inst_opcode = INVOKE /\
      f.cf_inst = EL f.cf_state.vs_inst_idx p.rpe_block.bb_instructions
End

Definition ricf_active_use_def:
  ricf_active_use p pre s <=>
    ricf_remaining_selected_use p (ricf_visit_owner_state pre s) \/
    ricf_outstanding_selected p pre
End

Theorem ricf_active_use_owner:
  ricf_active_use p [] s <=> ricf_remaining_selected_use p s
Proof
  simp[ricf_active_use_def, ricf_visit_owner_state_def,
       ricf_outstanding_selected_def]
QED

(* A selected call stays relevant even after the last rewrite position was
   entered: its actual saved frame remains until the matching return. *)
Theorem ricf_active_use_outstanding:
  ricf_outstanding_selected p pre ==> ricf_active_use p pre s
Proof
  simp[ricf_active_use_def]
QED

Theorem ricf_active_use_selected_call:
  f.cf_state.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block f.cf_state.vs_inst_idx /\
  f.cf_inst.inst_opcode = INVOKE /\
  f.cf_inst = EL f.cf_state.vs_inst_idx p.rpe_block.bb_instructions ==>
  ricf_active_use p (inner ++ f::outer) s
Proof
  simp[ricf_active_use_def, ricf_outstanding_selected_def, MEM_APPEND] >>
  metis_tac[]
QED

Theorem ricf_active_use_finished:
  ~ricf_outstanding_selected p pre /\
  ~ricf_remaining_selected_use p (ricf_visit_owner_state pre s) ==>
  ~ricf_active_use p pre s
Proof
  simp[ricf_active_use_def]
QED

Theorem ricf_active_use_final_return:
  ~ricf_remaining_selected_use p
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ~ricf_active_use p []
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  simp[ricf_active_use_owner]
QED

(* Cursor histories may cross an unselected or mutable call.  This produces
   no inherited readonly history and makes no assertion about memory. *)
Theorem ricf_protection_cursor_call:
  !vs C p pre PG G tn caller s inv nm ops callee args cs s1.
  ricf_protection_cursor vs C p pre PG G tn caller s /\
  active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
  decode_invoke inv = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 ==>
  ricf_protection_cursor vs C p
    (<| cf_fn := caller; cf_inst := inv; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
Proof
  simp[ricf_protection_cursor_def] >> metis_tac[ricf_visit_prefix_call]
QED

(* Acceptance excludes analyzed clobbers, not arbitrary semantic writes.
   Consumers must still align bp/alias locations with the actual endpoints. *)
Theorem ricf_event_no_src_clobber:
  ricf_event_ok e bb ==>
  ~icf_has_src_clobber e.rfe_ctx.icf_aliases e.rfe_ctx.icf_bp
    bb.bb_instructions e.rfe_index
    (MAP THE (MAP (\(inst,pos).
      findi (\el. el.inst_id = inst.inst_id) bb.bb_instructions) e.rfe_sites))
    (bp_get_read_location e.rfe_ctx.icf_bp (ricf_event_copy e bb) AddrSp_Memory)
Proof
  simp[ricf_event_ok_def, ricf_event_copy_def, ricf_try_forward_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `_ :: _ = e.rfe_sites` (assume_tac o SYM) >> gvs[]
QED

Theorem ricf_event_intervening_alias_exclusion:
  ricf_event_ok e bb /\
  loc = bp_get_read_location e.rfe_ctx.icf_bp
          (ricf_event_copy e bb) AddrSp_Memory /\
  loc.ml_size <> SOME 0 /\
  ricf_selected_position e bb j /\ e.rfe_index < k /\ k < j /\
  Eff_MEMORY IN write_effects (EL k bb.bb_instructions).inst_opcode ==>
  ~ma_may_alias e.rfe_ctx.icf_aliases loc
    (bp_get_write_location e.rfe_ctx.icf_bp
      (EL k bb.bb_instructions) AddrSp_Memory)
Proof
  strip_tac >> drule ricf_event_no_src_clobber >>
  simp[icf_has_src_clobber_def, EXISTS_MEM, MEM_COUNT_LIST] >>
  gvs[ricf_selected_position_def] >>
  disch_then (qspec_then `j` mp_tac) >>
  `MEM j (MAP THE (MAP (\(inst,pos).
     findi (\el. el.inst_id = inst.inst_id) bb.bb_instructions) e.rfe_sites))`
    by (simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
        metis_tac[optionTheory.THE_DEF]) >>
  simp[] >>
  disch_then (qspec_then `k - e.rfe_index - 1` mp_tac) >>
  `k - e.rfe_index - 1 < j - (e.rfe_index + 1)` by decide_tac >>
  `k - e.rfe_index - 1 + (e.rfe_index + 1) = k` by decide_tac >>
  simp[]
QED

(* An actual matching return restores the cursor even when relevance ends.
   Nothing here deletes sites/maps or asserts inherited_start for a later call. *)
Theorem ricf_protection_last_selected_return:
  ricf_protection_cursor vs C p [f] PG G tn fn s /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  ~ricf_remaining_selected_use p
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_protection_cursor vs C p [] f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  ~ricf_active_use p [] (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  metis_tac[ricf_protection_cursor_owner_ret, ricf_active_use_final_return]
QED

(* The readonly premise of inherited_start genuinely rejects a mutable
   endpoint argument.  A cursor_call above intentionally needs no such premise. *)
Theorem ricf_mutable_endpoint_not_readonly_start:
  k < LENGTH ops /\ op_prov G (EL k ops) = SOME endpoint /\ ~RO nm k ==>
  ~(!j. j < LENGTH ops /\ op_prov G (EL j ops) = SOME endpoint ==> RO nm j)
Proof
  metis_tac[]
QED

(* Explicit analysis alignment: an endpoint-relevant semantic write cannot
   occur in the analyzed interval IF its location is reflected by may_alias.
   The implication is not bundled into relevance or event validity. *)
Theorem ricf_event_intervening_endpoint_exclusion:
  ricf_event_ok e bb /\
  loc = bp_get_read_location e.rfe_ctx.icf_bp
          (ricf_event_copy e bb) AddrSp_Memory /\
  loc.ml_size <> SOME 0 /\
  ricf_selected_position e bb j /\ e.rfe_index < k /\ k < j /\
  Eff_MEMORY IN write_effects (EL k bb.bb_instructions).inst_opcode /\
  (relevant ==> ma_may_alias e.rfe_ctx.icf_aliases loc
    (bp_get_write_location e.rfe_ctx.icf_bp
      (EL k bb.bb_instructions) AddrSp_Memory)) ==>
  ~relevant
Proof
  metis_tac[ricf_event_intervening_alias_exclusion]
QED
