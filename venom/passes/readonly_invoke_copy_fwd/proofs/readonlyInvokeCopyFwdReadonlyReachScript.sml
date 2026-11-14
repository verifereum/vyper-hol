(* Readonly protection is scoped to a callee activation, not its owner. *)
Theory readonlyInvokeCopyFwdReadonlyReach
Ancestors
  readonlyProvenanceSupport readonlyInheritedSiteGeometry occurrenceGeometry
  o1LowerDloadOccurrence ptrDiscipline venomExecSemantics venomInst
  venomExecProps contextCodegenRel o1PassContract finite_map pred_set list

(* A saved allocation has an occurrence owner among the suspended frames. *)
Theorem readonly_saved_allocation_owner:
  !U stk. occurrence_saved_ok B U stk /\ MEM f stk /\
    FLOOKUP f.cf_state.vs_allocas aid = SOME q ==>
    ?owner. MEM owner (MAP (\u. u.of_owner) U) /\
            FLOOKUP B (owner,aid) = SOME q
Proof
  Induct >> simp[occurrence_saved_ok_def] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `h.of_owner` >> gvs[occurrence_allocas_ok_def]) >>
  metis_tac[]
QED

Theorem readonly_saved_alloca_step_exclusion:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn active s /\ MEM f stk /\
  FLOOKUP f.cf_state.vs_allocas aid = SOME (b,z) /\ 0 < z /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' ==>
  FLOOKUP s'.vs_allocas inst.inst_id <> SOME (b,z)
Proof
  strip_tac >> drule_all frame_reachable_inherited_site_exclusion >> strip_tac >>
  `?owner. MEM owner (MAP (\u. u.of_owner) U) /\
    FLOOKUP B (owner,aid) = SOME (b,z)` by
    (irule readonly_saved_allocation_owner >>
     gvs[occurrence_annotation_ok_def] >> metis_tac[]) >>
  metis_tac[inherited_site_alloca_step_exclusion, arithmeticTheory.ZERO_LESS_EQ]
QED

(* pre contains only callers suspended inside the protected activation.
   anchor belongs to the owning caller and is never popped by these rules. *)
Inductive readonly_call_reachable:
[~start:]
  (!vs C RO caller inv s stk PG G tn nm ops callee args cs s1 inst aid b z.
    frame_reachable vs C stk PG G tn caller inv s /\
    active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 /\
    FLOOKUP s.vs_allocas aid = SOME (b,z) /\ 0 < z /\
    (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (b,z) ==> RO nm k) ==>
    readonly_call_reachable vs C RO
      <| cf_fn := caller; cf_inst := inv; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>
      stk aid b z [] (MAP (op_prov G) ops) FEMPTY
      (tn with t_var := FEMPTY) callee inst s1)
[~next:]
  (!vs C RO anchor tail aid b z pre PG G tn fn inst inst' s s' fuel.
    readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s /\
    active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    readonly_call_reachable vs C RO anchor tail aid b z pre PG
      (step_prov PG G inst s') (step_taint inst s s' tn) fn inst'
      (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs C RO anchor tail aid b z pre PG G tn fn inst inst' s s' s1 fuel.
    readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s /\
    active_inst fn inst s /\ is_terminator inst.inst_opcode /\
    step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
    enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    readonly_call_reachable vs C RO anchor tail aid b z pre PG
      (entry_prov fn s' G) (entry_taint_vars fn s' tn) fn inst' s1)
[~call:]
  (!vs C RO anchor tail aid b z pre PG G tn caller inv s nm ops callee args cs s1 inst.
    readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn caller inv s /\
    active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    readonly_call_reachable vs C RO anchor tail aid b z
      (<| cf_fn := caller; cf_inst := inv; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1)
[~ret:]
  (!vs C RO anchor tail aid b z f pre PG G tn fn rinst s ret se s' inst' fuel.
    readonly_call_reachable vs C RO anchor tail aid b z (f::pre) PG G tn fn rinst s /\
    active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
    active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
    readonly_call_reachable vs C RO anchor tail aid b z pre f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

Theorem readonly_call_reachable_projection:
  !vs C RO anchor tail aid b z pre PG G tn fn inst s.
    readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s ==>
    frame_reachable vs C (pre ++ anchor::tail) PG G tn fn inst s /\
    FLOOKUP anchor.cf_state.vs_allocas aid = SOME (b,z) /\ 0 < z /\
    active_inst fn inst s
Proof
  ho_match_mp_tac readonly_call_reachable_ind >> rpt strip_tac >>
  gvs[] >> metis_tac[frame_reachable_rules]
QED

Theorem readonly_reachable_static:
  frame_reachable vs C stk PG G tn fn inst s /\
  EVERY (readonly_origin_contract RO V) C.ctx_functions /\ ~ctx_has_dalloca C ==>
  readonly_origin_contract RO V fn /\ inst.inst_opcode <> DALLOCA /\
  MEM inst (fn_insts fn)
Proof
  strip_tac >> drule frame_reachable_occurrence_lift >> strip_tac >>
  drule occ_frame_reachable_annotation >> strip_tac >>
  `active_inst fn inst s` by
    (gvs[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  gvs[EVERY_MEM, ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem readonly_call_param_support:
  readonly_origin_contract RO V fn /\ readonly_site_support V fn G q /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee ==>
  readonly_param_support RO callee (MAP (op_prov G) ops) q
Proof
  strip_tac >>
  `callee.fn_name = nm` by
    (gvs[lookup_function_def] >> drule venomExecProofsTheory.FIND_P >> simp[]) >>
  simp[readonly_param_support_def] >> rpt strip_tac >> gvs[EL_MAP] >>
  irule readonly_site_support_call >> metis_tac[]
QED

Definition readonly_saved_support_def:
  readonly_saved_support RO V q f <=>
    readonly_site_support V f.cf_fn f.cf_prov q /\
    readonly_param_support RO f.cf_fn f.cf_params q
End

Theorem readonly_call_reachable_support:
  !vs C RO anchor tail aid b z pre PG G tn fn inst s.
    readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s ==>
    !V. vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
      EVERY (readonly_origin_contract RO V) C.ctx_functions ==>
    readonly_site_support V fn G (b,z) /\
    readonly_param_support RO fn PG (b,z) /\
    EVERY (readonly_saved_support RO V (b,z)) pre
Proof
  ho_match_mp_tac readonly_call_reachable_strongind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume readonly_call_reachable_support[start]:
  rpt strip_tac >> simp[] >>
  `fn.fn_name = nm` by
    (gvs[lookup_function_def] >> drule venomExecProofsTheory.FIND_P >> simp[]) >>
  simp[readonly_param_support_def] >> rpt strip_tac >> gvs[EL_MAP]
QED

Resume readonly_call_reachable_support[next]:
  rpt strip_tac >> first_x_assum (qspec_then `V` mp_tac) >> simp[] >> strip_tac >>
  drule readonly_call_reachable_projection >> strip_tac >>
  `readonly_origin_contract RO V fn /\ inst.inst_opcode <> DALLOCA /\
    MEM inst (fn_insts fn)` by (irule readonly_reachable_static >> metis_tac[]) >>
  `inst.inst_opcode = ALLOCA ==> FLOOKUP s'.vs_allocas inst.inst_id <> SOME (b,z)` by
    (strip_tac >> irule readonly_saved_alloca_step_exclusion >>
     simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  metis_tac[readonly_site_support_step]
QED

Resume readonly_call_reachable_support[block]:
  rpt strip_tac >> first_x_assum (qspec_then `V` mp_tac) >> simp[] >> strip_tac >>
  drule readonly_call_reachable_projection >> strip_tac >>
  `readonly_origin_contract RO V fn` by metis_tac[readonly_reachable_static] >>
  simp[] >> metis_tac[readonly_site_support_entry]
QED

Resume readonly_call_reachable_support[call]:
  rpt strip_tac >> first_x_assum (qspec_then `V` mp_tac) >> simp[] >> strip_tac >>
  drule readonly_call_reachable_projection >> strip_tac >>
  `readonly_origin_contract RO V fn /\ MEM inst (fn_insts fn)` by
    metis_tac[readonly_reachable_static] >>
  simp[readonly_saved_support_def] >> irule readonly_call_param_support >> metis_tac[]
QED

Resume readonly_call_reachable_support[ret]:
  rpt strip_tac >> first_x_assum (qspec_then `V` mp_tac) >>
  simp[readonly_saved_support_def] >> strip_tac >>
  metis_tac[readonly_site_support_restrict]
QED

Finalise readonly_call_reachable_support

Theorem readonly_call_reachable_no_write:
  readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract RO V) C.ctx_functions /\
  mem_write_ops inst = SOME ops ==>
  op_prov G ops.iao_ofst <> SOME (b,z)
Proof
  strip_tac >> drule readonly_call_reachable_support >>
  disch_then (qspec_then `V` mp_tac) >> simp[] >> strip_tac >>
  drule readonly_call_reachable_projection >> strip_tac >>
  drule_all readonly_reachable_static >> strip_tac >>
  metis_tac[readonly_site_support_no_write]
QED

Theorem readonly_call_reachable_call_position:
  readonly_call_reachable vs C RO anchor tail aid b z pre PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract RO V) C.ctx_functions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  k < LENGTH args /\ op_prov G (EL k args) = SOME (b,z) ==>
  RO nm k
Proof
  strip_tac >> drule readonly_call_reachable_support >>
  disch_then (qspec_then `V` mp_tac) >> simp[] >> strip_tac >>
  drule readonly_call_reachable_projection >> strip_tac >>
  drule_all readonly_reachable_static >> strip_tac >>
  metis_tac[readonly_site_support_call]
QED
