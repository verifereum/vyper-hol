Theory concretizePtrChronologicalHistory
Ancestors
  concretizePtrHistoryDemand frameExecutionHistory ptrDiscipline venomExecSemantics venomInst list rich_list
  pred_set codegenRel memLocDefs opcodeClass concretizeMemLocDefs

(* Full observations, including completed activations, never popped on return. *)
Datatype:
  ptr_observation = <| po_stack : call_frame list;
    po_params : (num # num) option list;
    po_prov : (string, num # num) fmap;
    po_taint : taint;
    po_fn : ir_function;
    po_inst : instruction;
    po_state : venom_state |>
End

Definition ptr_observe_def:
  ptr_observe stk PG G tn fn inst s =
    <| po_stack := stk; po_params := PG; po_prov := G; po_taint := tn;
       po_fn := fn; po_inst := inst; po_state := s |>
End

Definition ptr_observation_reachable_def:
  ptr_observation_reachable vs0 ctx obs <=>
    frame_reachable vs0 ctx obs.po_stack obs.po_params obs.po_prov obs.po_taint
      obs.po_fn obs.po_inst obs.po_state
End

Inductive ptr_chrono_step:
[~next:]
  (!ctx stk PG G tn fn inst inst' s s' fuel.
     active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_chrono_step ctx (ptr_observe stk PG G tn fn inst s)
       (ptr_observe stk PG (step_prov PG G inst s')
         (step_taint inst s s' tn) fn inst'
         (s' with vs_inst_idx := SUC s.vs_inst_idx)))
[~block:]
  (!ctx stk PG G tn fn inst inst' s s' s1 fuel.
     active_inst fn inst s /\ is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     ptr_chrono_step ctx (ptr_observe stk PG G tn fn inst s)
       (ptr_observe stk PG (entry_prov fn s' G)
         (entry_taint_vars fn s' tn) fn inst' s1))
[~call:]
  (!ctx stk PG G tn caller inv s nm ops callee args cs s1 inst.
     active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
     decode_invoke inv = SOME (nm,ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     ptr_chrono_step ctx (ptr_observe stk PG G tn caller inv s)
       (ptr_observe
         (<| cf_fn := caller; cf_inst := inv; cf_state := s;
             cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
         (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1))
[~ret:]
  (!ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel.
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
     active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     ptr_chrono_step ctx (ptr_observe (f::stk) PG G tn fn rinst s)
       (ptr_observe stk f.cf_params
         (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
         (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
         f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)))
End

Theorem ptr_chrono_step_reachable:
  !ctx a b. ptr_chrono_step ctx a b ==>
    !vs0. ptr_observation_reachable vs0 ctx a ==>
      ptr_observation_reachable vs0 ctx b
Proof
  ho_match_mp_tac ptr_chrono_step_ind >>
  simp[ptr_observation_reachable_def, ptr_observe_def] >>
  rpt strip_tac >> metis_tac[frame_reachable_rules]
QED

Inductive ptr_chrono_history:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     ptr_chrono_history vs0 ctx
       [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
       (ptr_observe [] [] FEMPTY entry_taint fn inst s1))
[~snoc:]
  (!vs0 ctx h a b.
     ptr_chrono_history vs0 ctx h a /\ ptr_chrono_step ctx a b ==>
     ptr_chrono_history vs0 ctx (h ++ [b]) b)
End

Theorem ptr_chrono_history_reachable:
  !vs0 ctx h a. ptr_chrono_history vs0 ctx h a ==>
    ptr_observation_reachable vs0 ctx a /\
    EVERY (ptr_observation_reachable vs0 ctx) h
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- (simp[ptr_observation_reachable_def, ptr_observe_def] >>
      metis_tac[frame_reachable_rules]) >>
  rpt strip_tac >> gvs[EVERY_APPEND] >>
  metis_tac[ptr_chrono_step_reachable]
QED

Theorem ptr_chrono_history_end:
  !vs0 ctx h a. ptr_chrono_history vs0 ctx h a ==> h <> [] /\ LAST h = a
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> simp[LAST_APPEND]
QED

Theorem ptr_reachable_has_chrono_history:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    ?h. ptr_chrono_history vs0 ctx h (ptr_observe stk PG G tn fn inst s)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >>
  metis_tac[ptr_chrono_history_rules, ptr_chrono_step_rules]
QED

(* Only ordinary steps can remove memory taint. The witness carries an
   actual successful execution, not merely a syntactic memory operand. *)
Definition ptr_chrono_write_def:
  ptr_chrono_write ctx x obs <=>
    ~is_terminator obs.po_inst.inst_opcode /\ obs.po_inst.inst_opcode <> INVOKE /\
    (?fuel s'. step_inst fuel ctx obs.po_inst obs.po_state = OK s') /\
    x IN range_bytes (source_memory_write_ranges obs.po_inst obs.po_state)
End

Theorem ptr_chrono_ordinary_step_success:
  !C a z. ptr_chrono_step C a z ==>
    ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE ==>
    ?fuel s'. step_inst fuel C a.po_inst a.po_state = OK s'
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac >>
  simp[ptr_observe_def] >> rpt strip_tac
  >- metis_tac[] >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem ptr_write_size_ordinary:
  inst_write_size inst = SOME n ==>
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def, is_terminator_def]
QED

Theorem ptr_chrono_range_write:
  ptr_chrono_step C a z /\ inst_write_size a.po_inst = SOME n /\
  x IN range_bytes (source_memory_write_ranges a.po_inst a.po_state) ==>
  ptr_chrono_write C x a
Proof
  strip_tac >> drule ptr_write_size_ordinary >> strip_tac >>
  drule_all ptr_chrono_ordinary_step_success >>
  simp[ptr_chrono_write_def]
QED

Theorem ptr_chrono_step_mem:
  !ctx a b. ptr_chrono_step ctx a b ==>
    !x. x IN a.po_taint.t_mem /\ x NOTIN b.po_taint.t_mem ==>
      ptr_chrono_write ctx x a
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac
  >- (simp[ptr_observe_def, ptr_chrono_write_def] >> rpt strip_tac
      >- (qexistsl [`fuel`,`s'`] >> simp[]) >>
      metis_tac[ptr_step_mem_no_write])
  >- (simp[ptr_observe_def, entry_taint_vars_def] >>
      rpt gen_tac >> CASE_TAC >> simp[]) >>
  simp[ptr_observe_def]
QED

Theorem ptr_chrono_step_alloca:
  ptr_chrono_step ctx a b /\ a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' ==>
  x IN b.po_taint.t_mem
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def, step_inst_non_invoke] >>
  `x NOTIN range_bytes (source_memory_write_ranges inst s)` by
    simp[source_memory_write_ranges_def, mem_write_ops_def, range_bytes_def] >>
  metis_tac[ptr_step_mem_no_write]
QED

Theorem ptr_chrono_fresh_no_write:
  !vs0 ctx h endpoint. ptr_chrono_history vs0 ctx h endpoint ==>
    !pre a tail fuel sa' x.
    h = pre ++ [a] ++ tail /\ tail <> [] /\
    a.po_inst.inst_opcode = ALLOCA /\
    step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
    x IN new_site_bytes a.po_state sa' /\
    EVERY (\obs. ~ptr_chrono_write ctx x obs) (FRONT tail) ==>
    x IN endpoint.po_taint.t_mem
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt strip_tac >> Cases_on `pre` >> gvs[] >>
      Cases_on `tail` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ptr_history_split_snoc >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  Cases_on `FRONT tail = []`
  >- (gvs[LAST_APPEND] >> metis_tac[ptr_chrono_step_alloca]) >>
  `LAST (FRONT tail) = endpoint` by
    (qpat_x_assum `LAST h = _` mp_tac >>
     qpat_x_assum `h = _` (fn th => rewrite_tac[th]) >>
     Cases_on `FRONT tail` >> fs[LAST_APPEND]) >>
  `EVERY (\obs. ~ptr_chrono_write ctx x obs) (FRONT (FRONT tail)) /\
   ~ptr_chrono_write ctx x endpoint` by
    (conj_tac >- (irule ptr_every_front >> simp[]) >>
     drule_all ptr_every_last >> simp[]) >>
  `x IN endpoint.po_taint.t_mem` by
    (first_x_assum irule >>
     qexistsl [`a`,`fuel`,`pre`,`sa'`,`FRONT tail`] >> simp[]) >>
  metis_tac[ptr_chrono_step_mem]
QED

Theorem ptr_chrono_fresh_write:
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem ==>
  EXISTS (ptr_chrono_write ctx x) (FRONT tail)
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `EVERY (\obs. ~ptr_chrono_write ctx x obs) (FRONT tail)` by
    gvs[listTheory.NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[ptr_chrono_fresh_no_write]
QED

(* k is strictly after the allocation boundary and before the final boundary.
   Its observation includes the writer's own activation and all ghost fields. *)
Theorem ptr_chrono_fresh_write_index:
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem ==>
  ?k. LENGTH pre < k /\ k + 1 < LENGTH h /\
      ptr_chrono_write ctx x (EL k h) /\
      ptr_observation_reachable vs0 ctx (EL k h)
Proof
  strip_tac >> drule_all ptr_chrono_fresh_write >>
  simp[EXISTS_MEM, MEM_EL] >> strip_tac >>
  qexists `LENGTH pre + 1 + n` >>
  `tail = FRONT tail ++ [LAST tail]` by metis_tac[APPEND_FRONT_LAST] >>
  `EL (LENGTH pre + 1 + n) h = EL n (FRONT tail)` by
    (qpat_x_assum `h = _` (fn th => rewrite_tac[th]) >>
     simp[EL_APPEND_EQN] >>
     qpat_x_assum `tail = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_APPEND_EQN, FRONT_APPEND]) >>
  `LENGTH tail = LENGTH (FRONT tail) + 1` by
    (qpat_x_assum `tail = _` mp_tac >> disch_then (mp_tac o AP_TERM ``LENGTH:ptr_observation list -> num``) >> simp[]) >>
  conj_tac >- decide_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
  metis_tac[]
QED

(* Interface report (C1.5.37):
   - ptr_reachable_has_chrono_history covers every frame_reachable endpoint.
   - ptr_chrono_history_reachable erases both the endpoint and EVERY recorded
     observation, preserving the exact stack, PG, G and tn.
   - ptr_chrono_fresh_write_index finds an ordinary successful writer at k,
     LENGTH pre < k and k+1 < LENGTH h. Completed callees are retained by snoc;
     no INVOKE-only escape is present. ALLOCA taints the new bytes; block,
     call and return preserve t_mem exactly, so no extra terminator fact is
     required. The allocation transition and writer need not be in one frame.
   This is byte initialization evidence, not allocation-id identity or lifetime
   separation. No production-demand or layout-safety conclusion is asserted.
   Four existing local list/taint interfaces in HistoryDemand are exported
   unchanged to avoid duplicate lemmas; no existing proof is refactored. *)
