(* Least instruction-site reachability for the code-generation package.
 * Entry and block transitions expose states after PHIs; ordinary steps
 * expose the incremented instruction index, including aggregate INVOKE returns.
 *)
Theory contextReachability
Ancestors
  contextCodegenRel contextCodegenRelProps

Inductive raw_inst_reachable:
[~entry:]
  (!initial_vs ctx name fn lbl s1 inst.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    enters_block fn
      (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>) s1 /\
    active_inst fn inst s1 ==>
    raw_inst_reachable initial_vs ctx fn inst s1)
[~next:]
  (!initial_vs ctx fn inst inst' s s' fuel.
    raw_inst_reachable initial_vs ctx fn inst s /\ active_inst fn inst s /\
    ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    raw_inst_reachable initial_vs ctx fn inst'
      (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!initial_vs ctx fn inst inst' s s' s1 fuel.
    raw_inst_reachable initial_vs ctx fn inst s /\ active_inst fn inst s /\
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
    ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    raw_inst_reachable initial_vs ctx fn inst' s1)
[~callee:]
  (!initial_vs ctx caller inv s nm ops callee args cs s1 inst.
    raw_inst_reachable initial_vs ctx caller inv s /\ active_inst caller inv s /\
    inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    raw_inst_reachable initial_vs ctx callee inst s1)
End

Theorem raw_inst_reachable_active:
  !initial_vs ctx fn inst s.
    raw_inst_reachable initial_vs ctx fn inst s ==> active_inst fn inst s
Proof
  ho_match_mp_tac raw_inst_reachable_ind >> simp[]
QED

Theorem raw_inst_reachable_closed:
  reachability_closed (raw_inst_reachable initial_vs) ctx
Proof
  rewrite_tac[reachability_closed_def, fn_entry_inv_def] >>
  conj_tac >- metis_tac[raw_inst_reachable_next] >>
  conj_tac >- metis_tac[raw_inst_reachable_block] >>
  metis_tac[raw_inst_reachable_callee]
QED

Theorem raw_inst_reachable_fn_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  fn_entry_inv (raw_inst_reachable initial_vs) ctx fn
    (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0 |>)
Proof
  rewrite_tac[fn_entry_inv_def] >>
  metis_tac[raw_inst_reachable_entry]
QED

(* An executable entry instruction is not required by the existing package:
 * a valid lookup/label witness may have an empty or failing PHI entry. *)
Theorem raw_inst_reachable_package:
  codegen_reachability_package (raw_inst_reachable initial_vs) ctx initial_vs <=>
  ?name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
Proof
  rewrite_tac[codegen_reachability_package_def] >>
  simp[raw_inst_reachable_closed] >>
  metis_tac[raw_inst_reachable_fn_entry]
QED

Theorem raw_inst_reachable_minimal:
  codegen_reachability_package Inv ctx initial_vs ==>
  !fn inst s. raw_inst_reachable initial_vs ctx fn inst s ==> Inv ctx fn inst s
Proof
  `!initial_vs ctx fn inst s.
     raw_inst_reachable initial_vs ctx fn inst s ==>
     codegen_reachability_package Inv ctx initial_vs ==> Inv ctx fn inst s`
    suffices_by metis_tac[] >>
  ho_match_mp_tac raw_inst_reachable_ind >>
  rpt conj_tac
  >- (rpt strip_tac >> drule codegen_reachability_package_entry >>
      strip_tac >> gvs[] >> metis_tac[fn_entry_inv_active])
  >- metis_tac[codegen_reachability_package_entry, reachability_closed_next]
  >- metis_tac[codegen_reachability_package_entry, reachability_closed_block] >>
  metis_tac[codegen_reachability_package_entry, reachability_closed_callee,
            fn_entry_inv_active]
QED
