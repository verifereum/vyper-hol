(* Static frame interface for an active renamed callee and suspended caller. *)
Theory functionInlinerFrame
Ancestors
  functionInlinerReturnBoundary stateFrame venomExecProofs venomState finite_map pred_set
  o1FrameLockstep venomExecSemantics passSharedProps functionInlinerDefs
  fnFrameBoundaryGenRet functionInlinerOpacity

(* Ignore only frame-local call bookkeeping, in addition to execution control.
   In particular fmp, memory, oracle streams and observable effects remain. *)
Definition inline_shared_frame_def:
  inline_shared_frame s = execution_frame (s with <|
    vs_params := []; vs_call_entry_fmp := 0w; vs_return_pc_token := 0w;
    vs_allocas := FEMPTY; vs_alloca_next := 0 |>)
End

Definition inline_frame_rel_def:
  inline_frame_rel rho V saved P s t <=>
    inline_shared_frame s = inline_shared_frame t /\
    (!v. v IN V ==> lookup_var v s = lookup_var (rho v) t) /\
    (!p. p IN P ==> FLOOKUP t.vs_vars p = FLOOKUP saved p)
End

Definition inline_rename_operand_def:
  (inline_rename_operand rho lab (Lit w) = Lit w) /\
  (inline_rename_operand rho lab (Var v) = Var (rho v)) /\
  (inline_rename_operand rho lab (Label l) = Label (lab l))
End

Theorem inline_frame_eval_operand:
  !rho V saved P s t lab op.
    inline_frame_rel rho V saved P s t /\
    (!v. op = Var v ==> v IN V) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)) ==>
    eval_operand (inline_rename_operand rho lab op) t = eval_operand op s
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[inline_rename_operand_def, eval_operand_def, inline_frame_rel_def] >>
  metis_tac[]
QED

Theorem inline_frame_eval_operands:
  !ops rho V saved P s t lab.
    inline_frame_rel rho V saved P s t /\
    EVERY (\op. (!v. op = Var v ==> v IN V) /\
      (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l))) ops ==>
    eval_operands (MAP (inline_rename_operand rho lab) ops) t = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  rename1 `inline_frame_rel ren V saved P s t` >>
  `eval_operand (inline_rename_operand ren lab h) t = eval_operand h s` by
    (irule inline_frame_eval_operand >> metis_tac[]) >>
  simp[] >> first_x_assum drule >> simp[]
QED

Theorem inline_shared_frame_update_var[simp]:
  inline_shared_frame (update_var x w s) = inline_shared_frame s
Proof
  simp[inline_shared_frame_def, execution_frame_def, update_var_def]
QED

Theorem inline_frame_write_disjoint:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> ren v <> x) /\ x NOTIN P ==>
  inline_frame_rel ren V saved P s (update_var x w t)
Proof
  simp[inline_frame_rel_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem inline_frame_write_renamed:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P ==>
  inline_frame_rel ren V saved P (update_var x w s) (update_var (ren x) w t)
Proof
  simp[inline_frame_rel_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem inline_frame_writes_disjoint:
  !pairs ren V saved P s t.
    inline_frame_rel ren V saved P s t /\
    EVERY (\p. (!v. v IN V ==> ren v <> FST p) /\ FST p NOTIN P) pairs ==>
    inline_frame_rel ren V saved P s
      (FOLDL (\t (x,w). update_var x w t) t pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  irule inline_frame_write_disjoint >> metis_tac[]
QED

(* Every return source is evaluated in the original callee snapshot even
   after any prefix of the caller-output writes has executed. *)
Theorem inline_frame_return_snapshot:
  inline_frame_rel ren V saved P s t /\
  EVERY (\p. (!v. v IN V ==> ren v <> FST p) /\ FST p NOTIN P) pairs /\
  EVERY (\op. (!v. op = Var v ==> v IN V) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l))) ops ==>
  eval_operands (MAP (inline_rename_operand ren lab) ops)
    (FOLDL (\t (x,w). update_var x w t) t pairs) = eval_operands ops s
Proof
  rpt strip_tac >> irule inline_frame_eval_operands >>
  qexistsl [`P`, `V`, `saved`] >> conj_tac
  >- simp[foldl_update_var_labels] >>
  irule inline_frame_writes_disjoint >> metis_tac[]
QED

Theorem inline_shared_frame_setup:
  setup_callee fn args s = SOME cs /\ ~s.vs_halted ==>
  inline_shared_frame cs = inline_shared_frame s
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[inline_shared_frame_def, execution_frame_def,
    venom_state_component_equality]
QED

Theorem inline_frame_fmp:
  inline_frame_rel ren V saved P s t ==> s.vs_fmp = t.vs_fmp
Proof
  simp[inline_frame_rel_def] >> strip_tac >>
  qpat_x_assum `inline_shared_frame s = inline_shared_frame t`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_fmp``) >>
  simp[inline_shared_frame_def, execution_frame_def]
QED

Theorem inline_frame_getfmp_write:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P ==>
  inline_frame_rel ren V saved P
    (update_var x s.vs_fmp s) (update_var (ren x) t.vs_fmp t)
Proof
  rpt strip_tac >> `s.vs_fmp = t.vs_fmp` by metis_tac[inline_frame_fmp] >>
  simp[] >> irule inline_frame_write_renamed >> metis_tac[]
QED

Theorem inline_frame_parameter_write:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  i < LENGTH s.vs_params /\ eval_operand arg t = SOME (EL i s.vs_params) ==>
  ?w. eval_operand arg t = SOME w /\
    inline_frame_rel ren V saved P
      (update_var x (EL i s.vs_params) s) (update_var (ren x) w t)
Proof
  rpt strip_tac >> qexists `EL i s.vs_params` >> simp[] >>
  irule inline_frame_write_renamed >> metis_tac[]
QED

Theorem inline_frame_retpc_zero_write:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  s.vs_return_pc_token = 0w ==>
  inline_frame_rel ren V saved P
    (update_var x s.vs_return_pc_token s) (update_var (ren x) 0w t)
Proof
  rpt strip_tac >> simp[] >> irule inline_frame_write_renamed >> metis_tac[]
QED

Definition inline_rename_inst_def:
  inline_rename_inst ren lab inst = inst with <|
    inst_operands := MAP (inline_rename_operand ren lab) inst.inst_operands;
    inst_outputs := MAP ren inst.inst_outputs |>
End

Theorem inline_rename_resolve_phi:
  !prev ops ren lab.
    (!l. lab l = lab prev <=> l = prev) ==>
    resolve_phi (lab prev) (MAP (inline_rename_operand ren lab) ops) =
      OPTION_MAP (inline_rename_operand ren lab) (resolve_phi prev ops)
Proof
  recInduct resolve_phi_ind >>
  simp[resolve_phi_def, inline_rename_operand_def] >>
  rpt strip_tac >> gvs[inline_rename_operand_def, resolve_phi_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem inline_frame_eval_one_phi:
  inline_frame_rel ren V saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  EVERY (\op. (!v. op = Var v ==> v IN V) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)))
    inst.inst_operands /\
  eval_one_phi s inst = SOME (out,w) ==>
  eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren out,w)
Proof
  rpt strip_tac >>
  `resolve_phi (lab prev) (MAP (inline_rename_operand ren lab) inst.inst_operands) =
    OPTION_MAP (inline_rename_operand ren lab) (resolve_phi prev inst.inst_operands)`
    by (irule inline_rename_resolve_phi >> simp[]) >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  `MEM val_op inst.inst_operands` by metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
  `eval_operand (inline_rename_operand ren lab val_op) t = eval_operand val_op s`
    by (irule inline_frame_eval_operand >> gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[eval_one_phi_def, inline_rename_inst_def]
QED

Theorem inline_frame_eval_phis:
  !insts ren lab V saved P s t u prev.
    inline_frame_rel ren V saved P s t /\
    s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
    (!l. lab l = lab prev <=> l = prev) /\
    EVERY (\inst.
      EVERY (\op. (!v. op = Var v ==> v IN V) /\
        (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)))
        inst.inst_operands /\
      EVERY (\x. (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P)
        inst.inst_outputs) insts /\
    eval_phis s insts = OK u ==>
    ?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
      inline_frame_rel ren V saved P u t'
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, AllCaseEqs()] >>
      `eval_one_phi t (inline_rename_inst ren lab h) = SOME (ren out,v)` by
        (irule inline_frame_eval_one_phi >> metis_tac[]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists `update_var (ren out) v t'` >>
      simp[inline_rename_inst_def] >>
      irule inline_frame_write_renamed >>
      `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
      gvs[]) >>
  gvs[eval_phis_def, inline_rename_inst_def]
QED

Theorem inline_frame_return_assign_step:
  inline_frame_rel ren V saved P s t /\
  EVERY (\p. (!v. v IN V ==> ren v <> FST p) /\ FST p NOTIN P) pairs /\
  (!v. op = Var v ==> v IN V) /\
  (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)) /\
  eval_operand op s = SOME w /\ inst.inst_outputs = [out] ==>
  step_inst fuel ctx (mk_assign_inst inst (inline_rename_operand ren lab op))
    (FOLDL (\t (x,w). update_var x w t) t pairs) =
  OK (update_var out w (FOLDL (\t (x,w). update_var x w t) t pairs))
Proof
  rpt strip_tac >> irule mk_assign_inst_correct >> simp[] >>
  `eval_operands (MAP (inline_rename_operand ren lab) [op])
     (FOLDL (\t (x,w). update_var x w t) t pairs) = eval_operands [op] s`
    by (irule inline_frame_return_snapshot >> simp[] >> metis_tac[]) >>
  gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem inline_frame_rel_fmp_update:
  inline_frame_rel ren V saved P s t ==>
  inline_frame_rel ren V saved P (s with vs_fmp := w) (t with vs_fmp := w)
Proof
  simp[inline_frame_rel_def, lookup_var_def] >> strip_tac >>
  qpat_x_assum `inline_shared_frame s = inline_shared_frame t`
    (mp_tac o AP_TERM ``\u:venom_state. u with vs_fmp := w``) >>
  simp[inline_shared_frame_def, execution_frame_def]
QED

Theorem inline_frame_retfmp_adopt:
  inline_frame_rel ren V saved P s t ==>
  inline_frame_rel ren V saved P
    (adopt_return_fmp <|iret_values := vals; iret_adopt_fmp := SOME t.vs_fmp|> s) t
Proof
  rpt strip_tac >> `s.vs_fmp = t.vs_fmp` by metis_tac[inline_frame_fmp] >>
  simp[adopt_return_fmp_def, venom_state_component_equality] >>
  gvs[inline_frame_rel_def, inline_shared_frame_def, execution_frame_def,
    lookup_var_def, venom_state_component_equality]
QED

(* Caller outputs may belong to P.  In that case update the saved caller
   too, rather than incorrectly claiming that its old values survive. *)
Theorem inline_frame_write_caller:
  inline_frame_rel ren V caller.vs_vars P s t /\
  (!v. v IN V ==> ren v <> x) ==>
  inline_frame_rel ren V (update_var x w caller).vs_vars P s (update_var x w t)
Proof
  simp[inline_frame_rel_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem inline_frame_writes_caller:
  !pairs ren V caller P s t.
    inline_frame_rel ren V caller.vs_vars P s t /\
    EVERY (\p. !v. v IN V ==> ren v <> FST p) pairs ==>
    inline_frame_rel ren V
      (FOLDL (\c (x,w). update_var x w c) caller pairs).vs_vars P s
      (FOLDL (\t (x,w). update_var x w t) t pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  irule inline_frame_write_caller >> metis_tac[]
QED

Theorem inline_frame_bind_return_outputs:
  inline_frame_rel ren V caller.vs_vars P s t /\
  (!x v. MEM x outs /\ v IN V ==> ren v <> x) /\
  bind_outputs outs vals caller = SOME caller' /\
  bind_outputs outs vals t = SOME t' ==>
  inline_frame_rel ren V caller'.vs_vars P s t'
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  gvs[] >> irule inline_frame_writes_caller >> simp[] >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  imp_res_tac listTheory.MEM_ZIP >> gvs[] >> metis_tac[listTheory.EL_MEM]
QED

(* Actual cloning is the abstract frame renaming, with external labels fixed. *)
Theorem clone_operand_inline_rename:
  !p labels op.
    clone_operand p labels op =
      inline_rename_operand (STRCAT p)
        (\l. if MEM l labels then STRCAT p l else l) op
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[clone_operand_def, inline_rename_operand_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem clone_instruction_inline_rename:
  clone_instruction p labels inst =
    inline_rename_inst (STRCAT p)
      (\l. if MEM l labels then STRCAT p l else l) inst
Proof
  `clone_operand p labels = inline_rename_operand (STRCAT p)
     (\l. if MEM l labels then STRCAT p l else l)` by
    simp[FUN_EQ_THM, clone_operand_inline_rename] >>
  simp[clone_instruction_def, inline_rename_inst_def, SF ETA_ss]
QED

(* At call entry no callee variables have been established.  The target may
   retain arbitrary bindings in the fresh namespace; none is read yet. *)
Theorem inline_frame_setup_empty:
  setup_callee fn args caller = SOME cs /\ ~caller.vs_halted ==>
  inline_frame_rel ren {} caller.vs_vars P cs caller
Proof
  simp[inline_frame_rel_def] >> metis_tac[inline_shared_frame_setup]
QED

Theorem inline_frame_write_establish:
  inline_frame_rel ren V saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P ==>
  inline_frame_rel ren (x INSERT V) saved P
    (update_var x w s) (update_var (ren x) w t)
Proof
  simp[inline_frame_rel_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE] >> metis_tac[]
QED

(* opaque is static token ancestry, not a scan of transformed RETPC_PARAMs.
   Only definedness flows forward for opaque variables. *)
Definition inline_opaque_frame_rel_def:
  inline_opaque_frame_rel ren V opaque saved P s t <=>
    inline_frame_rel ren (V DIFF opaque) saved P s t /\
    (!v. v IN V INTER opaque /\ IS_SOME (lookup_var v s) ==>
      IS_SOME (lookup_var (ren v) t))
End

Theorem inline_opaque_frame_exact:
  inline_opaque_frame_rel ren V {} saved P s t <=>
  inline_frame_rel ren V saved P s t
Proof
  simp[inline_opaque_frame_rel_def]
QED

Theorem inline_opaque_frame_setup_empty:
  setup_callee fn args caller = SOME cs /\ ~caller.vs_halted ==>
  inline_opaque_frame_rel ren {} opaque caller.vs_vars P cs caller
Proof
  simp[inline_opaque_frame_rel_def] >> metis_tac[inline_frame_setup_empty]
QED

Theorem inline_opaque_frame_write_establish:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P /\
  (x NOTIN opaque ==> a = b) ==>
  inline_opaque_frame_rel ren (x INSERT V) opaque saved P
    (update_var x a s) (update_var (ren x) b t)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem inline_opaque_frame_eval_operands:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l))) ops ==>
  eval_operands (MAP (inline_rename_operand ren lab) ops) t = eval_operands ops s
Proof
  simp[inline_opaque_frame_rel_def] >> rpt strip_tac >>
  irule inline_frame_eval_operands >>
  qexistsl [`P`, `V DIFF opaque`, `saved`] >> simp[]
QED

Theorem inline_opaque_frame_read_defined:
  inline_opaque_frame_rel ren V opaque saved P s t /\ v IN V /\
  lookup_var v s = SOME a ==>
  ?b. lookup_var (ren v) t = SOME b /\ (v NOTIN opaque ==> b = a)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  rpt strip_tac >> Cases_on `v IN opaque` >> gvs[] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

(* ASSIGN and each PHI selection read their source snapshot before writing. *)
Theorem inline_opaque_frame_copy:
  inline_opaque_frame_rel ren V opaque saved P s t /\ v IN V /\ x IN opaque /\
  (!u. u IN V ==> (ren u = ren x <=> u = x)) /\ ren x NOTIN P /\
  lookup_var v s = SOME a ==>
  ?b. eval_operand (Var (ren v)) t = SOME b /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P
      (update_var x a s) (update_var (ren x) b t)
Proof
  rpt strip_tac >> drule_all inline_opaque_frame_read_defined >> strip_tac >>
  qexists `b` >> simp[eval_operand_def] >>
  irule inline_opaque_frame_write_establish >> metis_tac[]
QED

Theorem inline_opaque_frame_token_seed:
  inline_opaque_frame_rel ren V opaque saved P s t /\ x IN opaque /\
  (!v. v IN V ==> (ren v = ren x <=> v = x)) /\ ren x NOTIN P ==>
  inline_opaque_frame_rel ren (x INSERT V) opaque saved P
    (update_var x s.vs_return_pc_token s) (update_var (ren x) 0w t)
Proof
  rpt strip_tac >> irule inline_opaque_frame_write_establish >> metis_tac[]
QED

(* Each selected opaque PHI input is read from the pre-PHI snapshot.
   This deliberately permits a nonopaque input to an opaque PHI output. *)
Theorem inline_opaque_frame_selected_phi:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  inst.inst_outputs = [x] /\ resolve_phi prev inst.inst_operands = SOME (Var v) /\
  v IN V /\ eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b)
Proof
  rpt strip_tac >>
  `lookup_var v s = SOME a` by gvs[eval_one_phi_def, eval_operand_def, AllCaseEqs()] >>
  drule_all inline_opaque_frame_read_defined >> strip_tac >> qexists `b` >>
  `resolve_phi (lab prev) (MAP (inline_rename_operand ren lab) inst.inst_operands) =
    SOME (Var (ren v))` by
    (simp[inline_rename_resolve_phi, inline_rename_operand_def]) >>
  simp[eval_one_phi_def, inline_rename_inst_def, eval_operand_def]
QED

(* Full return operands must be defined, including the discarded token.
   Only FRONT and the shared fmp are observable at the call boundary. *)
Theorem inline_opaque_frame_return_suffix:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l))) ops /\
  v IN V /\ lookup_var v s = SOME a /\ eval_operands ops s = SOME ws ==>
  ?b. eval_operands (ops ++ [Var v]) s = SOME (ws ++ [a]) /\
    eval_operands (MAP (inline_rename_operand ren lab) (ops ++ [Var v])) t =
      SOME (ws ++ [b]) /\
    FRONT (ws ++ [a]) = FRONT (ws ++ [b]) /\ s.vs_fmp = t.vs_fmp
Proof
  rpt strip_tac >>
  `eval_operands (MAP (inline_rename_operand ren lab) ops) t = SOME ws` by
    (drule_all inline_opaque_frame_eval_operands >> simp[]) >>
  drule_all inline_opaque_frame_read_defined >> strip_tac >> qexists `b` >>
  `s.vs_fmp = t.vs_fmp` by
    metis_tac[inline_opaque_frame_rel_def, inline_frame_fmp] >>
  simp[eval_operands_append, eval_operands_def, eval_operand_def,
    inline_rename_operand_def, rich_listTheory.FRONT_APPEND]
QED

Theorem inline_opaque_frame_phi_write:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  inst.inst_outputs = [x] /\ resolve_phi prev inst.inst_operands = SOME (Var v) /\
  v IN V /\ x IN opaque /\
  (!u. u IN V ==> (ren u = ren x <=> u = x)) /\ ren x NOTIN P /\
  eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b) /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P
      (update_var x a s) (update_var (ren x) b t)
Proof
  rpt strip_tac >> drule_all inline_opaque_frame_selected_phi >> strip_tac >>
  qexists `b` >> simp[] >>
  irule inline_opaque_frame_write_establish >> metis_tac[]
QED

(* Static ancestry discharges only opacity; coverage and label agreement
   remain explicit dynamic-frame premises. *)
Theorem inline_opacity_frame_ordinary_operands:
  inline_opacity_ok fn opaque /\ MEM inst (fn_insts fn) /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  EVERY (\op. (!v. op = Var v ==> v IN V) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)))
    inst.inst_operands ==>
  eval_operands (MAP (inline_rename_operand ren lab) inst.inst_operands) t =
    eval_operands inst.inst_operands s
Proof
  rpt strip_tac >> irule inline_opaque_frame_eval_operands >>
  goal_assum (drule_at Any) >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >> gvs[] >>
  drule_all inline_opacity_use >> simp[unitShapeDefsTheory.retpc_use_ok_def]
QED

Theorem inline_opacity_frame_return:
  inline_opacity_ok fn opaque /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [RET; RETFMP] /\ inst.inst_operands = ops ++ [Var v] /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  EVERY (\op. (!x. op = Var x ==> x IN V) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l))) ops /\
  v IN V /\ lookup_var v s = SOME a /\ eval_operands ops s = SOME ws ==>
  ?b. eval_operands inst.inst_operands s = SOME (ws ++ [a]) /\
    eval_operands (MAP (inline_rename_operand ren lab) inst.inst_operands) t =
      SOME (ws ++ [b]) /\
    FRONT (ws ++ [a]) = FRONT (ws ++ [b]) /\ s.vs_fmp = t.vs_fmp
Proof
  rpt strip_tac >>
  qpat_assum `inst.inst_operands = _` (fn th => rewrite_tac[th]) >>
  irule inline_opaque_frame_return_suffix >> simp[] >>
  goal_assum (drule_at (Pat `inline_opaque_frame_rel _ _ _ _ _ _ _`)) >>
  simp[] >> gvs[listTheory.EVERY_MEM] >> rpt strip_tac >> gvs[] >>
  `MEM (Var v') (TAKE (LENGTH inst.inst_operands - 1) inst.inst_operands)` by
    simp[rich_listTheory.TAKE_APPEND] >>
  drule_at (Pat `MEM i (fn_insts fn)`) inline_opacity_return_front >>
  simp[rich_listTheory.TAKE_APPEND] >> metis_tac[]
QED

Theorem inline_opacity_frame_phi_write:
  inline_opacity_ok fn opaque /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  inline_opaque_frame_rel ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  inst.inst_outputs = [x] /\ resolve_phi prev inst.inst_operands = SOME (Var v) /\
  v IN V /\ v IN opaque /\
  (!u. u IN V ==> (ren u = ren x <=> u = x)) /\ ren x NOTIN P /\
  eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b) /\
    inline_opaque_frame_rel ren (x INSERT V) opaque saved P
      (update_var x a s) (update_var (ren x) b t)
Proof
  rpt strip_tac >> irule inline_opaque_frame_phi_write >>
  goal_assum (drule_at Any) >> simp[] >>
  irule inline_opacity_phi >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl [`fn`, `inst`] >>
  simp[] >> metis_tac[dftCommutationTheory.resolve_phi_MEM]
QED

Theorem inline_opaque_frame_eval_one_phi:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ (v IN opaque ==> x IN opaque)) /\
    (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)))
    inst.inst_operands /\
  eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b) /\
    (x NOTIN opaque ==> b = a)
Proof
  rpt strip_tac >>
  `resolve_phi (lab prev) (MAP (inline_rename_operand ren lab) inst.inst_operands) =
    OPTION_MAP (inline_rename_operand ren lab) (resolve_phi prev inst.inst_operands)`
    by (irule inline_rename_resolve_phi >> simp[]) >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  `MEM val_op inst.inst_operands` by metis_tac[dftCommutationTheory.resolve_phi_MEM] >>
  gvs[listTheory.EVERY_MEM] >>
  Cases_on `val_op` >> gvs[eval_operand_def, inline_rename_operand_def]
  >- (qexists `a` >> simp[inline_rename_inst_def, eval_operand_def])
  >- (`s' IN V` by metis_tac[] >>
      drule_all inline_opaque_frame_read_defined >> strip_tac >>
      qexists `b` >> simp[inline_rename_inst_def, eval_operand_def] >>
      metis_tac[]) >>
  qexists `a` >> simp[inline_rename_inst_def, eval_operand_def] >> metis_tac[]
QED

Definition inline_phi_outputs_def:
  inline_phi_outputs [] = {} /\
  inline_phi_outputs (inst::rest) =
    if inst.inst_opcode = PHI then set inst.inst_outputs UNION inline_phi_outputs rest
    else {}
End

Theorem inline_opaque_frame_phis_snapshot:
  !insts ren lab V opaque saved P s t u.
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!inst x a. MEM inst insts /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) ==>
    ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b) /\
      (x NOTIN opaque ==> b = a)) /\
  (!x. x IN inline_phi_outputs insts ==> ren x NOTIN P) /\
  (!x v. x IN inline_phi_outputs insts /\
    v IN V UNION inline_phi_outputs insts ==> (ren v = ren x <=> v = x)) /\
  eval_phis s insts = OK u ==>
  ?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
    inline_opaque_frame_rel ren (V UNION inline_phi_outputs insts) opaque saved P u t'
Proof
  Induct >> simp[eval_phis_def, inline_phi_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, inline_phi_outputs_def, AllCaseEqs()] >>
      rename1 `eval_phis s insts = OK tail_state` >>
      `?b. eval_one_phi t (inline_rename_inst ren lab h) = SOME (ren out,b) /\
        (out NOTIN opaque ==> b = v)` by metis_tac[] >>
      `?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
        inline_opaque_frame_rel ren (V UNION inline_phi_outputs insts) opaque saved P tail_state t'`
        by (first_x_assum irule >> metis_tac[]) >>
      `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
      qexists `update_var (ren out) b t'` >>
      simp[inline_rename_inst_def] >>
      `V UNION ({out} UNION inline_phi_outputs insts) =
        out INSERT (V UNION inline_phi_outputs insts)` by SET_TAC[] >>
      qpat_x_assum `V UNION _ = out INSERT _`
        (fn th => pure_once_rewrite_tac[th]) >>
      irule inline_opaque_frame_write_establish >>
      simp[pred_setTheory.FORALL_IN_UNION]) >>
  gvs[eval_phis_def, inline_phi_outputs_def, inline_rename_inst_def]
QED

Theorem inline_opaque_frame_eval_phis:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  EVERY (\inst. !x. MEM x inst.inst_outputs ==>
    EVERY (\op. (!v. op = Var v ==> v IN V /\ (v IN opaque ==> x IN opaque)) /\
      (!l. op = Label l ==> FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)))
      inst.inst_operands) insts /\
  (!x. x IN inline_phi_outputs insts ==> ren x NOTIN P) /\
  (!x v. x IN inline_phi_outputs insts /\
    v IN V UNION inline_phi_outputs insts ==> (ren v = ren x <=> v = x)) /\
  eval_phis s insts = OK u ==>
  ?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
    inline_opaque_frame_rel ren (V UNION inline_phi_outputs insts) opaque saved P u t'
Proof
  strip_tac >> irule inline_opaque_frame_phis_snapshot >>
  goal_assum (drule_at Any) >> simp[] >> qexists `s` >> simp[] >>
  rpt strip_tac >> irule inline_opaque_frame_eval_one_phi >>
  goal_assum (drule_at Any) >> simp[] >>
  `inst.inst_outputs = [x]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  goal_assum (drule_at (Pat `inline_opaque_frame_rel _ _ _ _ _ _ _`)) >>
  gvs[listTheory.EVERY_MEM] >>
  qpat_x_assum `!i. MEM i insts ==> _` (qspec_then `inst` mp_tac) >> simp[]
QED

Theorem inline_rename_extract_labels:
  !ops ren lab.
  extract_labels (MAP (inline_rename_operand ren lab) ops) =
    OPTION_MAP (MAP lab) (extract_labels ops)
Proof
  Induct >> simp[extract_labels_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[inline_rename_operand_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> simp[]
QED

Theorem inline_opaque_phis_control:
  !insts s u.
  eval_phis s insts = OK u ==>
  u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb /\
  u.vs_inst_idx = s.vs_inst_idx /\ u.vs_halted = s.vs_halted
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem inline_opaque_frame_write_caller:
  inline_opaque_frame_rel ren V opaque caller.vs_vars P s t /\
  (!v. v IN V ==> ren v <> x) ==>
  inline_opaque_frame_rel ren V opaque (update_var x w caller).vs_vars P
    s (update_var x w t)
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem inline_opaque_frame_writes_caller:
  !pairs ren V opaque caller P s t.
    inline_opaque_frame_rel ren V opaque caller.vs_vars P s t /\
    EVERY (\p. !v. v IN V ==> ren v <> FST p) pairs ==>
    inline_opaque_frame_rel ren V opaque
      (FOLDL (\c (x,w). update_var x w c) caller pairs).vs_vars P s
      (FOLDL (\t (x,w). update_var x w t) t pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  irule inline_opaque_frame_write_caller >> metis_tac[]
QED

Theorem inline_opaque_frame_bind_return_outputs:
  inline_opaque_frame_rel ren V opaque caller.vs_vars P s t /\
  (!x v. MEM x outs /\ v IN V ==> ren v <> x) /\
  bind_outputs outs vals caller = SOME caller' /\
  bind_outputs outs vals t = SOME t' ==>
  inline_opaque_frame_rel ren V opaque caller'.vs_vars P s t'
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  gvs[] >> irule inline_opaque_frame_writes_caller >> simp[] >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  imp_res_tac listTheory.MEM_ZIP >> gvs[] >> metis_tac[listTheory.EL_MEM]
QED

(* Coverage is deliberately one-sided: support may also contain undefined names.
   Parallel PHIs read their original snapshot, not preceding PHI writes. *)
Definition inline_defined_support_def:
  inline_defined_support V s <=>
    !v a. lookup_var v s = SOME a ==> v IN V
End

Definition inline_supported_frame_def:
  inline_supported_frame ren V opaque saved P s t <=>
    inline_opaque_frame_rel ren V opaque saved P s t /\
    inline_defined_support V s
End

Theorem inline_defined_support_empty:
  inline_defined_support {} (s with vs_vars := FEMPTY)
Proof
  simp[inline_defined_support_def, lookup_var_def]
QED

Theorem inline_defined_support_write:
  inline_defined_support V s ==>
  inline_defined_support (x INSERT V) (update_var x w s)
Proof
  simp[inline_defined_support_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem inline_defined_support_phis:
  !insts s u V.
    eval_phis s insts = OK u /\ inline_defined_support V s ==>
    inline_defined_support (V UNION inline_phi_outputs insts) u
Proof
  Induct >> simp[eval_phis_def, inline_phi_outputs_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, inline_phi_outputs_def, AllCaseEqs()] >>
      rpt strip_tac >>
      `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
      `inline_defined_support (V UNION inline_phi_outputs insts) s''` by
        (first_x_assum irule >> metis_tac[]) >>
      gvs[inline_defined_support_def, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[eval_phis_def, inline_phi_outputs_def] >> metis_tac[]
QED

Theorem inline_supported_frame_eval_one_phi:
  inline_supported_frame ren V opaque saved P s t /\
  s.vs_prev_bb = SOME prev /\ t.vs_prev_bb = SOME (lab prev) /\
  (!l. lab l = lab prev <=> l = prev) /\
  (!l. resolve_phi prev inst.inst_operands = SOME (Label l) ==>
    FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)) /\
  (!v. resolve_phi prev inst.inst_operands = SOME (Var v) /\ v IN opaque ==>
    x IN opaque) /\
  eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t (inline_rename_inst ren lab inst) = SOME (ren x,b) /\
    (x NOTIN opaque ==> b = a)
Proof
  rpt strip_tac >>
  `resolve_phi (lab prev) (MAP (inline_rename_operand ren lab) inst.inst_operands) =
    OPTION_MAP (inline_rename_operand ren lab) (resolve_phi prev inst.inst_operands)`
    by (irule inline_rename_resolve_phi >> simp[]) >>
  gvs[inline_supported_frame_def, eval_one_phi_def, AllCaseEqs()] >>
  Cases_on `val_op` >> gvs[eval_operand_def, inline_rename_operand_def]
  >- (qexists `a` >> simp[inline_rename_inst_def, eval_operand_def])
  >- (`s' IN V` by metis_tac[inline_defined_support_def] >>
      drule_all inline_opaque_frame_read_defined >> strip_tac >>
      qexists `b` >> simp[inline_rename_inst_def, eval_operand_def] >> metis_tac[]) >>
  qexists `a` >> simp[inline_rename_inst_def, eval_operand_def] >> metis_tac[]
QED

Theorem inline_eval_phis_none_success:
  s.vs_prev_bb = NONE /\ eval_phis s insts = OK u ==>
  u = s /\ inline_phi_outputs insts = {} /\
  !ren lab t. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t
Proof
  Cases_on `insts` >> simp[eval_phis_def, inline_phi_outputs_def] >>
  Cases_on `h.inst_opcode = PHI` >> rpt strip_tac >>
  gvs[eval_phis_def, eval_one_phi_def, inline_phi_outputs_def,
    inline_rename_inst_def, AllCaseEqs()]
QED

Theorem inline_supported_frame_eval_phis:
  inline_supported_frame ren V opaque saved P s t /\
  t.vs_prev_bb = OPTION_MAP lab s.vs_prev_bb /\
  (!prev l. s.vs_prev_bb = SOME prev ==> (lab l = lab prev <=> l = prev)) /\
  (!inst prev l. MEM inst insts /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Label l) ==>
    FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (lab l)) /\
  (!inst prev v x a. MEM inst insts /\ s.vs_prev_bb = SOME prev /\
    eval_one_phi s inst = SOME (x,a) /\
    resolve_phi prev inst.inst_operands = SOME (Var v) /\ v IN opaque ==>
    x IN opaque) /\
  (!x. x IN inline_phi_outputs insts ==> ren x NOTIN P) /\
  (!x v. x IN inline_phi_outputs insts /\
    v IN V UNION inline_phi_outputs insts ==> (ren v = ren x <=> v = x)) /\
  eval_phis s insts = OK u ==>
  ?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
    inline_supported_frame ren (V UNION inline_phi_outputs insts) opaque saved P u t'
Proof
  strip_tac >> Cases_on `s.vs_prev_bb`
  >- (drule_all inline_eval_phis_none_success >> strip_tac >>
      qexists `t` >> gvs[]) >>
  `?t'. eval_phis t (MAP (inline_rename_inst ren lab) insts) = OK t' /\
    inline_opaque_frame_rel ren (V UNION inline_phi_outputs insts) opaque saved P u t'`
    by (irule inline_opaque_frame_phis_snapshot >>
        goal_assum (drule_at Any) >>
        gvs[inline_supported_frame_def] >> qexists `s` >> simp[] >>
        rpt strip_tac >> irule inline_supported_frame_eval_one_phi >>
        goal_assum (drule_at Any) >> simp[inline_supported_frame_def] >> metis_tac[]) >>
  qexists `t'` >> simp[inline_supported_frame_def] >>
  irule inline_defined_support_phis >>
  gvs[inline_supported_frame_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inline_supported_frame_setup:
  setup_callee fn args caller = SOME cs /\ ~caller.vs_halted ==>
  inline_supported_frame ren {} opaque caller.vs_vars P cs caller /\
  cs.vs_prev_bb = NONE
Proof
  strip_tac >>
  `inline_opaque_frame_rel ren {} opaque caller.vs_vars P cs caller` by
    (irule inline_opaque_frame_setup_empty >> metis_tac[]) >>
  simp[inline_supported_frame_def] >>
  gvs[setup_callee_def, inline_defined_support_def, lookup_var_def,
    AllCaseEqs()]
QED
