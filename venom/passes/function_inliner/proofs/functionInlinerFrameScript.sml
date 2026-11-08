(* Static frame interface for an active renamed callee and suspended caller. *)
Theory functionInlinerFrame
Ancestors
  functionInlinerReturnBoundary stateFrame venomExecProofs venomState finite_map pred_set

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
