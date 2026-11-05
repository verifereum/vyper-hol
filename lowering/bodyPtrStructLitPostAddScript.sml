(* Operand-local frames; no claim about the entire live ghost invariant. *)
Theory bodyPtrStructLitPostAdd
Ancestors bodyPtrDefs typedCopyPtr decoderGhostFramePtr venomState
          ptrDiscipline context finite_map venomInst

Theorem ptr_mem_ok_operand_frame:
  ptr_mem_ok cx t v op G tn s /\
  eval_operand op s' = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
  s'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  ptr_mem_ok cx t v op G' tn' s'
Proof
  simp[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_val_ok_operand_frame:
  ptr_val_ok cx t v op G tn s /\
  eval_operand op s' = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\
  (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
  s'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  ptr_val_ok cx t v op G' tn' s'
Proof
  simp[ptr_val_ok_def] >> metis_tac[ptr_mem_ok_operand_frame]
QED

Theorem ptr_vv_ok_operand_frame:
  ptr_vv_ok cx t tv vv es G tn s /\
  eval_operand (vv_operand vv) s' = eval_operand (vv_operand vv) s /\
  op_taint tn' (vv_operand vv) = op_taint tn (vv_operand vv) /\
  (!x. vv_operand vv = Var x ==> FLOOKUP G' x = FLOOKUP G x) /\
  s'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient /\
  s'.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans ==>
  ptr_vv_ok cx t tv vv es G' tn' s'
Proof
  Cases_on `vv` >>
  simp[vv_operand_def, ptr_vv_ok_def] >>
  metis_tac[ptr_mem_ok_operand_frame, ptr_val_ok_operand_frame]
QED

Theorem fresh_add_operand_frame:
  (!x. op = Var x ==> x <> out) ==>
  eval_operand op (update_var out w s) = eval_operand op s /\
  op_taint (step_taint (mk_inst id ADD [left; right] [out]) s
    (update_var out w s) tn) op = op_taint tn op /\
  (!x. op = Var x ==>
    FLOOKUP (step_prov PG G (mk_inst id ADD [left; right] [out])
      (update_var out w s)) x = FLOOKUP G x)
Proof
  Cases_on `op` >>
  simp[copy_len_binop_ghost_frame, op_taint_def] >>
  simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[step_prov_other_output, mk_inst_def]
QED

Theorem ptr_mem_ok_fresh_add:
  ptr_mem_ok cx t v op G tn s /\
  (!x. op = Var x ==> x <> out) ==>
  ptr_mem_ok cx t v op
    (step_prov PG G (mk_inst id ADD [left; right] [out])
      (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s
      (update_var out w s) tn) (update_var out w s)
Proof
  strip_tac >> irule ptr_mem_ok_operand_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >>
  simp[copy_len_binop_ghost_frame] >>
  Cases_on `op` >>
  simp[copy_len_binop_ghost_frame, op_taint_def] >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      step_prov_other_output, mk_inst_def]
QED

Theorem ptr_val_ok_fresh_add:
  ptr_val_ok cx t v op G tn s /\
  (!x. op = Var x ==> x <> out) ==>
  ptr_val_ok cx t v op
    (step_prov PG G (mk_inst id ADD [left; right] [out])
      (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s
      (update_var out w s) tn) (update_var out w s)
Proof
  strip_tac >> irule ptr_val_ok_operand_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >>
  simp[copy_len_binop_ghost_frame] >>
  Cases_on `op` >>
  simp[copy_len_binop_ghost_frame, op_taint_def] >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      step_prov_other_output, mk_inst_def]
QED

Theorem ptr_vv_ok_fresh_add:
  ptr_vv_ok cx t tv vv es G tn s /\
  (!x. vv_operand vv = Var x ==> x <> out) ==>
  ptr_vv_ok cx t tv vv es
    (step_prov PG G (mk_inst id ADD [left; right] [out])
      (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s
      (update_var out w s) tn) (update_var out w s)
Proof
  strip_tac >> irule ptr_vv_ok_operand_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >>
  simp[copy_len_binop_ghost_frame] >>
  Cases_on `vv_operand vv` >>
  simp[copy_len_binop_ghost_frame, op_taint_def] >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      step_prov_other_output, mk_inst_def]
QED

(* Root coverage is independent of destination coverage and the older frame. *)
Theorem ptr_covers_fresh_add:
  ptr_covers G tn x s C /\ x <> out ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [left; right] [out])
      (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s
      (update_var out w s) tn) x (update_var out w s) C
Proof
  strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
