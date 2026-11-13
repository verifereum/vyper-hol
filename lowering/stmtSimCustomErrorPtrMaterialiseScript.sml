Theory stmtSimCustomErrorPtrMaterialise
Ancestors
  bodyPtrDefs bodyPtrAttributeAdd exprSimVVFrame exprOperandVar
  exprLowering loweringPosts context compileEnv ptrSafeRun
  valueCopyBytes ptrDiscipline emitHelper freshWrites venomState
  venomExecSemantics finite_map loweringStateRelDefs fragGasPathPtr

(* No representation-size assumption is needed here, including for empty values.
   Located values may use a different bytestring representation type. *)
Theorem custom_error_unwrap_no_load_ptr:
  ~s.vs_halted /\ ptr_vv_ok cx t tv vv es G tn s /\
  read_result cx tv es = (INL v,es) /\
  (case vv of StackValue ty op => T
   | LocatedValue ty p => ~is_word_type t /\ ~is_word_type ty /\
                          p.ptr_location = LocMemory) ==>
  unwrap_value ce vv sm = (vv_operand vv,sm) /\
  ptr_val_ok cx t v (vv_operand vv) G tn s /\
  gas_path_ptr D lo ctx func PG G tn s 0 G tn (OK s)
Proof
  Cases_on `vv` >>
  simp[ptr_vv_ok_def, unwrap_value_def, vv_operand_def,
       comp_return_def, ptr_val_ok_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[cj 1 gas_path_ptr_rules]
QED

(* The compiler representation's non-wordness follows from vv_post, not a
   new assumption on a custom-error argument. *)
Theorem custom_error_vv_post_nonword:
  vv_post ctx func ce cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  ~is_word_type (post_value_type ce e) ==>
  ~is_word_type ty
Proof
  simp[vv_post_def, vv_holds_def] >>
  metis_tac[is_bytestring_word_type]
QED

(* ADD only updates a fresh destination. These are the exact observations
   required to transport an older vv, irrespective of its location. *)
Theorem custom_error_vv_ghost_frame[local]:
  (!w. eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s) /\
  op_taint tn' (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov G' (vv_operand vv) = op_prov G (vv_operand vv) /\
  u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_transient = s.vs_transient /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\
  ptr_vv_ok cx ty tv vv es G tn s ==>
  ptr_vv_ok cx ty tv vv es G' tn' u
Proof
  Cases_on `vv_operand vv` >> Cases_on `vv` >>
  gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def,
      op_prov_def] >> metis_tac[]
QED

Theorem custom_error_buf_ghost_frame[local]:
  eval_operand op u = eval_operand op s /\
  op_prov G' op = op_prov G op /\
  ptr_buf_ok ce e op G s ==>
  ptr_buf_ok ce e op G' u
Proof
  Cases_on `op` >> simp[ptr_buf_ok_def, op_prov_def] >>
  metis_tac[]
QED

Theorem custom_error_fresh_add_transport:
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  out = STRING #"%" (toString sm.cs_next_var) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  ptr_buf_ok ce e (vv_operand vv) G s /\
  (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans ==>
  vv_post ctx func ce cx e es sa sn s0 ee tv vv
    (update_var out w s with vs_inst_idx := n) /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn'
    (update_var out w s with vs_inst_idx := n) /\
  ptr_buf_ok ce e (vv_operand vv) G'
    (update_var out w s with vs_inst_idx := n)
Proof
  strip_tac >>
  `~not_fresh_at sm out /\ sm.cs_next_id <= sn.cs_next_id` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, comp_return_def, emit_def, not_fresh_at_def] >>
  `eval_operand (vv_operand vv) (update_var out w s with vs_inst_idx := n) =
   eval_operand (vv_operand vv) s /\
   op_taint tn' (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov G' (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, op_taint_def, op_prov_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[] >> irule vv_post_update_var >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule custom_error_vv_ghost_frame >>
      qexistsl_tac [`G`, `s`, `tn`] >> simp[update_var_def]) >>
  irule custom_error_buf_ghost_frame >> metis_tac[]
QED
