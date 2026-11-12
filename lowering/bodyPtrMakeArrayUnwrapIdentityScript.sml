(* No-code unwrap branches: the endpoint and both ghost components are unchanged. *)
Theory bodyPtrMakeArrayUnwrapIdentity
Ancestors
  bodyPtrDefs exprSimUnwrap exprLowering loweringPosts context
  fragGasPathPtr compileEnv valueCopyBytes

Theorem unwrap_stack_ptr_path:
  unwrap_value cenv (StackValue t op) sm = (result,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (StackValue t op) s /\
  read_result cx tv ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t op) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = op /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (expr_type e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def] >> metis_tac[]
QED

Theorem unwrap_memory_ptr_path:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  unwrap_value cenv (LocatedValue t p) sm = (result,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  read_result cx tv ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = p.ptr_operand /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (expr_type e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def, ptr_val_ok_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac
  >- (reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      qpat_x_assum `!tvt. _ ==> val_wf _ _ /\ _`
        (drule_then strip_assume_tac) >> metis_tac[]) >>
  strip_tac >> gvs[post_value_type_word] >>
  imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!tvt. _ ==> val_wf _ _ /\ _` (drule_then strip_assume_tac) >>
  metis_tac[]
QED
