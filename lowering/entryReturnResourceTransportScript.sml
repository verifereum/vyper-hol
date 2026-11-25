(* Semantic return-stage resources, independent of the host's code layout. *)
Theory entryReturnResourceTransport
Ancestors
  exprSimExtCallCase loweringPosts exprLoweringProps
  loweringStateRelDefs[qualified,ignore_grammar]
  list rich_list finite_map venomInst fcgDefs ptrDiscipline

Definition return_resource_agree_def:
  return_resource_agree ctx func ctx' func' <=>
    func.fn_name = func'.fn_name /\
    FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func) =
      FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func') /\
    unit_alloca_frame ctx = unit_alloca_frame ctx' /\
    fn_directly_calls ctx = fn_directly_calls ctx' /\
    (ctx_has_dalloca ctx <=> ctx_has_dalloca ctx') /\
    (EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts func) <=>
      EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts func')) /\
    (lookup_function func.fn_name ctx.ctx_functions = SOME func <=>
      lookup_function func'.fn_name ctx'.ctx_functions = SOME func')
End

Theorem return_alloca_site_filter[local]:
  (MEM i l /\ i.inst_opcode = ALLOCA /\ P) <=>
  MEM i (FILTER (\j. j.inst_opcode = ALLOCA) l) /\ P
Proof
  simp[MEM_FILTER, AC CONJ_ASSOC CONJ_COMM]
QED

Theorem return_pending_alloca_size_transport[local]:
  return_resource_agree ctx func ctx' func' ==>
  !s. pending_alloca_size func s = pending_alloca_size func' s
Proof
  rw[return_resource_agree_def] >>
  `!l. FILTER (\i. i.inst_opcode = ALLOCA /\
                    i.inst_id NOTIN FDOM s.vs_allocas) l =
       FILTER (\i. i.inst_id NOTIN FDOM s.vs_allocas)
         (FILTER (\i. i.inst_opcode = ALLOCA) l)` by
    simp[FILTER_FILTER, CONJ_COMM] >>
  pure_rewrite_tac[pending_alloca_size_def] >> simp[]
QED

Theorem return_stmt_state_rel_transport:
  return_resource_agree ctx func ctx' func' ==>
  !H cenv cx es s.
    stmt_state_rel H ctx func cenv cx es s <=>
    stmt_state_rel H ctx' func' cenv cx es s
Proof
  strip_tac >>
  drule_then assume_tac return_pending_alloca_size_transport >>
  fs[return_resource_agree_def] >>
  pure_rewrite_tac[stmt_state_rel_def, alloca_room_def, fmp_room_def,
       immutable_alloca_sep_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.local_ptrs_rel_def,
       loweringStateRelDefsTheory.local_backed_def] >>
  pure_rewrite_tac[return_alloca_site_filter] >>
  asm_rewrite_tac[]
QED

Theorem extcall_returned_transport:
  return_resource_agree ctx func ctx' func' ==>
  (extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op
     cap target has_default default_op default_ty default_opt returnData ee t <=>
   extcall_returned st0 ctx' func' cenv cx ret_type es sa s0 sr addr_op buf_op
     cap target has_default default_op default_ty default_opt returnData ee t)
Proof
  strip_tac >>
  drule_then (fn th => rewrite_tac[extcall_returned_def, th])
    return_stmt_state_rel_transport
QED

Theorem extcall_return_post_transport:
  return_resource_agree ctx func ctx' func' ==>
  (vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
   vv_post H ctx' func' cenv cx e es sa sb s0 es' tv vv s)
Proof
  strip_tac >>
  drule_then (fn th => pure_rewrite_tac[vv_post_def, pure_frame_def, th])
    return_stmt_state_rel_transport >>
  fs[return_resource_agree_def] >>
  pure_rewrite_tac[return_alloca_site_filter] >>
  asm_rewrite_tac[]
QED
