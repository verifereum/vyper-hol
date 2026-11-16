(* Cursor and history transport for the common TopLevelName copy endpoint. *)
Theory bodyFullToplevelCodeNormalize
Ancestors
  bodyFullUnwrapRun exprPtrUnwrapAllocation exprSimCopy exprSimProps
  bodyFieldMemoryProps
  exprSimMemDefs bodyPtrDefs loweringPosts loweringStateRelDefs
  venomMemProps venomState venomInst compileEnv exprLoweringProps
  ptrDiscipline list arithmetic venomExecSemantics exprSimStorageCopy

Theorem toplevel_code_runtime_history:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  fn_has_code sm mid func /\ fn_has_code mid sc func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  mid.cs_current_bb = sm.cs_current_bb /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  alloca_inv a /\ a.vs_current_bb = mid.cs_current_bb /\
  copy_runtime_frame mid a sc z /\ z.vs_current_bb = sc.cs_current_bb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sc) /\
  s0.vs_alloca_next <= s.vs_alloca_next ==>
  alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  s.vs_alloca_next <= (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_alloca_next /\
  s0.vs_alloca_next <= (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_alloca_next /\
  (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_current_bb = sc.cs_current_bb
Proof
  strip_tac >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (irule step_inst_alloca_alloca_next_mono >>
     qexistsl [`ARB`, `0`, `mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_alloca_op_def]) >>
  `a.vs_alloca_next = u.vs_alloca_next /\ z.vs_alloca_next = a.vs_alloca_next` by
    (fs[copy_runtime_frame_def, copy_static_def, venom_state_component_equality]) >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `alloca_history func a` by
    (qpat_x_assum `a = _` SUBST_ALL_TAC >>
     irule emitted_alloca_history >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `fn_has_code sm mid func`)) >>
     qexistsl [`[mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]]`, `s`] >>
     gvs[run_inst_seq_def, mk_inst_def, is_terminator_def]) >>
  `alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (irule emitted_alloca_history >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `fn_has_code mid sc func`)) >>
     qexistsl [`emitted_insts mid sc`, `a`] >>
     fs[copy_runtime_frame_def, same_blocks_def]) >>
  simp[] >> decide_tac
QED

Theorem toplevel_code_runtime_normalize:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) ==>
  (expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op
     (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ghost_inv_at D lo ret cenv cx ee G tn
     (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   vv_at cenv cx pt sa sc ee tv (LocatedValue pt (mk_ptr op LocMemory))
     (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   expr_store_bound cx et v op (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ptr_val_ok cx pt v op G tn (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ptr_buf_ok cenv (TopLevelName ann nsid) op G
     (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   wb_frame cenv ee ee sb s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   (!rt w. evaluate_type (get_tenv cx) lt = SOME rt /\
      eval_operand op (z with vs_inst_idx := LENGTH sc.cs_current_insts) = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <=
        (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_alloca_next) /\
   (!x. not_fresh_at sb x ==>
      lookup_var x (z with vs_inst_idx := LENGTH sc.cs_current_insts) = lookup_var x s) /\
   (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_inst_idx = LENGTH sc.cs_current_insts
   <=>
   expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
   ghost_inv_at D lo ret cenv cx ee G tn z /\
   vv_at cenv cx pt sa sc ee tv (LocatedValue pt (mk_ptr op LocMemory)) z /\
   expr_store_bound cx et v op z /\ ptr_val_ok cx pt v op G tn z /\
   ptr_buf_ok cenv (TopLevelName ann nsid) op G z /\ wb_frame cenv ee ee sb s z /\
   (!rt w. evaluate_type (get_tenv cx) lt = SOME rt /\ eval_operand op z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
   (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s))
Proof
  strip_tac >> Cases_on `ret` >- simp[return_buf_ptr_def, ghost_inv_at_def,
    vv_at_def, expr_store_bound_def, wb_frame_def, lookup_var_def, local_region_def,
    ptr_covers_def, stor_taint_ok_at_def, allocas_from_def, ptr_val_ok_def,
    ptr_mem_ok_def, ptr_buf_ok_def] >>
  PairCases_on `x` >> simp[ghost_inv_at_def, vv_at_def, expr_store_bound_def, wb_frame_def,
       lookup_var_def, local_region_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_at_def, allocas_from_def, ptr_val_ok_def, ptr_mem_ok_def,
       ptr_buf_ok_def]
QED
