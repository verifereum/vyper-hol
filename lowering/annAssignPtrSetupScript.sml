(* Counted declaration setup and the explicit not-yet-live pointer frame. *)
Theory annAssignPtrSetup
Ancestors
  annAssignPtrFacts bodyPtrDefs allocationPtr fragGasSeqPtr
  exprSimProps loweringPosts finite_map fragExecPtr venomInst venomExecSemantics
  fragGasPathPtr venomInstProofs venomState stmtSimProps compileEnv
  annAssignPtrAllocGhost fragExec emitHelper emitHelperProps

Theorem annassign_declared_pointer_after_rhs_ptr:
  !cenv es sa G0 tn0 s0 G tn s p sz.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    not_fresh_at sa p /\ lookup_var p s = lookup_var p s0 /\
    ptr_covers G0 tn0 p s0 sz ==>
    ptr_covers G tn p s sz
Proof
  rw[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem annassign_expr_pointer_frame_ptr:
  !ctx func cenv cx e es sa sb s0 es' v op s G0 tn0 G tn p sz aid b.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
    ptr_covers G0 tn0 p s0 sz /\
    FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
    ptr_covers G tn p s sz /\ FLOOKUP s.vs_allocas aid = SOME (b,sz)
Proof
  rw[expr_post_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem annassign_vv_pointer_frame_ptr:
  !ctx func cenv cx e es sa sb s0 es' tv vv s G0 tn0 G tn p sz aid b.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
    ptr_covers G0 tn0 p s0 sz /\
    FLOOKUP s0.vs_allocas aid = SOME (b,sz) ==>
    ptr_covers G tn p s sz /\ FLOOKUP s.vs_allocas aid = SOME (b,sz)
Proof
  rw[vv_post_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem annassign_alloca_edge_ptr:
  !D ctx fn PG G tn s bb id n p u.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit n] [p]) /\
    step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u)
      (step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
  simp[ptr_inst_ok_alloca] >> qexists `bb` >> simp[]
QED

Theorem annassign_alloca_path_ptr:
  !D ctx func PG G tn cenv cx es s bb id n p u.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [p]) /\
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [p]) s = OK u ==>
    gas_path_ptr D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [p]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [p]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [p]) s u tn)
      p (u with vs_inst_idx := SUC s.vs_inst_idx) n /\
    ?b. FLOOKUP u.vs_allocas id = SOME (b,n) /\
        b + n < dimword (:256) /\ eval_operand (Var p) u = SOME (n2w b)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst 0 ctx (mk_inst id ALLOCA [Lit (n2w n)] [p]) s = OK u` by
    simp[step_inst_non_invoke, instruction_accessors] >>
  `~u.vs_halted` by
    (drule step_preserves_halted >>
     simp[instruction_accessors, is_terminator_def]) >>
  conj_tac
  >- (drule_all annassign_alloca_edge_ptr >>
      disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] assume_tac) >>
      drule (cj 2 gas_path_ptr_rules) >> simp[] >>
      disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  conj_tac
  >- (simp[ptr_covers_def, lookup_var_def] >>
      drule_all alloca_step_ptr_covers >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
      simp[ptr_covers_def, lookup_var_def]) >>
  drule_all alloca_step_site >> simp[]
QED

Theorem annassign_ghost_declare_local_entry_ptr:
  !d cenv cx es G tn s id ty st c st1.
    declare_local cenv id ty st = (c,st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id es.scopes = NONE /\ ghost_inv d cenv cx es G tn s ==>
    ghost_inv d c cx es G tn s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf /\
   c.ce_return_pc = cenv.ce_return_pc` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                           ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  fs[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `name = id` >> gvs[] >>
      qpat_x_assum `!name entry p sz. _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[]) >>
  simp[] >> Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def]
QED

Theorem annassign_emit_instruction_ptr[local]:
  !opc args outs st st1 func.
    emit_inst opc args outs st = ((),st1) /\ fn_has_code st st1 func ==>
    ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH st.cs_current_insts) =
        SOME (mk_inst st.cs_next_id opc args outs)
Proof
  rpt gen_tac >> strip_tac >>
  `st1.cs_current_bb = st.cs_current_bb /\
   st1.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc args outs]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >> qexists `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED
