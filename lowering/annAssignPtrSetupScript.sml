(* Counted declaration setup and the explicit not-yet-live pointer frame. *)
Theory annAssignPtrSetup
Ancestors
  annAssignPtrFacts bodyPtrDefs allocationPtr fragGasSeqPtr
  exprSimProps loweringPosts finite_map fragExecPtr venomInst venomExecSemantics
  fragGasPathPtr venomInstProofs venomState stmtSimProps compileEnv
  annAssignPtrAllocGhost fragExec emitHelper emitHelperProps
  stmtSimDeclPath loweringSlice exprLoweringProps

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

Theorem annassign_emit_instruction_ptr:
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

Theorem annassign_ghost_inst_idx_ptr:
 !d cenv cx es G tn s i.
 ghost_inv d cenv cx es G tn (s with vs_inst_idx := i) <=>
 ghost_inv d cenv cx es G tn s
Proof
 rpt gen_tac >> Cases_on `d`
 >- simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
         lookup_var_def, stor_taint_ok_def] >>
 PairCases_on `x` >>
 simp[ghost_inv_def, return_buf_ptr_def, ptr_covers_def,
      lookup_var_def, stor_taint_ok_def]
QED

Theorem annassign_setup_ptr:
 !ctx func cenv cx es st st1 p sz s0 sa d PG G0 tn0.
 emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),st1) /\
 stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
 MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
 not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
 ~not_fresh_at sa p /\
 (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> x <> p) /\
 (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> x <> p) /\
 fn_has_code st st1 func /\ ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
 s0.vs_current_bb = st.cs_current_bb /\
 s0.vs_inst_idx = LENGTH st.cs_current_insts /\
 ghost_inv d cenv cx es G0 tn0 s0 ==>
 ?s1 w G1 tn1.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G1 tn1 (OK s1) /\
 stmt_state_rel ctx func cenv cx es s1 /\
 ghost_inv d cenv cx es G1 tn1 s1 /\
 ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
 ptr_covers G1 tn1 p s1 sz /\
 lookup_var p s1 = SOME w /\
 FLOOKUP s1.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
 w2n w + sz < dimword (:256) /\
 (!op. op <> Var p ==> eval_operand op s1 = eval_operand op s0) /\
 s1.vs_memory = s0.vs_memory /\
 (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
 (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                FLOOKUP s1.vs_allocas aid = SOME entry) /\
 ~s1.vs_halted /\ s1.vs_current_bb = st1.cs_current_bb /\
 s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
 ?u. step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 = OK u /\
     s1 = u with vs_inst_idx := SUC s0.vs_inst_idx /\
     G1 = step_prov PG G0 (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) u /\
     tn1 = step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 u tn0
Proof
 rpt gen_tac >> strip_tac >>
 `?u. exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p])
        s0 (n2w sz : bytes32) = OK u` by
   (Cases_on `FLOOKUP s0.vs_allocas st.cs_next_id`
    >- simp[exec_alloca_def, mk_inst_def] >>
    rename1 `FLOOKUP s0.vs_allocas st.cs_next_id = SOME entry` >>
    PairCases_on `entry` >> simp[exec_alloca_def, mk_inst_def]) >>
 `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s0 = OK u` by
   simp[step_inst_base_def, instruction_accessors, eval_operand_def] >>
 drule_all annassign_emit_instruction_ptr >> strip_tac >>
 `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s0.vs_inst_idx =
    SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p])` by simp[] >>
 drule_all annassign_alloca_path_ptr >>
 disch_then (qspecl_then [`cx_dead cx`, `PG`, `G0`, `tn0`] strip_assume_tac) >>
 drule_all annassign_alloca_ghost_frame_ptr >>
 disch_then (qspec_then `PG` strip_assume_tac) >>
 `stmt_state_rel ctx func cenv cx es u` by
   (irule (cj 1 stmt_state_rel_exec_alloca) >>
    conj_tac >- simp[] >>
    qexistsl [`mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]`,
              `n2w sz`, `p`, `s0`] >> simp[instruction_accessors]) >>
 drule exec_alloca_operand_frame >> simp[instruction_accessors] >> disch_tac >>
 drule exec_alloca_memory >> disch_tac >>
 drule_at (Pat `exec_alloca _ _ _ = _`) exec_alloca_frames >> simp[instruction_accessors] >> strip_tac >>
 `~u.vs_halted /\ u.vs_current_bb = s0.vs_current_bb` by
   (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
    simp[exec_alloca_def, AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
 `st1.cs_current_bb = st.cs_current_bb /\
  LENGTH st1.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
   gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
 qexists `n2w b` >>
 simp[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def] >>
 simp[annassign_ghost_inst_idx_ptr] >>
 gvs[eval_operand_def, lookup_var_def]
QED
