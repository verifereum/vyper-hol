(* The scalar prefix and operator preserve the constructor's reserved frame. *)
Theory augAssignFullStateFrame
Ancestors
  bodyFullGhostFrame bodyMemoryDefs bodyPtrDefs exprSimProps exprLoweringProps
  stmtSimProps stmtSimDefs loweringPosts loweringStateRelDefs ptrDiscipline
  compileEnv venomState finite_map

Theorem augassign_exterior_state_frame:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  t = (s with vs_inst_idx := pc) with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  stmt_state_rel H ctx func cenv cx es t /\
  ghost_inv_at D lo d cenv cx es G' tn' t /\
  return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
  local_ptrs_reserved cenv sb
Proof
  strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  conj_tac
  >- (qpat_assum `t = _` SUBST1_TAC >>
      irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_inst_idx] >>
      rpt strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      fs[lookup_var_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[]) >>
  conj_tac
  >- (qspecl_then [`D`, `lo`, `d`, `cenv`, `cx`, `es`, `es`, `G`, `G'`,
       `tn`, `tn'`, `s`, `t`, `sa`] mp_tac ghost_inv_at_exterior_frame >>
      simp[]) >>
  rpt conj_tac
  >- (qspecl_then [`d`, `cenv`, `cenv`, `sa`, `sb`, `s`, `t`]
        mp_tac return_buf_frame_frame >> simp[])
  >- (qspecl_then [`cenv`, `cenv`, `sa`, `sb`, `s`, `t`]
        mp_tac ret_pc_ok_frame >> simp[]) >>
  qspecl_then [`cenv`, `sa`, `sb`] mp_tac local_ptrs_reserved_next_var >> simp[]
QED

