(* Request-prefix companion to bodyFullForStorage. *)
Theory s1PrefixForStorage
Ancestors
  s1PrefixPreds bodyFullForStorage s1PrefixDefs

val _ = Parse.hide "body";

Theorem for_storage_body_invoke_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx RetQ tops bindings env id typ
      tyv v ei body env_b ret_ty bc bc1 sb0 sb1 shadow_sb0 shadow_sb1 st0 s G
      tn idx p lvo k dst len.
  body_stmts_full_ok cx body /\
  body_stmts_prefix_ok cx body /\
  body_inv tops ctx bc cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env ei /\
  supported_stmts tops bindings body /\
  (!target.
       supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
       occurs_abi_decode_target target tops) /\
  expr_sim_inv bc cx (extend_local env id typ F)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
  ce_locals_declared bc (extend_local env id typ F) /\
  locals_alloc_ok bc (extend_local env id typ F) /\
  type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
  stmts_exprs_ok bc body /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc
      ret_ty /\
  stmts_env bc (InLoop exit incr) ret_ty body sb0 = (bc1,sb1) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
      shadow_sb0 = (gas_shadow_env T bc1,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\
  gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\
  fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\
  ret_pc_ok bc sb0 s /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
  ~block_is_terminated sb0 /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr))
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes) /\
  return_buf_frame d bc sb0 s /\
  return_buf_sep d bc
      (ei with scopes :=
        fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
          FEMPTY::ei.scopes) s /\
  alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes).storage_trace ==>
         stmt_state_rel H ctx func bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) s /\
         storage_well_formed_on cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) (FST H) /\
         ghost_inv_at (DF H) lo d bc cx
           (ei with
            scopes :=
              fmupdate id
                <|assignable := F; type := tyv; value := v; popped := []|>
                FEMPTY::ei.scopes) G tn s) /\
  ~s.vs_halted /\
  s.vs_current_bb = sb0.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb0.cs_current_insts /\
  not_fresh_at sb0 idx /\
  not_fresh_at sb0 p /\
  (!x. lvo = Var x ==> not_fresh_at sb0 x) /\
  (!lbl. lvo <> Label lbl) /\
  lookup_var idx s = SOME (n2w k) /\
  lookup_var p s = SOME dst /\
  eval_operand lvo s = SOME (n2w len) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmts cx body)
      (ei with
       scopes :=
         fmupdate id <|assignable := F; type := tyv; value := v; popped := []|>
           FEMPTY::ei.scopes,s,G,tn)
Proof
  rpt gen_tac >>
  qpat_abbrev_tac `envb = extend_local env id typ F` >>
  qpat_abbrev_tac `eb = ei with scopes := (FEMPTY |+ (id, _)) :: ei.scopes` >>
  rpt strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx envb eb` by
    simp[Abbr `envb`, Abbr `eb`] >>
  qpat_x_assum `body_stmts_prefix_ok _ _`
    (mp_tac o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
  disch_then drule_all >>
  disch_then (qspec_then `InLoop exit incr` mp_tac) >>
  rewrite_tac [stmt_frag_prefix_def] >>
  disch_then (qspecl_then [`st0`, `sb0`, `sb1`, `shadow_sb0`,
    `shadow_sb1`, `s`, `G`, `tn`, `bc1`] mp_tac) >>
  simp[stmt_frag_full_pre_def] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[]
QED
