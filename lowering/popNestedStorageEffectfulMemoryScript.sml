(* Authorized residual: counted twin of S1's
   exprSimPopNestedStorageEffectful.pop_nested_storage_effectful_dead_case.
   The target fragment premise is inlined with T-mode history preservation. *)
Theory popNestedStorageEffectfulMemory
Ancestors
  exprSimPopNestedStorageFrame exprSimMemDefs targetPlaceSimMem
  exprSimPopNestedBase exprSimHypsDefs gasOutcome gasContext loweringPosts
  exprLowering compileEnv vyperInterpreter vyperState venomState

Theorem pop_nested_storage_effectful_dead_case_mem:
  !ctx func cenv cx env ann bt ty es src id ts d.
    (!pty sa sb r s0.
      type_place_target env bt = SOME (Type pty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx,func) (eval_target_place cx bt) (es,s0)
        (\res ee t. ?p. res = INL p /\
          target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type pty) r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) /\
    ~EVERY (storage_frame_expr cx) (target_indices bt) ==>
    expr_vv_sim_mem ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
