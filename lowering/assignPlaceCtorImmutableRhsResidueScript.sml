Theory assignPlaceCtorImmutableRhsResidue
Ancestors
  assignPlaceCallerFacts assignPlaceStoreReady assignPlaceGasCompose
  assignPlaceOperandFacts targetPureVvFrame targetPlaceSimCases
  stmtSimAugAssignPlaceMemory assignPlaceTargetLive exprSimHyps
  exprOperandVar exprSimAggregateSource exprSimSource
  stmtLoweringMono stmtSimDeclCompose targetPlaceSimDefs targetPlaceSim loweringPosts
  compileEnv stmtSimDefs vyperExprNoControl
Libs monadsyntax

(* Owner-authorized constructor immutable-buffer framing residue. *)
Theorem assign_place_ctor_immutable_rhs_residue:
  supported_target_pure tops bt /\
  type_place_target env bt = SOME (Type dty) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  assignable_type env.type_defs (expr_type e) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
  assign_alloc_ok cenv bt e /\ target_indices_pre cenv cx env bt /\
  expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ ~expr_has_effect e /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_get_target_ptr compile_expr cenv bt sm = (tr,st) /\
  unwrap_value cenv vv st = (src,su) /\
  (case FST (SND tr) of
     SOME loc => compile_assign_value cenv (FST tr) loc src
       (is_word_type (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e))
       (vv_location vv)
       (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e)
       (lowered_value_type cenv e)
       (case (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e) of
          ArrayT et (Dynamic _) =>
            SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
        | _ => NONE)
       (type_memory_bytes cenv (case SND (SND tr) of SOME (ValPT tt) => tt | _ => lowered_value_type cenv e))
   | NONE => emit_void INVALID []) su = ((),sb) /\
  ci_mono sa sm /\ ci_mono sm st /\ ci_mono st su /\ ci_mono su sb /\
  fn_has_code sa sm func /\ fn_has_code sm st func /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~block_is_terminated sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL pv) mid (OK t) /\
  vv_post ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) pv vv t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (read_result cx pv)
      (\v. bind (eval_target_place cx bt) (\p. write_place cx p v)))
    (mid with gas_obs := [],t)
    (\res ee u. !tail. stmt_post ctx func cx lctx cenv cenv sa sb es s0
      res (ee with gas_obs := tail) u)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  cheat
QED
