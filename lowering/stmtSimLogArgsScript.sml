(* Frame interfaces for typed log arguments. *)
Theory stmtSimLogArgs
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimOps exprSimOperands compileEnv venomState stmtLowering
  exprSimWordArgs exprSimHyps exprSimAttributeFields logArgumentCompile exprLowering

(* A captured value in a live local survives a later expression whenever
   its footprint avoids the local's dynamic array length words, the only
   local bytes expressions may change (locals_kept). *)
Theorem log_local_footprint_kept:
  !cenv es s t n b sz off len.
    locals_kept cenv es s t /\
    local_region cenv es.scopes s n b sz /\
    b <= off /\ off + len <= b + sz /\
    (!k. dynarray_len_at cenv n k ==> off + len <= b + k \/ b + k + 32 <= off) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  rw[locals_kept_def] >> first_x_assum irule >>
  qexistsl [`b`, `n`, `sz`] >> simp[]
QED

Theorem log_local_value_kept:
  !cenv cx ty tv v op es s t n b sz w.
    expr_val_rel cx ty v op s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
    locals_kept cenv es s t /\
    local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
    (!k. dynarray_len_at cenv n k ==>
         w2n w + val_footprint tv v <= b + k \/ b + k + 32 <= w2n w) ==>
    expr_val_rel cx ty v op t
Proof
  rpt strip_tac >> irule expr_val_rel_footprint_agree >>
  simp[] >> qexists_tac `s` >> simp[] >>
  sym_tac >> irule log_local_footprint_kept >>
  qexistsl [`b`, `cenv`, `es`, `n`, `sz`] >> simp[]
QED

(* Wherever a value of type ty sits in a live local, it is apart from the
   local's dynamic array length words. *)
Definition log_arg_clear_def:
  log_arg_clear cenv cx ty v <=>
    !tv n j k.
      evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
      local_val_at cenv cx n j tv v /\ dynarray_len_at cenv n k ==>
      j + val_footprint tv v <= k \/ k + 32 <= j
End

(* A base type value holds no dynamic array, so it is clear of them. *)
Theorem log_arg_clear_base:
  expr_sim_inv cenv cx env es ==> log_arg_clear cenv cx (BaseT bt) v
Proof
  rw[log_arg_clear_def] >>
  drule vyperTypeValuesTheory.evaluate_type_BaseT_cases >> strip_tac >>
  gvs[] >>
  `dynarray_free (BaseTV btv)` by simp[dynarray_free_base] >>
  drule_all local_val_at_dynarray_apart >> simp[]
QED

Theorem log_argument_footprint_kept:
  !cenv cx ty tv v op sa sb es s t w.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    ~is_word_type ty /\ log_arg_clear cenv cx ty v /\
    eval_operand op s = SOME w /\
    wb_frame cenv es sb s t ==>
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >>
  disch_then strip_assume_tac
  >- (gvs[] >>
      `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `aid` >> simp[]) >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      strip_tac >> sym_tac >> first_x_assum irule >> simp[])
  >- (gvs[] >> irule log_local_footprint_kept >>
      qexistsl [`b`, `cenv`, `es`, `n`, `sz`] >>
      gvs[wb_frame_def] >> rpt strip_tac >>
      qpat_x_assum `log_arg_clear _ _ _ _`
        (mp_tac o REWRITE_RULE [log_arg_clear_def]) >>
      disch_then (qspecl_then [`tv`, `n`, `w2n w - b`, `k`] mp_tac) >>
      simp[]) >>
  gvs[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem log_argument_value_kept:
  !cenv cx ty es sa sb s t v op.
    expr_val_rel cx ty v op s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    wb_frame cenv es sb s t /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
    log_arg_clear cenv cx ty v ==>
    expr_val_rel cx ty v op t
Proof
  rpt gen_tac >> strip_tac >>
  `?w. eval_operand op s = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand op t = SOME w` by
    (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sb`, `s`] >> gvs[wb_frame_def]) >>
  Cases_on `is_word_type ty`
  >- gvs[expr_val_rel_def] >>
  Cases_on `evaluate_type (get_tenv cx) ty`
  >- simp[expr_val_rel_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  `val_wf tv v` by (gvs[expr_val_at_def] >> metis_tac[]) >>
  drule_all log_argument_footprint_kept >> strip_tac >>
  irule expr_val_rel_footprint_agree >> simp[] >>
  qexists_tac `s` >> simp[]
QED

Theorem compile_log_eval_all_nil:
  compile_log_eval_all cenv [] sa = ([], sa)
Proof
  simp[compile_log_eval_all_def, comp_return_def]
QED

(* With no later argument able to mutate memory, no argument is saved. *)
Theorem compile_log_eval_all_unsaved_cons:
  ~exprs_can_mutate cenv args ==>
  (compile_log_eval_all cenv (e::args) sa = (xs, sb) <=>
   ?x sm ys.
     lower_value compile_expr cenv (expr_type e) e sa = (x, sm) /\
     compile_log_eval_all cenv args sm = (ys, sb) /\
     xs = (x, lowered_value_type cenv e)::ys)
Proof
  strip_tac >>
  simp[logArgumentCompileTheory.compile_log_eval_all_cons,
       compile_log_save_arg_def, comp_return_def]
QED

(* lower_word_args itself is type-polymorphic; only its simulation theorem
   is word-specific. Reuse its compile-state shape interface. *)
Theorem compile_log_eval_all_operands:
  !args sa xs sb.
    ~exprs_can_mutate cenv args /\
    compile_log_eval_all cenv args sa = (xs, sb) ==>
    lower_word_args cenv expr_type args sa = (MAP FST xs, sb)
Proof
  Induct_on `args` >> simp[compile_log_eval_all_nil, lower_word_args_nil] >>
  rpt gen_tac >> simp[expr_can_mutate_def] >> strip_tac >>
  qpat_x_assum `compile_log_eval_all _ _ _ = _` mp_tac >>
  simp[compile_log_eval_all_unsaved_cons] >> strip_tac >> gvs[] >>
  simp[lower_word_args_cons] >>
  goal_assum (drule_at Any) >>
  first_x_assum drule_all >> simp[]
QED

Theorem compile_log_eval_all_shape:
  !args cenv.
    ~exprs_can_mutate cenv args /\
    (!e sa sb x. MEM e args /\
       lower_value compile_expr cenv (expr_type e) e sa = (x, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) ==>
    !sa sb xs. compile_log_eval_all cenv args sa = (xs, sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
      EVERY (\x. (!z. FST x = Var z ==> not_fresh_at sb z) /\
                 (!l. FST x <> Label l)) xs
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all compile_log_eval_all_operands >> strip_tac >>
  drule_all lower_word_args_shape >> simp[listTheory.EVERY_MAP]
QED

Theorem log_frame_operand:
  wb_frame cenv es sb s t /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  strip_tac >> irule eval_operand_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sb`, `s`] >> gvs[wb_frame_def]
QED

Theorem log_frame_local_region:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  wb_frame cenv es sb s t ==>
  (local_region cenv es'.scopes t n b sz <=>
   local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >>
      conj_tac
      >- (qexists_tac `func` >>
          gvs[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def]) >>
      qexistsl_tac [`sb`, `es'.scopes`, `t`] >> gvs[wb_frame_def]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `sb`, `es.scopes`] >> gvs[wb_frame_def]
QED

Theorem log_frame_placement:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es sb s t /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
  expr_val_at cenv cx ty sa sb es v op s ==>
  expr_val_at cenv cx ty sa sc es' v op t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es'.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> drule_all log_frame_local_region >> simp[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  simp[expr_val_at_def] >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `eval_operand op t = SOME w` by (drule_all log_frame_operand >> simp[]) >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
      gvs[wb_frame_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >>
      metis_tac[]) >>
  simp[]
QED

Definition log_arg_rel_def:
  log_arg_rel cenv cx sa sb es s (op,ty) v <=>
    expr_val_rel cx ty v op s /\ expr_val_at cenv cx ty sa sb es v op s /\
    log_arg_clear cenv cx ty v
End

Theorem log_arg_rel_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  log_arg_rel cenv cx sm sb es s arg v ==>
  log_arg_rel cenv cx sa sb es s arg v
Proof
  Cases_on `arg` >> simp[log_arg_rel_def] >>
  metis_tac[expr_val_at_start_mono]
QED

Theorem log_arg_rel_frame:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es sb s t /\
  (!z. FST arg = Var z ==> not_fresh_at sb z) /\
  (!l. FST arg <> Label l) /\
  log_arg_rel cenv cx sa sb es s arg v ==>
  log_arg_rel cenv cx sa sc es' t arg v
Proof
  Cases_on `arg` >> simp[log_arg_rel_def] >> strip_tac >>
  rpt conj_tac
  >- (drule_all log_argument_value_kept >> simp[])
  >- (drule_all log_frame_placement >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Definition log_args_post_def:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    LIST_REL (log_arg_rel cenv cx sa sb es' s) xs vs /\
    wb_frame cenv es sa s0 s
End

Theorem log_args_post_nil:
  stmt_state_rel ctx func cenv cx es s ==>
  log_args_post ctx func cenv cx es sa sa s es [] [] s
Proof
  simp[log_args_post_def, wb_frame_refl]
QED

Theorem log_args_post_state:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  stmt_state_rel ctx func cenv cx es' s
Proof
  simp[log_args_post_def]
QED

Theorem log_args_post_frame:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  wb_frame cenv es sa s0 s
Proof
  simp[log_args_post_def]
QED

Theorem log_args_post_values:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  LIST_REL (\arg v. expr_val_rel cx (SND arg) v (FST arg) s) xs vs
Proof
  simp[log_args_post_def] >> strip_tac >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  Cases >> simp[log_arg_rel_def]
QED

Theorem log_args_post_placements:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  LIST_REL (\arg v. expr_val_at cenv cx (SND arg) sa sb es' v (FST arg) s) xs vs
Proof
  simp[log_args_post_def] >> strip_tac >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  Cases >> simp[log_arg_rel_def]
QED

Theorem log_args_post_cons:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  expr_sim_inv cenv cx env0 es0 /\ expr_type e = BaseT bt /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v x t /\
  log_args_post ctx func cenv cx es1 sm sb t es' ys vs u ==>
  log_args_post ctx func cenv cx es sa sb s0 es'
    ((x,expr_type e)::ys) (v::vs) u
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t` by
    (drule_all expr_post_state >> simp[]) >>
  `wb_frame cenv es sa s0 t` by (drule_all expr_post_frame >> simp[]) >>
  `wb_frame cenv es1 sm t u` by (drule_all log_args_post_frame >> simp[]) >>
  `log_arg_rel cenv cx sa sm es1 t (x,expr_type e) v` by
    (gvs[expr_post_def, log_arg_rel_def] >>
     irule log_arg_clear_base >> metis_tac[]) >>
  `log_arg_rel cenv cx sa sb es' u (x,expr_type e) v` by
    (irule log_arg_rel_frame >> simp[] >>
     qexistsl_tac [`ctx`, `es1`, `func`] >>
     qexistsl_tac [`t`, `sm`] >> gvs[]) >>
  simp[log_args_post_def] >> conj_tac
  >- (drule_all log_args_post_state >> simp[]) >>
  conj_tac
  >- (gvs[log_args_post_def] >> irule listTheory.LIST_REL_mono >>
      goal_assum (drule_at Any) >> rpt strip_tac >>
      drule_all log_arg_rel_start_mono >> simp[]) >>
  drule_all wb_frame_trans >> simp[]
QED
