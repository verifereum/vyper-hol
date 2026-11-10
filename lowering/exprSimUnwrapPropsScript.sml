(* Pure compiled-value read and postcondition transport. *)
Theory exprSimUnwrapProps
Ancestors
  exprSimProps freshWrites exprSimDefs loweringPosts list finite_map
  exprLowering compileEnv vyperAST vyperState valueEncoding
  valueEncodingProofs vyperTypeSystem venomInst venomState valueCopyBytes

Theorem vv_post_read_result:
  !func cenv cx e es sa sb s0 es' tv v vv s ctx.
    read_result cx tv es' = (INL v, es') ==>
    (vv_post ctx func cenv cx e es sa sb s0 es' tv vv s <=>
     vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s)
Proof
  rpt strip_tac >> Cases_on `vv` >>
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_own_def, storage_holds_def,
       immutable_holds_def, read_result_def, return_def]
QED

Theorem expr_post_of_vv_post_memory:
  !func cenv cx e es sa sb s0 es' v t p s ctx.
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v) (LocatedValue t p) s /\
    p.ptr_location = LocMemory /\ ~is_word_type t ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v p.ptr_operand s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  gvs[read_result_def, return_def, expr_val_rel_def, expr_val_at_def,
      expr_val_own_def, is_bytestring_word_type] >>
  first_x_assum irule >> simp[SF SFY_ss]
QED

Theorem expr_post_of_vv_post_load_physical:
  !func cenv cx e es sa sm sb s0 es' v t p op s1 s w ctx.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 /\
    is_word_type (post_value_type cenv e) /\ sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' s /\ eval_operand op s = SOME w /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
           w = typed_val_to_w256 tvt v) /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s1 = SOME w' ==>
            lookup_var x s = SOME w') /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_def]
  >~ [`expr_val_rel`] >- gvs[expr_val_rel_def]
  >~ [`expr_val_at`] >- simp[expr_val_at_def]
  >~ [`expr_val_own`] >- simp[expr_val_own_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- fs[vv_post_def]
  >~ [`locals_kept`]
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem expr_post_of_vv_post_load:
  !func cenv cx e es sa sm sb s0 es' v t p op s1 s w ctx.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 /\
    is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' s /\ eval_operand op s = SOME w /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           w = typed_val_to_w256 tvt v) /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s1 = SOME w' ==>
            lookup_var x s = SOME w') /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  qpat_x_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all expr_post_of_vv_post_load_physical >> simp[]
QED

Theorem expr_exit_exception_transport:
  !exc result.
    expr_res_ok (INR exc : value + exception) ==>
    (expr_exit (INR exc : eval_result + exception) result <=>
     expr_exit (INR exc : value + exception) result)
Proof
  rpt strip_tac >> gvs[expr_res_ok_def] >>
  Cases_on `result` >> simp[expr_exit_def]
QED
