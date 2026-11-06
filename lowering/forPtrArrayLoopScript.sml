(* Specialize the ghost-parametric rounds induction to the shared array
   invariant. Public entry is responsible for the static semantic producers. *)
Theory forPtrArrayLoop
Ancestors forPtrArrayAssemble forPtrArrayTerminal forPtrArrayInvariant forPtrRounds
  bodyPtrDefs loweringPosts stmtSimForArrayLoop vyperInterpreter
Libs monadsyntax

Theorem array_code_loop_counted_ptr:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride (Var bp)
    p sz ainst idx dv ov ep nv cond_lbl exit_lbl stmts_lbl incr_lbl
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = (bc',sb1) /\
  (!j ei. j < LENGTH vs /\ lookup_scopes name ei.scopes = SOME snapshot ==>
    stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)) /\
  (!j ei G tn s. Inv j ei G tn s <=>
    for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
      cond_lbl st s0 G0 tn0 d name snapshot j ei G tn s) /\
  (!ei G tn s. Done ei G tn s <=>
    for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d ei G tn s) /\
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  LENGTH vs < dimword (:256) /\
  snapshot.type = ArrayTV tv (Fixed n) /\ snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  (!j. j < LENGTH vs ==> value_has_type tv (EL j vs) /\ val_wf tv (EL j vs) /\
    w2n arr_base + j * stride < dimword (:256)) /\
  st.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!ei. lookup_scopes name ei.scopes = SOME snapshot /\
    lookup_scopes id ei.scopes = NONE ==>
    not_local_ptr bc (FEMPTY :: ei.scopes) p) /\
  ~ctx_has_dalloca ctx /\ ~bc.ce_is_ctor /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  (!x. not_fresh_at st x ==> not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> ep /\
    x <> idx /\ x <> nv) /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) ==>
  !k es s G tn.
    k <= LENGTH vs /\ Inv k es G tn s /\
    gas_admissible (eval_for cx tv id stmts (DROP k vs)) (stmt_res_ok lctx) es ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_for cx tv id stmts (DROP k vs)) (es,s,G,tn)
      (\res ee gf tf t. res = INL () /\ Done ee gf tf t)
      (\res ee gt r. ?ex. res = INR ex /\
        !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >> ho_match_mp_tac eval_for_rounds_ptr >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `lookup_scopes name es.scopes = SOME snapshot /\
       lookup_scopes id es.scopes = NONE` by
        (fs[for_array_inv_ptr_def, array_loop_inv_def, IgnAsm `vs = _`] >> metis_tac[]) >>
      `stmt_frag_ptr d ctx PG func cx (InLoop exit_lbl incr_lbl) RetQ bc
        (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
        (es with <|scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
          gas_obs := []|>)` by metis_tac[] >>
      `not_local_ptr bc (FEMPTY :: es.scopes) p /\
       value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
       w2n arr_base + k * stride < dimword (:256)` by metis_tac[] >>
      drule_all for_array_round_ptr >> simp[IgnAsm `vs = _`]) >>
  rpt gen_tac >> strip_tac >>
  `for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot (LENGTH vs) es G tn s` by metis_tac[] >>
  `not_local_ptr cenv es.scopes dv` by fs[array_for_code_def, IgnAsm `vs = _`] >>
  `(!x. not_fresh_at st x ==> x <> dv) /\
   (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x)` by metis_tac[] >>
  drule array_for_code_condition >> disch_tac >>
  drule_at (Pat `for_array_inv_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    for_array_terminal_ptr >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (simp[IgnAsm `vs = _`] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`t`, `gf`, `tf`] >> simp[IgnAsm `vs = _`]
QED
