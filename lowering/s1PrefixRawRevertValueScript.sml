(* Request-prefix companion to bodyFullRawRevertValue. *)
Theory s1PrefixRawRevertValue
Ancestors
  s1PrefixPreds bodyFullRawRevertValue s1PrefixDefs

Theorem raw_revert_value_prefix_from_tail:
  (!(H : (bool # 256 word # type_value) list # num list) ctx func cenv cx e es (sa:compile_state) (sm:compile_state)
      (sb:compile_state) (s0:venom_state) ee bs op (t:venom_state)
      cap G tn D lo d explicit PG.
      compile_raw_revert op sm = ((),sb) /\
      fn_has_code sm sb func /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      ~t.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      (!x. op = Var x ==> not_fresh_at sm x) /\
      expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op t /\
      expr_store_bound cx (expr_type e) (BytesV bs) op t /\
      expr_type e = BaseT (BytesT (Dynamic cap)) /\
      evaluate_type (get_tenv cx) (expr_type e) =
        SOME (BaseTV (BytesT (Dynamic cap))) /\
      ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn t /\
      ghost_inv_at D lo d cenv cx ee G tn t ==>
      ?w G' tn'. !D'.
        gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
          (t,G,tn) [] (Abort Revert_abort w,G',tn')) ==>
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func
     cenv env ty es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty (Call ann RawRevert args dflt) es
Proof
  cheat
QED
