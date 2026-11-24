(* The actual zero-instruction producer, before outcome packaging.
   An out-of-domain source trace needs no normal endpoint. *)
Theory bodyFullToplevelVVNil
Ancestors
  gasOutcomeFullCompose bodySimFull fragGasOriginPtr
  loweringPosts bodyPtrDefs exprSimMemDefs

Definition toplevel_vv_nil_def:
  toplevel_vv_nil (DF,lo,d,ctx,func) ce cx ty e es <=>
    !st0 sa sb vv s0 G0 tn0.
      compile_expr ce ty e sa = (vv,sb) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      (!H. dead_lo_ok H (DF H) lo ce cx) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
           stmt_state_rel H ctx func ce cx es s0 /\
           storage_well_formed_on cx es (FST H) /\
           ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) ==>
      ?tv ee.
        (!tail. eval_expr cx e (es with gas_obs := tail) =
                (INL tv,ee with gas_obs := tail)) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          sb = sa /\
          let er = ee with gas_obs := [] in
          vv_post H ctx func ce cx e es sa sb s0 er tv vv s0 /\
          vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) er tv vv s0 /\
          ghost_inv_at (DF H) lo d ce cx er G0 tn0 s0 /\
          ptr_vv_ok cx (post_value_type ce e) tv vv er G0 tn0 s0 /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
               ~is_bytestring_type (post_value_type ce e) ==>
               vv_own ce cx (post_value_type ce e) sa sb er tv vv s0 /\
               (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
          (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
           ?val. read_result cx tv er = (INL val,er) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                     eval_operand (vv_operand vv) s0 = SOME w ==>
                     w2n w + type_memory_size rt <= lo /\
                     (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
                            val_in_memory rt val (w2n w) mem)) /\
          (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
                   ptr_buf_ok ce e op G0 s0) /\
          (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok ce e p.ptr_operand G0 s0) /\
          ghost_kept_at lo ce es sa G0 tn0 s0 G0 tn0)
End

Theorem toplevel_vv_nil_full:
  toplevel_vv_nil (DF,lo,d,ctx,func) ce cx ty e es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
Proof
  rw[expr_vv_sim_full_def] >> fs[toplevel_vv_nil_def] >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`,`ee`,`INL tv`,`s0`,`tn0`] >>
  simp[gas_origin_ptr_path_rules] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >> simp[]
QED
