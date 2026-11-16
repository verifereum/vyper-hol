Theory bodyFullStructLitCopy
Ancestors
  logStoreDataOriginPtr gasOutcomeFullCompose

(* Select the store endpoint once, before specializing the dead-mask family.
   The continuation receives the entire physical and ghost frame, not just
   the destination's ordinary memory encoding. *)
Theorem structlit_var_store_full_suffix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee G1 tn1 t) ==>
    ?v sw dw.
      compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
      ~is_word_type dty /\ (is_bytestring_type dty ==> is_bytestring_type sty) /\
      type_memory_bytes cenv dty = type_memory_size dtv /\
      acyclic_struct_metadata cenv.ce_struct_fields /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv /\
      (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
         ALL_DISTINCT (MAP FST fields) /\
         EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
           sz = type_memory_size tv) fields) /\
      type_widens_to tenv sty dty /\
      evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
      value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
      not_fresh_at sa xs /\ not_fresh_at sa xd /\
      lookup_var xs t = SOME sw /\ lookup_var xd t = SOME dw /\
      (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
             val_in_memory stv v (w2n sw) mem) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
      (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= t.vs_alloca_next) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      ptr_covers G1 tn1 xs t (type_memory_size stv) /\
      ptr_covers G1 tn1 xd t (type_memory_size dtv) /\
      allocas_from lo t /\ lo <= t.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
      t.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!u G2 tn2.
        val_in_memory dtv v (w2n dw) u.vs_memory /\
        typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) t u /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        tn2.t_imm = tn1.t_imm /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
             (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
        (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
               val_in_memory dtv v (w2n dw) mem) /\
        (!p. not_fresh_at sa p ==>
           FLOOKUP G2 p = FLOOKUP G1 p /\ op_taint tn2 (Var p) = op_taint tn1 (Var p)) ==>
        !H. valid_horizon cx st0 H ee.storage_trace ==> Q' H res ee G2 tn2 u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >> irule gas_outcome_full_zero_suffix >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all compile_store_memory_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >>
  gen_tac >> disch_tac >> conj_tac >- simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem structlit_word_store_full_suffix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee G1 tn1 t) ==>
    ?v dw.
      compile_store_memory cenv src (Var xd) dty sty sa = ((),sb) /\
      is_word_type dty /\ evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\
      eval_operand src t = SOME (typed_val_to_w256 dtv v) /\ op_taint tn1 src = {} /\
      lookup_var xd t = SOME dw /\ w2n dw + 32 < dimword (:256) /\
      w2n dw + 32 <= t.vs_alloca_next /\ ptr_covers G1 tn1 xd t 32 /\
      allocas_from lo t /\ lo <= t.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
      fn_has_code sa sb func /\
      ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
      t.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!u G2 tn2.
        val_in_memory dtv v (w2n dw) u.vs_memory /\
        typed_copy_state_frame sa (w2n dw) 32 t u /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        tn2.t_imm = tn1.t_imm /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + 32) ==>
             (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
        (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
               val_in_memory dtv v (w2n dw) mem) /\
        (!p. FLOOKUP G2 p = FLOOKUP G1 p /\ op_taint tn2 (Var p) = op_taint tn1 (Var p)) ==>
        !H. valid_horizon cx st0 H ee.storage_trace ==> Q' H res ee G2 tn2 u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >> irule gas_outcome_full_zero_suffix >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >>
  gen_tac >> disch_tac >> conj_tac >- simp[] >>
  first_x_assum irule >> simp[]
QED
