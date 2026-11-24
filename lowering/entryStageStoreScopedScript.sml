(* First-exit replay for the physical store's own endpoint and ghosts. *)
Theory entryStageStoreScoped
Ancestors
  entryStoreObserverStep entryStageStoreObserverCode logStoreDataOriginPtr
  entryCreatePathScope entryCreateFocusSpec createSizePrefixReplay createMarkedPath
  exprSimAbiGasBridge fragGasOriginPtr fragExec venomExecSemantics venomInst
  list pair relation
Libs
  stepInstBaseLib

Theorem stage_observer_stop_no_ok[local]:
  (s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut b ==>
  ~gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer a b fn id,PG)
    (s,G,tn) ms (OK t,Gf,tnf)
Proof
  strip_tac >> strip_tac >> gvs[frag_observer_cut_def] >>
  drule gas_origin_ptr_edge_common_fuel >>
  asm_simp_tac (srw_ss()) [frag_observer_cut_lookup, frag_observer_cut_instruction] >>
  simp[step_inst_non_invoke, opcode_clause ``STOP``, mk_inst_def]
QED

Theorem stage_prefix_cons_empty[local]:
  create_prefix_step a b explicit ctx fn s [] u /\
  create_expr_prefix a b explicit ctx fn u [] t ==>
  create_expr_prefix a b explicit ctx fn s [] t
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule (cj 2 RTC_RULES) >> qexists_tac `(u,[])` >>
  simp[create_marked_edge_def]
QED

Theorem stage_observer_path_transfer[local]:
  !cx st ms out. gas_origin_ptr_path cx st ms out ==>
    !D lo explicit ctx a b fn id PG s G tn t Gf tnf.
      cx = (D,lo,explicit,ctx,frag_observer a b fn id,PG) /\
      st = (s,G,tn) /\ ms = [] /\ out = (OK t,Gf,tnf) /\
      (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b /\
      (!u Gu tnu v Gv tnv.
        (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region a b /\
        (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b /\
        gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer a b fn id,PG)
          (u,Gu,tnu) [] (OK v,Gv,tnv) ==>
        gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tnu) [] (OK v,Gv,tnv) /\
        create_prefix_step a b explicit ctx fn u [] v /\
        (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b) ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
      create_expr_prefix a b explicit ctx fn s [] t
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      `(s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut b` by
        metis_tac[stage_observer_stop_no_ok] >>
      qpat_assum `!u Gu tnu v Gv tnv. _` (drule_all_then strip_assume_tac) >>
      qpat_x_assum `!a' b' fn' id'. _` (qspecl_then [`a`,`b`,`fn`,`id`] mp_tac) >>
      (impl_tac >- (conj_tac >- REFL_TAC >>
                    conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      reverse conj_tac >- metis_tac[stage_prefix_cons_empty] >>
      qpat_assum `gas_origin_ptr_edge (_,_,_,_,fn,_) (s,G,tn) [] _`
        (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
      simp[]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem stage_store_origin_ptr_scoped:
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
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  no_phi_fn func /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks sb)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    create_expr_prefix sa sb explicit ctx func s [] t /\ create_operand_at sb t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all stage_store_observer_code >>
  disch_then (qx_choose_then `id` (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`func` |-> `frag_observer sa sb func id`]
          compile_store_memory_origin_ptr_path) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
       create_expr_prefix sa sb explicit ctx func s [] t` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,frag_observer sa sb func id,PG) _ _ _`
       (qspec_then `D` (mp_then Any mp_tac stage_observer_path_transfer)) >>
     disch_then (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`sa`,`sb`,`func`,`id`,`PG`,
                             `s`,`G`,`tn`,`t`,`Gf`,`tnf`] mp_tac) >>
     simp[] >> impl_tac >-
       (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        irule store_observer_joint_step_fetch >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `id` >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!i l. MEM i (frag_code sa sb) /\ _ ==> _`
          (drule_all_then strip_assume_tac) >> metis_tac[]) >>
     simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >-
    (qx_gen_tac `mask` >>
     first_x_assum (qspec_then `mask` strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (first_x_assum (qspec_then `ARB` strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rewrite_tac[create_operand_at_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
