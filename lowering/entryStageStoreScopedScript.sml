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
