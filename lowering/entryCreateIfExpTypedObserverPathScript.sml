(* Transfer the typed copy selected by the stopped observer, including ghosts. *)
Theory entryCreateIfExpTypedObserverPath
Ancestors
  bodyFullIfExpObserve entryCreateIfExpTypedStore entryCreateIntervalLayout
  entryCreateFocusSpec
  entryStoreObserverStep entryCreateCompletedCut createSizePrefixReplay
  createMarkedPath fragGasOriginPtr fragGasOrigin exprSimAbiGasBridge fragFuel
  fragExec venomExecSemantics venomInst relation list pair
Libs
  stepInstBaseLib

Theorem typed_observer_stop_no_ok[local]:
  (s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut b ==>
  ~gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer a b fn id,PG)
    (s,G,tn) ms (OK t,Gf,tnf)
Proof
  strip_tac >> strip_tac >> gvs[frag_observer_cut_def] >>
  drule gas_origin_ptr_edge_common_fuel >>
  asm_simp_tac (srw_ss()) [frag_observer_cut_lookup, frag_observer_cut_instruction] >>
  simp[step_inst_non_invoke, opcode_clause ``STOP``, mk_inst_def]
QED

(* The recorder changes only the entries of the list, not whether it is empty. *)
Theorem typed_observer_prefix_cons[local]:
  create_prefix_step a b explicit ctx fn s [] u /\
  create_expr_prefix a b E ctx fn u [] t ==>
  create_expr_prefix a b E ctx fn s [] t
Proof
  strip_tac >>
  `create_prefix_step a b explicit ctx fn s [] u <=>
   create_prefix_step a b E ctx fn s [] u` by
    simp[NoAsms, create_prefix_step_def, gas_origin_edge_def] >>
  `create_prefix_step a b E ctx fn s [] u` by metis_tac[] >>
  fs[create_expr_prefix_marked] >>
  irule (cj 2 RTC_RULES) >> qexists_tac `(u,[])` >>
  simp[create_marked_edge_def]
QED

Theorem typed_observer_path_transfer[local]:
  !cx st ms out. gas_origin_ptr_path cx st ms out ==>
    !D lo explicit ctx a b fn id PG s G tn t Gf tnf E.
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
      create_expr_prefix a b E ctx fn s [] t
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      `(s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut b` by
        metis_tac[typed_observer_stop_no_ok] >>
      qpat_assum `!u Gu tnu v Gv tnv. _` (drule_all_then strip_assume_tac) >>
      qpat_x_assum `!a' b' fn' id' E'. _`
        (qspecl_then [`a`,`b`,`fn`,`id`,`E`] mp_tac) >>
      (impl_tac >- (conj_tac >- REFL_TAC >>
                    conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      reverse conj_tac >- metis_tac[typed_observer_prefix_cons] >>
      qpat_assum `gas_origin_ptr_edge (_,_,_,_,fn,_) (s,G,tn) [] _`
        (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
      simp[]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem ifexp_typed_store_observation_from_install:
  (!ce xd dt xs st a b f.
    compile_store_memory_typed ce (Var xd) dt (Var xs) st a = ((),b) /\
    fn_has_code a b f /\ fn_inst_ids_distinct f /\ no_phi_fn f /\
    create_layout a b ==>
    ?id. fn_has_code a b (frag_observer a b f id) /\
      fn_inst_ids_distinct (frag_observer a b f id) /\
      (a.cs_current_bb,LENGTH a.cs_current_insts) IN frag_observer_region a b /\
      (!lbl idx bb i.
        (lbl,idx) IN frag_observer_region a b /\ (lbl,idx) <> frag_observer_cut b /\
        lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
        get_instruction bb idx = SOME i ==>
        MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\
        MEM i.inst_opcode [ADD; MLOAD; AND; MCOPY; NOT; MSTORE; INVALID; ASSIGN;
                           JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] /\
        ?real. lookup_block lbl f.fn_blocks = SOME real /\
               get_instruction real idx = SOME i) /\
      (!i lbl. MEM i (frag_code a b) /\ MEM i.inst_opcode [JMP; JNZ] /\
        MEM lbl (create_cut_targets i.inst_opcode i.inst_operands) ==>
        (lbl,0) IN frag_observer_region a b /\
        ?ob bb. lookup_block lbl (frag_observer a b f id).fn_blocks = SOME ob /\
                lookup_block lbl f.fn_blocks = SOME bb /\
                phi_prefix_length ob.bb_instructions = 0 /\
                phi_prefix_length bb.bb_instructions = 0)) ==>
  ifexp_observed_typed_store
    (\ctx f a b s t. create_layout a b /\ no_phi_fn f ==>
       create_operand_at a s /\ create_operand_full_scope a b E ctx f s [] (OK t))
Proof
  disch_then (mk_asm "install") >>
  simp_tac bool_ss [ifexp_observed_typed_store_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `fn_has_code sa sb func` >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  Cases_on `create_layout sa sb /\ no_phi_fn func`
  >- (pop_assum strip_assume_tac >>
      asm "install" (drule_all_then strip_assume_tac) >>
      mp_tac (Q.INST [`func` |-> `frag_observer sa sb func id`]
        ifexp_typed_store_selected_site) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
        (map_every assume_tac o CONJUNCTS)))) >>
      `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
           create_expr_prefix sa sb E ctx func s [] t` by
        (gen_tac >> irule typed_observer_path_transfer >>
         simp[] >> qexists_tac `id` >> simp[] >>
         rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         irule store_observer_joint_step_fetch >>
         rpt (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `id` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`t`,`Gf`,`tnf`] >>
      simp_tac bool_ss [create_operand_full_scope_def,exec_result_case_def] >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all ifexp_typed_store_selected_site >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  pure_once_rewrite_tac[GSYM DE_MORGAN_THM] >> first_assum ACCEPT_TAC
QED
