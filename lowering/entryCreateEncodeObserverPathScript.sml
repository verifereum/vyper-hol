(* Fold the guarded transfer law along the actual stopped observer path. *)
Theory entryCreateEncodeObserverPath
Ancestors
  exprSimAbiGasBridge abiEncoderExtendControl abiEncoderExtendSim
  entryCreatePathScope createSizePrefixReplay createMarkedPath
  fragGasOriginPtr fragExec venomExecSemantics venomInst venomState
  relation list pair pred_set

Theorem stopped_observer_no_ok_edge[local]:
  (s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut b ==>
  ~gas_origin_ptr_edge (D,lo,explicit,oc,frag_observer a b f id,PG)
    (s,G,tn) marks (OK t,G',tn')
Proof
  rpt strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  `inst = mk_inst id STOP [] []` by
    (gvs[frag_observer_cut_def, frag_observer_cut_lookup,
         frag_observer_cut_instruction]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def, exit_result_def]
QED

Theorem create_prefix_empty_cons[local]:
  create_prefix_step a b explicit ctx f s [] u /\
  create_expr_prefix a b explicit ctx f u [] t ==>
  create_expr_prefix a b explicit ctx f s [] t
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule (cj 2 RTC_rules) >> qexists_tac `(u,[])` >>
  simp[create_marked_edge_def] >> metis_tac[]
QED

Theorem create_encode_stopped_path_transfer:
  (!u G tn v H nu.
    guard u /\ (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region a b /\
    (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b /\
    gas_origin_ptr_edge (D,lo,explicit,oc,frag_observer a b f id,PG)
      (u,G,tn) [] (OK v,H,nu) ==>
    gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,G,tn) [] (OK v,H,nu) /\
    create_prefix_step a b explicit ctx f u [] v /\
    abi_observer_step ctx f (frag_observer_cut b) u v /\
    (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b /\ guard v) /\
  guard s /\ (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b /\
  gas_origin_ptr_path (D,lo,explicit,oc,frag_observer a b f id,PG)
    (s,G,tn) [] (OK t,G',tn') ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,f,PG) (s,G,tn) [] (OK t,G',tn') /\
  create_expr_prefix a b explicit ctx f s [] t /\
  abi_encoder_extend_sim ctx f s t
Proof
  strip_tac >>
  `!config entry marks result. gas_origin_ptr_path config entry marks result ==>
    !u Gu tu v Gv tv.
      config = (D,lo,explicit,oc,frag_observer a b f id,PG) /\
      entry = (u,Gu,tu) /\ marks = [] /\ result = (OK v,Gv,tv) /\
      guard u /\ (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region a b ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,f,PG) (u,Gu,tu) [] (OK v,Gv,tv) /\
      create_expr_prefix a b explicit ctx f u [] v /\
      abi_encoder_extend_sim ctx f u v` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >> rpt gen_tac
  >- simp[gas_origin_ptr_path_rules, abi_encoder_extend_sim_refl]
  >- (strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 `gas_origin_ptr_edge _ (u,Gu,tu) [] (OK mid,Gm,tm)` >>
      `(u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut b` by
        metis_tac[stopped_observer_no_ok_edge] >>
      qpat_assum `!u G tn v H nu. guard u /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `guard mid /\ _ ==> _` (drule_all_then strip_assume_tac) >>
      conj_tac
      >- (irule (SIMP_RULE (srw_ss()) []
            (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
              (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
          metis_tac[]) >>
      conj_tac >- metis_tac[create_prefix_empty_cons] >>
      drule abi_encoder_observer_step_extend_sim >>
      metis_tac[abi_encoder_extend_sim_trans]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED
