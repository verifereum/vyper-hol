(* Machine endpoint uniqueness at the slots observer's STOP cut. *)
Theory bodyFullStoreSlotsStaticTraceUnique
Ancestors
  fragGasOriginPtr fragExec exprSimAbiGasBridge abiEncoderObserver
  abiEncoderPrefixSafety ptrSafeRun venomExecSemantics venomInst venomState
  contextCodegenRel codegenRel unitTransformDefs list arithmetic
Libs
  stepInstBaseLib

Theorem store_slots_observer_cut_no_edge[local]:
  (s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut sb ==>
  ~gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (s,G,tn) marks (OK t,Gf,tnf)
Proof
  strip_tac >> strip_tac >> gvs[frag_observer_cut_def] >>
  drule gas_origin_ptr_edge_common_fuel >>
  asm_simp_tac (srw_ss()) [frag_observer_cut_lookup, frag_observer_cut_instruction] >>
  simp[step_inst_non_invoke, opcode_clause ``STOP``, mk_inst_def]
QED

Theorem store_slots_path_local_prefix[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    !D lo explicit ctx sa sb func id PG s G tn t Gf tnf.
      cx = (D,lo,explicit,ctx,frag_observer sa sb func id,PG) /\
      st = (s,G,tn) /\ marks = [] /\ out = (OK t,Gf,tnf) /\
      cs_extends sa sb /\ fn_has_code sa sb func /\ frag_gas_free sa sb /\
      (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
      (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb /\
      (!a Ga tna b Gb tnb.
        (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb /\
        (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut sb /\
        gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
          (a,Ga,tna) [] (OK b,Gb,tnb) ==>
        abi_observer_step ctx (frag_observer sa sb func id)
          (frag_observer_cut sb) a b) ==>
      local_prefix ctx (frag_observer sa sb func id) (frag_observer_cut sb) s t
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> irule (cj 1 local_prefix_rules) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      `(s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb` by
        metis_tac[store_slots_observer_cut_no_edge] >>
      `abi_observer_step ctx (frag_observer sa sb func' id)
         (frag_observer_cut sb) s mid` by metis_tac[] >>
      `(mid.vs_current_bb,mid.vs_inst_idx) IN frag_observer_region sa sb` by
        (drule_all frag_observer_region_closed >>
         simp[observer_region_closed_def] >> metis_tac[]) >>
      irule (cj 2 local_prefix_rules) >> qexists_tac `mid` >> simp[] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem store_slots_observer_cut_unique:
  cs_extends sa sb /\ fn_has_code sa sb func /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  local_prefix ctx (frag_observer sa sb func id) (frag_observer_cut sb) s u /\
  gas_origin_ptr_path (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (s,G,tn) [] (OK t,Gf,tnf) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb /\
  (!a Ga tna b Gb tnb.
    (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb /\
    (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut sb /\
    gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
      (a,Ga,tna) [] (OK b,Gb,tnb) ==>
    abi_observer_step ctx (frag_observer sa sb func id)
      (frag_observer_cut sb) a b) ==>
  u = t
Proof
  rpt strip_tac >>
  `local_prefix ctx (frag_observer sa sb func id) (frag_observer_cut sb) s t` by
    (irule store_slots_path_local_prefix >> metis_tac[]) >>
  metis_tac[local_prefix_endpoint_unique]
QED
