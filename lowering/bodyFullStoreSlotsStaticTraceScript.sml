Theory bodyFullStoreSlotsStaticTrace
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExec
  exprSimAbiGasBridge abiEncoderObserver exprSimAbiDecodeSetupObserve
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs
  list rich_list finite_map arithmetic

Theorem store_slots_path_finite:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    !t Gf tnf. marks = [] /\ out = (OK t,Gf,tnf) ==>
    ?L. L <> [] /\ HD L = st /\ LAST L = (t,Gf,tnf) /\
      (!n a Ga tna b Gb tnb.
        SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\
        EL (SUC n) L = (b,Gb,tnb) ==>
        gas_origin_ptr_edge cx (a,Ga,tna) [] (OK b,Gb,tnb))
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexists_tac `[(s,G,tn)]` >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      qexists_tac `(s,G,tn)::L` >> simp[] >>
      conj_tac >- (Cases_on `L` >> gvs[]) >>
      rpt gen_tac >> Cases_on `n` >> simp[] >> rpt strip_tac
      >- (Cases_on `L` >> gvs[]) >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED
