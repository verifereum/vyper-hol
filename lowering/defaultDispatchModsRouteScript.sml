(* The source and compiler tables need not use the same order. *)
Theory defaultDispatchModsRoute
Ancestors
  calldataSelectorProps selectorCompilerProps entryDispatchProps cfgNormSupplyProofs
  selectorDispatch moduleLoweringProps
  mem2varBlockSimHelpers list pair

Theorem default_linear_selector_mem[local]:
  MEM (sel,lbl) (MAP (\(s,l,z). (s,l)) (build_selectors tenv fs)) <=>
  ?mut nr rr name args ds ret b.
    MEM (mut,nr,rr,name,args,ds,ret,b) fs /\
    sel = abi_method_id tenv name (MAP SND args) /\ lbl = "fn_" ++ name
Proof
  simp[MEM_MAP, EXISTS_PROD] >> eq_tac >> rpt strip_tac
  >- (drule build_selectors_mem_inv >> simp[compute_selector_method_id] >>
      metis_tac[]) >>
  drule build_selectors_mem >>
  disch_then (qspec_then `tenv` mp_tac) >>
  simp[compute_selector_method_id] >> metis_tac[]
QED

Theorem default_linear_common_label[local]:
  !sels cd fallback sel lbl.
    MEM (sel,lbl) sels /\ calldata_hits_selector cd sel /\
    (!s l. MEM (s,l) sels /\ calldata_hits_selector cd s ==> l = lbl) ==>
    linear_dispatch_target cd sels fallback = lbl
Proof
  Induct >- simp[] >> PairCases >>
  rw[linear_dispatch_target_def] >> metis_tac[]
QED

Theorem default_linear_routes:
  ALL_DISTINCT (MAP (\(n,ts). abi_method_id tenv n ts) sigs) /\
  (!mut nr rr name args ds ret b.
    MEM (mut,nr,rr,name,args,ds,ret,b) fs ==> MEM (name,MAP SND args) sigs) ==>
  ((LENGTH cd < 4 \/ FIND (\(n,ts). abi_method_id tenv n ts = cd_selector cd) sigs = NONE ==>
    linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors tenv fs))
      fallback = fallback) /\
   (!mut nr rr name args ds ret b.
     MEM (mut,nr,rr,name,args,ds,ret,b) fs /\ 4 <= LENGTH cd /\
     FIND (\(n,ts). abi_method_id tenv n ts = cd_selector cd) sigs = SOME (name,MAP SND args) ==>
     linear_dispatch_target cd (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors tenv fs))
       fallback = "fn_" ++ name))
Proof
  simp[LET_THM] >> strip_tac >> conj_tac
  >- (Cases_on `LENGTH cd < 4` >- simp[linear_dispatch_target_short] >>
      simp[] >> strip_tac >> `4 <= LENGTH cd` by decide_tac >>
      irule linear_dispatch_target_fallback >> disj2_tac >>
      simp[default_linear_selector_mem, calldata_hits_selector_def,
           GSYM cd_selector_method_id] >>
      qpat_x_assum `FIND _ _ = NONE` mp_tac >>
      simp[FIND_NONE_EVERY, EVERY_MEM, combinTheory.o_DEF, FORALL_PROD] >>
      metis_tac[]) >>
  rpt strip_tac >>
  drule venomInstTheory.FIND_MEM >> strip_tac >>
  drule venomInstTheory.FIND_P >> simp[] >> strip_tac >>
  irule default_linear_common_label >> reverse conj_tac
  >- (qexists_tac `cd_selector cd` >>
      simp[default_linear_selector_mem, calldata_hits_selector_def,
           GSYM cd_selector_method_id] >> metis_tac[]) >>
  simp[default_linear_selector_mem, calldata_hits_selector_def,
       GSYM cd_selector_method_id] >>
  rpt gen_tac >>
  disch_then (qx_choosel_then [`m`,`n`,`r`,`other`,`params`,`ds'`,`ret'`,`b'`]
    strip_assume_tac) >>
  `MEM (other,MAP SND params) sigs` by metis_tac[] >>
  `(other,MAP SND params) = (name,MAP SND args)` by
    (irule (Q.ISPEC `\(n,ts). abi_method_id tenv n ts`
              all_distinct_map_mem_inj_cfg) >>
     map_every qexists_tac [`tenv`,`sigs`] >> simp[] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED
