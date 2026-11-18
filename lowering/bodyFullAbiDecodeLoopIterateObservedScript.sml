(* Bounded iteration with one outcome for all horizons and observers. *)
Theory bodyFullAbiDecodeLoopIterateObserved
Ancestors
  fragGasOriginPtrLoop fragGasPath venomExecSemantics venomState arithmetic

Theorem abi_decode_loop_iterate_observed:
  (!s G tn. Inv n s G tn ==>
    ?t Gf tnf.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      (!obs. Obs obs ==> gas_path ctx obs s 0 (OK t)) /\
      Q t Gf tnf) /\
  (!j s G tn. j < n /\ Inv j s G tn ==>
    ((?t Gf tnf.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
      (!obs. Obs obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
     (?u Gu tnu.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK u,Gu,tnu)) /\
      (!obs. Obs obs ==> gas_path ctx obs s 0 (OK u)) /\
      Inv (SUC j) u Gu tnu))) ==>
  !j s G tn. j <= n /\ Inv j s G tn ==>
    ((?t Gf tnf.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
      (!obs. Obs obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
     (?t Gf tnf.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      (!obs. Obs obs ==> gas_path ctx obs s 0 (OK t)) /\
      Q t Gf tnf))
Proof
  strip_tac >> measureInduct_on `n-j` >> rpt gen_tac >> strip_tac >>
  Cases_on `j = n`
  >- (disj2_tac >> gvs[] >> metis_tac[]) >>
  `j < n /\ SUC j <= n /\ n - SUC j < n - j` by decide_tac >>
  qpat_x_assum `!j s G tn. j < n /\ _ ==> _`
    (qspecl_then [`j`, `s`, `G`, `tn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `Inv (SUC j) u Gu tnu` >>
  qpat_x_assum `!y. n-y < n-j ==> _`
    (qspec_then `SUC j` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`u`, `Gu`, `tnu`] mp_tac) >>
  (impl_tac >- simp[]) >>
  qpat_x_assum `!s G tn. Inv n s G tn ==> _` kall_tac >>
  strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> conj_tac
      >- (rpt strip_tac >> metis_tac[gas_origin_ptr_path_trans]) >>
      rpt strip_tac >>
      `gas_path ctx obs s (0 + 0) (Abort Revert_abort t)` suffices_by simp[] >>
      irule gas_path_then >> qexists_tac `u` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[gas_origin_ptr_path_trans]) >>
  rpt strip_tac >>
  `gas_path ctx obs s (0 + 0) (OK t)` suffices_by simp[] >>
  irule gas_path_then >> qexists_tac `u` >> simp[]
QED
