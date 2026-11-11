Theory readonlyInvokeCopyFwdStepsDret
Ancestors
  readonlyInvokeCopyFwdStepsMemory readonlyInvokeCopyFwdStepsCore
  readonlyInvokeCopyFwdRel venomExecSemantics venomState venomInstProofs1
  taintAgree ptrDiscipline internalReturnCopyFwdSim venomInst words list pred_set
  o1LowerDloadRangeTransport

(* Raw taint follows the snapshots used by each individual MCOPY. *)
Definition ricf_pack_mem_def:
  ricf_pack_mem cursor sp sz M =
    (M DIFF {i | w2n cursor <= i /\ i < w2n cursor + w2n sz}) UNION
    {w2n cursor+k | k < w2n sz /\ w2n sp+k IN M}
End

Definition ricf_pack_taint_def:
  ricf_pack_taint cursor [] tn = tn /\
  ricf_pack_taint cursor ((sp,sz)::rest) tn =
    ricf_pack_taint (cursor + n2w (ceil32 (w2n sz))) rest
      (tn with t_mem := ricf_pack_mem cursor sp sz tn.t_mem)
End

(* These checks are evaluated at the concrete states after each finite prefix.
   In particular, reads are not assumed to survive overlapping earlier writes. *)
Definition ricf_pack_checks_def:
  ricf_pack_checks gam cursor [] qs M s t = (qs = []) /\
  ricf_pack_checks gam cursor ((sp,sz)::rest) qs M s t =
    case qs of
      [] => F
    | (sp',sz')::tail =>
        sz = sz' /\
        (!k. k < w2n sz ==>
          (w2n sp+k IN M <=> w2n sp'+k IN M) /\
          (w2n sp+k NOTIN M ==>
            read_byte (w2n sp+k) s.vs_memory =
            read_byte (w2n sp'+k) t.vs_memory)) /\
        (!db sb n k. (db,sb,n) IN gam /\ k < n ==>
          ~(w2n cursor <= db+k /\ db+k < w2n cursor+w2n sz) /\
          ~(w2n cursor <= sb+k /\ sb+k < w2n cursor+w2n sz)) /\
        ricf_pack_checks gam (cursor + n2w (ceil32 (w2n sz))) rest tail
          (ricf_pack_mem cursor sp sz M)
          (mcopy (w2n cursor) (w2n sp) (w2n sz) s)
          (mcopy (w2n cursor) (w2n sp') (w2n sz) t)
End

Theorem ricf_cert_mcopy_primitive:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  (!k. k < w2n sz ==>
    (w2n sp+k IN tn0.t_mem <=> w2n sp'+k IN tn0.t_mem) /\
    (w2n sp+k NOTIN tn0.t_mem ==> read_byte (w2n sp+k) s.vs_memory =
      read_byte (w2n sp'+k) t.vs_memory)) /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb n k. (db,sb,n) IN gam /\ k < n ==>
      ~(w2n cursor <= db+k /\ db+k < w2n cursor+w2n sz) /\
      ~(w2n cursor <= sb+k /\ sb+k < w2n cursor+w2n sz)) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (mcopy (w2n cursor) (w2n sp) (w2n sz) s) G0)
    (ricf_effective_taint fn (mcopy (w2n cursor) (w2n sp) (w2n sz) s)
      (tn0 with t_mem := ricf_pack_mem cursor sp sz tn0.t_mem)) fn
    sites maps targets G0 (tn0 with t_mem := ricf_pack_mem cursor sp sz tn0.t_mem)
    cur curs (mcopy (w2n cursor) (w2n sp) (w2n sz) s)
    (mcopy (w2n cursor) (w2n sp') (w2n sz) t)
Proof
  strip_tac >>
  `!i. ~(w2n cursor <= i /\ i < w2n cursor+w2n sz) ==>
    (i IN ricf_pack_mem cursor sp sz tn0.t_mem <=> i IN tn0.t_mem)` by
    (simp[ricf_pack_mem_def] >> rpt strip_tac >> eq_tac >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >> BETA_TAC >>
  match_mp_tac (ricf_cert_write_memory |> Q.INST
    [`G` |-> `G`, `tn` |-> `tn`, `len` |-> `w2n sz`]) >>
  simp[ld_read_memory_length] >>
  conj_tac >- simp[ricf_pack_mem_def, SUBSET_DEF] >>
  conj_tac
  >- (rpt strip_tac >> simp[ld_read_memory_element] >>
      `w2n sp+k NOTIN tn0.t_mem` by
        (fs[ricf_pack_mem_def] >> metis_tac[]) >> gvs[]) >>
  rpt strip_tac >>
  `~(w2n cursor <= db+k /\ db+k < w2n cursor+w2n sz) /\
   ~(w2n cursor <= sb+k /\ sb+k < w2n cursor+w2n sz)` by metis_tac[] >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Definition ricf_pack_footprint_def:
  ricf_pack_footprint sites maps stk cur curs =
    {tr | tr IN cur \/ (?gam. MEM gam curs /\ tr IN gam) \/
      tr IN ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ tr IN ricf_site_triples (EL j maps))}
End

Theorem ricf_cert_pack_dret_dynamic:
  !pairs cursor qs D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t
    ps fc u pt gc v.
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_pack_checks (ricf_pack_footprint sites maps stk cur curs)
    cursor pairs qs tn0.t_mem s t /\
  pack_dret_dynamic cursor pairs s = (ps,fc,u) /\
  pack_dret_dynamic cursor qs t = (pt,gc,v) ==>
  ps = pt /\ fc = gc /\
  ricf_cert_core D ids stk PG (ricf_effective_prov fn u G0)
    (ricf_effective_taint fn u (ricf_pack_taint cursor pairs tn0)) fn
    sites maps targets G0 (ricf_pack_taint cursor pairs tn0) cur curs u v
Proof
  Induct_on `pairs`
  >- (simp[ricf_pack_checks_def, ricf_pack_taint_def] >>
      rpt strip_tac >> gvs[] >>
      fs[ricf_cert_core_def, ricf_live_boundary_core_def,
         ricf_effective_prov_def, ricf_effective_taint_def]) >>
  qx_gen_tac `h` >> gen_tac >> qx_gen_tac `qs` >>
  PairCases_on `h` >> namedCases_on `qs` ["", "h tail"]
  >- simp[ricf_pack_checks_def] >>
  PairCases_on `h` >>
  simp[ricf_pack_checks_def, ricf_pack_taint_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `ricf_cert_core D ids stk PG
     (ricf_effective_prov fn (mcopy (w2n cursor) (w2n h0) (w2n h1) s) G0)
     (ricf_effective_taint fn (mcopy (w2n cursor) (w2n h0) (w2n h1) s)
       (tn0 with t_mem := ricf_pack_mem cursor h0 h1 tn0.t_mem)) fn
     sites maps targets G0 (tn0 with t_mem := ricf_pack_mem cursor h0 h1 tn0.t_mem)
     cur curs (mcopy (w2n cursor) (w2n h0) (w2n h1) s)
     (mcopy (w2n cursor) (w2n h0') (w2n h1) t)` by
    (irule ricf_cert_mcopy_primitive >> simp[] >>
     fs[ricf_pack_footprint_def] >> metis_tac[]) >>
  gvs[pack_dret_dynamic_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum drule >> disch_then drule >> simp[]
QED
