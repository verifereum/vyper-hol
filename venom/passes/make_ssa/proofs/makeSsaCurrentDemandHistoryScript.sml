Theory makeSsaCurrentDemandHistory
Ancestors
  makeSsaCurrentDemand
Libs
  listTheory arithmeticTheory

(* Syntactic cuts, not sequential execution of the parallel PHI prefix.
   List positions distinguish visits; cuts themselves need not be distinct. *)
Definition current_demand_cut_step_def:
  current_demand_cut_step fn (l,i) (m,j) <=>
    (?bb. lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\ m = l /\ j = SUC i) \/
    (?bb sb. lookup_block l fn.fn_blocks = SOME bb /\
      i = LENGTH bb.bb_instructions /\ MEM m (bb_succs bb) /\
      lookup_block m fn.fn_blocks = SOME sb /\ j = 0)
End

Definition current_cut_writes_def:
  current_cut_writes fn v (l,i) (m,j) <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\ m = l /\ j = SUC i /\
      MEM v (inst_defs (EL i bb.bb_instructions))
End

Definition current_demand_history_def:
  current_demand_history fn cuts <=>
    !k. SUC k < LENGTH cuts ==>
      current_demand_cut_step fn (EL k cuts) (EL (SUC k) cuts)
End

Theorem current_demand_history_nil[simp]:
  current_demand_history fn []
Proof
  simp[current_demand_history_def]
QED

Theorem current_demand_history_singleton[simp]:
  current_demand_history fn [cut]
Proof
  simp[current_demand_history_def]
QED

Theorem current_demand_history_cons:
  current_demand_history fn (a::b::cs) <=>
  current_demand_cut_step fn a b /\ current_demand_history fn (b::cs)
Proof
  simp[current_demand_history_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >- (first_x_assum (qspec_then `SUC k` mp_tac) >> simp[])
  >> Cases_on `k` >> gvs[]
QED

Theorem current_demand_history_pair[simp]:
  current_demand_history fn [a;b] <=> current_demand_cut_step fn a b
Proof
  simp[current_demand_history_cons]
QED

Theorem current_demand_cut_transport:
  current_demand_cut_step fn (l,i) (m,j) /\
  ~current_cut_writes fn v (l,i) (m,j) /\ current_demand fn v m j ==>
  current_demand fn v l i
Proof
  simp[current_demand_cut_step_def, current_cut_writes_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[current_demand_rules]
QED

Theorem current_demand_history_transport:
  current_demand_history fn cuts /\ cuts <> [] /\
  (!k. SUC k < LENGTH cuts ==>
    ~current_cut_writes fn v (EL k cuts) (EL (SUC k) cuts)) /\
  current_demand fn v (FST (LAST cuts)) (SND (LAST cuts)) ==>
  !k. k < LENGTH cuts ==>
    current_demand fn v (FST (EL k cuts)) (SND (EL k cuts))
Proof
  Induct_on `cuts` >- simp[] >>
  Cases_on `cuts` >- simp[] >>
  simp[current_demand_history_cons] >> rpt strip_tac >>
  rename [`current_demand_cut_step fn a b`,
          `current_demand_history fn (b::bs)`] >>
  `!k. k < LENGTH (b::bs) ==>
    current_demand fn v (FST (EL k (b::bs))) (SND (EL k (b::bs)))` by
    (qpat_x_assum `_ ==> !k. _` mp_tac >>
     (impl_tac >- (conj_tac >- (first_assum ACCEPT_TAC) >>
       conj_tac >- simp[] >> conj_tac
       >- (gen_tac >> strip_tac >>
         qpat_x_assum `!k. _ ==> ~current_cut_writes _ _ _ _`
           (qspec_then `SUC k'` mp_tac) >> gvs[]) >> (first_assum ACCEPT_TAC))) >> simp[]) >>
  Cases_on `k` >> gvs[] >>
  PairCases_on `a` >> PairCases_on `b` >>
  irule current_demand_cut_transport >>
  qexistsl_tac [`b1`,`b0`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!k. _ ==> ~current_cut_writes _ _ _ _`
        (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `!k. _ ==> current_demand _ _ _ _`
    (qspec_then `0` mp_tac) >> simp[]
QED

Theorem current_demand_history_last_write:
  current_demand_history fn cuts /\ cuts <> [] /\
  current_demand fn v (FST (LAST cuts)) (SND (LAST cuts)) ==>
  ((!k. SUC k < LENGTH cuts ==>
       ~current_cut_writes fn v (EL k cuts) (EL (SUC k) cuts)) /\
    current_demand fn v (FST (HD cuts)) (SND (HD cuts))) \/
  (?k. SUC k < LENGTH cuts /\
    current_cut_writes fn v (EL k cuts) (EL (SUC k) cuts) /\
    (!r. k < r /\ SUC r < LENGTH cuts ==>
      ~current_cut_writes fn v (EL r cuts) (EL (SUC r) cuts)) /\
    (!r. k < r /\ r < LENGTH cuts ==>
      current_demand fn v (FST (EL r cuts)) (SND (EL r cuts))))
Proof
  Induct_on `cuts` >- simp[] >>
  Cases_on `cuts` >- simp[] >>
  simp[current_demand_history_cons] >> rpt strip_tac >>
  rename [`current_demand_cut_step fn a b`,
          `current_demand_history fn (b::bs)`] >>
  qpat_x_assum `_ ==> _ \/ _` mp_tac >> simp[] >>
  strip_tac
  >- (Cases_on `current_cut_writes fn v a b`
      >- (disj2_tac >> qexists_tac `0` >> simp[] >> conj_tac
          >- (rpt strip_tac >> Cases_on `r` >> gvs[]) >>
          `!r. r < LENGTH (b::bs) ==>
            current_demand fn v (FST (EL r (b::bs)))
              (SND (EL r (b::bs)))` by
            (drule current_demand_history_transport >>
             disch_then (qspec_then `v` mp_tac) >> simp[]) >>
          rpt strip_tac >> Cases_on `r` >> gvs[]) >>
      disj1_tac >> conj_tac
      >- (rpt strip_tac >> Cases_on `k` >> gvs[]) >>
      PairCases_on `a` >> PairCases_on `b` >> gvs[] >>
      irule current_demand_cut_transport >>
      qexistsl_tac [`b1`,`b0`] >> simp[]) >>
  disj2_tac >> qexists_tac `SUC k` >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `r` >> gvs[]) >>
  rpt strip_tac >> Cases_on `r` >> gvs[]
QED
