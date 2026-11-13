(* Memory-only transport for one typed-array element write. *)
Theory bodyPtrIntCallArrayInvariant
Ancestors
  exprSimPtrTopLevelStorageFrame list pred_set arithmetic

Theorem intcall_array_robust_step:
  !vs k stv dtv a b ss ds mem mem' dirty dirty'.
  k < LENGTH vs /\
  (!j. j < LENGTH vs ==>
    val_wf stv (EL j vs) /\ val_footprint stv (EL j vs) <= ss /\
    val_wf dtv (EL j vs) /\ val_footprint dtv (EL j vs) <= ds) /\
  (!i. a <= i /\ i < a + LENGTH vs * ss ==>
    ~(b <= i /\ i < b + LENGTH vs * ds)) /\
  (!j. j < k ==> !m. mem_agree_outside dirty mem m ==>
    val_in_memory dtv (EL j vs) (b + j * ds) m) /\
  (!j. k <= j /\ j < LENGTH vs ==> !m. mem_agree_outside dirty mem m ==>
    val_in_memory stv (EL j vs) (a + j * ss) m) /\
  (!i. ~(b + k * ds <= i /\ i < b + (k+1) * ds) ==>
    mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
  (!i. ~(b + k * ds <= i /\ i < b + (k+1) * ds) /\ i IN dirty' ==>
    i IN dirty) /\
  (!m. mem_agree_outside dirty' mem' m ==>
    val_in_memory dtv (EL k vs) (b + k * ds) m) ==>
  (!j. j < k+1 ==> !m. mem_agree_outside dirty' mem' m ==>
    val_in_memory dtv (EL j vs) (b + j * ds) m) /\
  (!j. k+1 <= j /\ j < LENGTH vs ==> !m. mem_agree_outside dirty' mem' m ==>
    val_in_memory stv (EL j vs) (a + j * ss) m)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gen_tac >> strip_tac >> Cases_on `j = k` >- gvs[] >>
      `j < k /\ j < LENGTH vs` by decide_tac >>
      `val_wf dtv (EL j vs) /\ val_footprint dtv (EL j vs) <= ds` by metis_tac[] >>
      `!i. b + j * ds <= i /\ i < b + j * ds + val_footprint dtv (EL j vs) ==>
        ~(b + k * ds <= i /\ i < b + (k+1) * ds)` by
        (rpt strip_tac >>
         `(j+1)*ds <= k*ds` by (irule LESS_MONO_MULT2 >> decide_tac) >>
         gvs[RIGHT_ADD_DISTRIB] >> decide_tac) >>
      rpt strip_tac >> irule toplevel_robust_exterior_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`mem`, `mem'`, `dirty`, `dirty'`,
        `{i | b + k * ds <= i /\ i < b + (k+1) * ds}`] >>
      simp[] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `val_wf stv (EL j vs) /\ val_footprint stv (EL j vs) <= ss` by metis_tac[] >>
  `!i. a + j * ss <= i /\ i < a + j * ss + val_footprint stv (EL j vs) ==>
    ~(b + k * ds <= i /\ i < b + (k+1) * ds)` by
    (rpt strip_tac >>
     `(j+1)*ss <= LENGTH vs * ss /\ (k+1)*ds <= LENGTH vs * ds` by
       (conj_tac >> irule LESS_MONO_MULT2 >> decide_tac) >>
     `a <= i /\ i < a + LENGTH vs * ss` by
       (qpat_x_assum `(j+1)*ss <= _` mp_tac >>
        pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
     qpat_x_assum `!i. a <= i /\ _ ==> _` drule >>
     qpat_x_assum `(k+1)*ds <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  rpt strip_tac >> irule toplevel_robust_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `mem'`, `dirty`, `dirty'`,
    `{i | b + k * ds <= i /\ i < b + (k+1) * ds}`] >>
  simp[] >> metis_tac[]
QED
