(* Tuple stores may read source gas while evaluating their destinations. *)
Theory assignTuplePtrOutcome
Ancestors
  tupleTargetStoreRun gasSummaryComposePtr gasExemptCert
  stmtLowering vyperInterpreter vyperState list

Theorem tuple_store_list_outcome_ptr:
  !gs vs tys ops sa sb es s G tn P Q R.
    (!st ee u H tt.
      P [] [] [] [] st ee H tt u ==>
      gas_outcome_ptr D tops (ctx,func) PG (return ())
        (ee,u,H,tt) Q R) /\
    (!g gs v vs ty tys op ops st sm ee u H tt.
      compile_tuple_store_all cenv [ty] [g] [op] st = ((),sm) /\
      P (g::gs) (v::vs) (ty::tys) (op::ops) st ee H tt u ==>
      gas_outcome_ptr D tops (ctx,func) PG (assign_tuple_targets cx g v)
        (ee,u,H,tt)
        (\res ee' H' tt' t. res = INL () /\
          P gs vs tys ops sm ee' H' tt' t)
        (\res ee' gt r. ?exc. res = INR exc /\ R (INR exc) ee' gt r)) /\
    EVERY (\g. ?bt. g = BaseTarget bt) gs /\
    LENGTH gs = LENGTH vs /\ LENGTH gs = LENGTH tys /\
    LENGTH gs = LENGTH ops /\
    compile_tuple_store_all cenv tys gs ops sa = ((),sb) /\
    P gs vs tys ops sa es G tn s ==>
    gas_outcome_ptr D tops (ctx,func) PG
      (assign_tuple_target_list cx gs vs) (es,s,G,tn) Q R
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `vs` >- gvs[] >> Cases_on `tys` >- gvs[] >>
  Cases_on `ops` >- gvs[] >>
  rename1 `P (h::gs) (v::vs') (ty::tys') (op::ops') sa es G tn s` >>
  `?bt. h = BaseTarget bt` by fs[] >> gvs[] >>
  drule tuple_store_base_cons >> strip_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_outcome_ptr_bind >>
  rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_unit >> metis_tac[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_unit >> metis_tac[])
  >> irule gas_outcome_ptr_conseq >>
  qexistsl_tac [
    `\res ee H tt t. res = INL () /\ P gs vs' tys' ops' sm ee H tt t`,
    `\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 `P gs vs' tys' ops' sm tail_es tail_G tail_tn tail_s` >>
      qpat_x_assum `!vs tys ops sa sb es s G tn P Q R. _`
        (qspecl_then [`vs'`, `tys'`, `ops'`, `sm`, `sb`,
          `tail_es`, `tail_s`, `tail_G`, `tail_tn`, `P`, `Q`, `R`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >> metis_tac[]
QED
