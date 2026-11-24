(* The cut follows the supplied StructLit visit, not a field chosen by
   expression membership.  Administrative phases retain their landings. *)
Theory entryCreateStructLitVisit
Ancestors
  entryCreateNativeFirstExit entryCreateFocusSpec entryCreateCompletedCut
  createExprSizeExitDefs createSizePrefixReplay createSizeCutCode fragExec
  entryCreateBodyCut gasSummary gasSummaryCompose gasOutcomeFull fragGasOriginPtr
  exprSimMemorySource exprLowering exprLoweringProps emitHelper
  vyperInterpreter vyperStorageTrace vyperState venomInst venomExecSemantics
  list pair

Theorem structlit_admin_cut_prepend[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ ~s.vs_halted /\
  create_operand_full_scope a m E ctx f s [] (OK u) /\
  create_operand_cut a m E ctx f tops cx st0 source (es,s) /\
  create_operand_cut m b E ctx f tops cx st0 source (es,u) ==>
  create_operand_cut a b E ctx f tops cx st0 source (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (fs[create_operand_cut_def] >> metis_tac[]) >>
  `t = u /\ create_cut_marks E front = []` by
    (fs[create_operand_at_def] >> drule_all create_operand_full_scope_match >> simp[]) >>
  `gas_path ctx f s (LENGTH (create_cut_marks E front)) (OK t)` by
    metis_tac[create_prefix_gas_path] >>
  `gas_explicit (create_cut_marks E back) s.vs_gas_readings =
   gas_explicit (create_cut_marks E back) t.vs_gas_readings` by
    (drule gas_explicit_append_path >> simp[gas_explicit_def]) >>
  `create_body_cut E tops cx st0 source (es,t) (back,hit)` by
    metis_tac[create_operand_cut_def] >>
  gvs[create_body_cut_def] >> first_assum ACCEPT_TAC
QED

Theorem structlit_read_tail_cut[local]:
  read_result cx tv mid = (INL v,mid) /\
  create_operand_cut a b E ctx f tops cx st0 (eval_exprs cx xs) (mid,s) ==>
  create_operand_cut a b E ctx f tops cx st0
    (bind (read_result cx tv) (\v. bind (eval_exprs cx xs) (\vs. return (v::vs))))
    (mid,s)
Proof
  strip_tac >> fs[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[create_body_cut_def] >>
  disch_tac >> strip_tac >> rpt gen_tac >>
  drule read_result_gas_obs >> strip_tac >> simp[bind_def,return_def] >>
  Cases_on `eval_exprs cx xs
    (mid with gas_obs := gas_explicit (create_cut_marks E before) s.vs_gas_readings ++ tail)` >>
  qpat_x_assum `_ ==> !H' tail' rp ee'. _`
    (fn th => drule th >> disch_then (qspecl_then [`H`,`tail`,`q`,`r`] mp_tac)) >>
  Cases_on `q` >> simp[create_cut_failure_def] >> metis_tac[]
QED

(* The field continuation needs the all-tails equation even though replay
   itself is queried at one tail. Preserve the selected normal witness. *)
Definition structlit_landing_def:
  structlit_landing (DF,lo,E,ctx,f,PG) cx st0 source (es,s,G,tn) P
    H res mid G1 tn1 t <=>
    P H res mid G1 tn1 t /\
    ?marks. storage_trace_domain cx st0 mid.storage_trace /\
      (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
              (res,mid with gas_obs := tail)) /\
      (!H'. valid_horizon cx st0 H' mid.storage_trace ==>
            gas_origin_ptr_path (DF H',lo,E,ctx,f,PG) (s,G,tn) marks
              (OK t,G1,tn1) /\ P H' res mid G1 tn1 t)
End

Theorem structlit_completed_landing[local]:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    source (es,s,G,tn) P R ==>
  gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 a m
    source (es,s,G,tn) (structlit_landing (DF,lo,E,ctx,f,PG) cx st0 source (es,s,G,tn) P)
Proof
  strip_tac >> irule scoped_outcome_completed_operand >> simp[] >>
  qexists_tac `R` >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[scoped_operand_outcome_def]) >>
  simp[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
      strip_tac >> simp[structlit_landing_def, exit_result_def] >>
      qexists_tac `marks` >> simp[] >> qx_gen_tac `hor` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `hor` mp_tac) >>
      gvs[exit_result_def]) >>
  simp[]
QED

Definition structlit_after_vv_def:
  structlit_after_vv cx xs tv =
    bind (read_result cx tv) (\v. bind (eval_exprs cx xs) (\vs. return (v::vs)))
End

Theorem structlit_after_vv_frame[local]:
  storage_trace_frame (structlit_after_vv cx xs tv)
Proof
  simp[structlit_after_vv_def, storage_trace_frame_bind,
       storage_trace_frame_read_result, evaluate_storage_trace_frame,
       storage_trace_frame_return]
QED

Theorem structlit_visit_eval_cons[local]:
  eval_exprs cx (e::xs) = bind (eval_expr cx e) (structlit_after_vv cx xs)
Proof
  simp[Once evaluate_def, structlit_after_vv_def, FUN_EQ_THM, bind_def] >>
  gen_tac >> BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >> simp[]
QED

(* Specialization of the common pointwise replay-bind rule to the head
   expression and the source continuation of a StructLit field. *)
Definition structlit_visit_replay_law_def:
  structlit_visit_replay_law (DF,lo,E,ctx,f,PG) tops cx st0 <=>
    !a m b e xs es s G tn Q.
      (!p d k before hit after.
        create_interior_visit a b E ctx f (p,d,k) s (before,hit,after) ==>
        create_interior_visit a m E ctx f (p,d,k) s (before,hit,after) \/
        ?t d1 k1 front back.
          before = front ++ back /\ create_operand_at m t /\
          create_expr_prefix a m E ctx f s (create_cut_marks E front) t /\
          create_interior_visit m b E ctx f (p,d1,k1) t (back,hit,after)) /\
      ~s.vs_halted /\
      create_operand_cut a m E ctx f tops cx st0 (eval_expr cx e) (es,s) /\
      gas_completed_operand (DF,lo,E,ctx,f,PG) tops cx st0 a m
        (eval_expr cx e) (es,s,G,tn) Q /\
      (!H res mid G1 tn1 t. Q H res mid G1 tn1 t ==> ?tv. res = INL tv) /\
      (!H0 front tv mid G1 tn1 t.
        valid_horizon cx st0 H0 mid.storage_trace /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn)
            (create_cut_marks E front) (OK t,G1,tn1) /\
          Q H (INL tv) (mid with gas_obs := []) G1 tn1 t) ==>
        create_operand_cut m b E ctx f tops cx st0 (structlit_after_vv cx xs tv)
          (mid with gas_obs := [],t)) ==>
      create_operand_cut a b E ctx f tops cx st0
        (bind (eval_expr cx e) (structlit_after_vv cx xs)) (es,s)
End

Definition structlit_visit_region_def:
  structlit_visit_region f a b <=> create_cut_code {} a b /\ fn_has_code a b f
End

Definition structlit_admin_visit_def:
  structlit_admin_visit E ctx f tops cx st0 source es a m s u <=>
    ~s.vs_halted /\ create_operand_full_scope a m E ctx f s [] (OK u) /\
    create_operand_cut a m E ctx f tops cx st0 source (es,s)
End

Theorem structlit_admin_visit_cons[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  structlit_visit_region f a m /\ structlit_visit_region f m b /\
  structlit_admin_visit E ctx f tops cx st0 source es a m s u /\
  create_operand_cut m b E ctx f tops cx st0 source (es,u) ==>
  create_operand_cut a b E ctx f tops cx st0 source (es,s)
Proof
  simp[structlit_visit_region_def, structlit_admin_visit_def] >>
  metis_tac[structlit_admin_cut_prepend]
QED

(* Pre contains the ordinary field-list accumulator (cells, offset, shadow
   cursors, and all-horizon invariant). Its cons supplier advances it at
   the actual store exit; this induction never selects a new semantic run. *)
Theorem structlit_fields_visit_intro:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  structlit_visit_replay_law (DF,lo,E,ctx,f,PG) tops cx st0 /\
  (!a b es s G tn aux. Pre [] a b es s G tn aux ==> a = b) /\
  (!nm e fields a b es s G tn aux. Pre ((nm,e)::fields) a b es s G tn aux ==>
    ?m n l j P R.
      structlit_visit_region f a m /\ structlit_visit_region f m b /\
      structlit_visit_region f m n /\ structlit_visit_region f n b /\
      structlit_visit_region f n l /\ structlit_visit_region f l b /\
      structlit_visit_region f l j /\ structlit_visit_region f j b /\
      ~s.vs_halted /\
      create_operand_cut a m E ctx f tops cx st0 (eval_expr cx e) (es,s) /\
      scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
        (eval_expr cx e) (es,s,G,tn) P R /\
      (!H res mid G1 tn1 t. P H res mid G1 tn1 t ==> ?tv. res = INL tv) /\
      (!H0 tv mid G1 tn1 t.
        valid_horizon cx st0 H0 mid.storage_trace /\ mid.gas_obs = [] /\
        structlit_landing (DF,lo,E,ctx,f,PG) cx st0 (eval_expr cx e)
          (es,s,G,tn) P H0 (INL tv) mid G1 tn1 t ==>
        ?v t' z u G2 tn2 aux'.
          read_result cx tv mid = (INL v,mid) /\
          structlit_admin_visit E ctx f tops cx st0
            (structlit_after_vv cx (MAP SND fields) tv) mid m n t t' /\
          structlit_admin_visit E ctx f tops cx st0
            (structlit_after_vv cx (MAP SND fields) tv) mid n l t' z /\
          structlit_admin_visit E ctx f tops cx st0
            (structlit_after_vv cx (MAP SND fields) tv) mid l j z u /\
          Pre fields j b mid u G2 tn2 aux')) ==>
  !fields a b es s G tn aux. Pre fields a b es s G tn aux ==>
    create_operand_cut a b E ctx f tops cx st0 (eval_exprs cx (MAP SND fields)) (es,s)
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> `a = b` by metis_tac[] >>
      simp[create_operand_cut_def, create_interior_visit_def,
           create_operand_fetch_def, abiEncoderPropsTheory.frag_ids_def]) >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  qpat_assum `!nm e fields a b es s G tn aux. _` (fn th => drule th) >> strip_tac >>
  simp[structlit_visit_eval_cons] >>
  qpat_x_assum `structlit_visit_replay_law _ _ _ _`
    (irule o REWRITE_RULE[structlit_visit_replay_law_def]) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`G`,
    `structlit_landing (DF,lo,E,ctx,f,PG) cx st0 (eval_expr cx h1) (es,s,G,tn) P`,
    `m`,`tn`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> fs[structlit_visit_region_def] >>
      drule_all create_interior_visit_first_exit >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (fn th => drule th) >>
      strip_tac >> qabbrev_tac `ready = mid with gas_obs := []` >>
      `valid_horizon cx st0 H0 ready.storage_trace /\ ready.gas_obs = []` by
        simp[Abbr `ready`] >>
      qpat_x_assum `!H0 tv mid G1 tn1 t. _` (fn th => drule_all th) >>
      strip_tac >>
      map_every (fn (fin,st) =>
        irule structlit_admin_visit_cons >> simp[] >>
        (conj_tac >- (qexists_tac `ce` >> simp[])) >>
        qexistsl_tac [fin,st] >> simp[])
        [(`n`,`t'`),(`l`,`z`),(`j`,`u`)] >>
      simp[structlit_after_vv_def] >> irule structlit_read_tail_cut >>
      conj_tac >- (qexists_tac `v` >> simp[]) >>
      qpat_assum `!a b es s G tn aux. Pre fields a b es s G tn aux ==> _`
        (fn th => drule th) >> simp[])
  >- (simp[structlit_landing_def] >> metis_tac[]) >>
  irule structlit_completed_landing >> metis_tac[]
QED
