Theory augAssignPtrMemoryCompose
Ancestors
  gasSummaryComposePtr gasSummaryCompose gasExemptCert gasOutcome
  fragGasPathPtr fragExec stmtSimAugAssignPlaceMemory bodyPtrBytestringBuiltinsUnary
  vyperInterpreter vyperState vyperAST exprSimLen exprSimDefs loweringPosts

Theorem aug_place_memory_reads_outcome_ptr:
  read_place cx (MemoryPlace id path) st = (INL cur,st) /\
  place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k cur ptv) (st,s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (read_place cx (MemoryPlace id path))
      (\v. bind (place_type_value cx (MemoryPlace id path)) (k v)))
    (st,s,G,tn) Q R
Proof
  strip_tac >>
  `!gs. read_place cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL cur,st with gas_obs := gs)` by simp[len_rp_obs] >>
  `!gs. place_type_value cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL ptv,st with gas_obs := gs)` by
    (Cases_on `lookup_scopes id st.scopes` >>
     gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, raise_def] >>
     Cases_on `subscripts_type x.type path` >> gvs[return_def, raise_def]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def]) >>
  rewrite_tac[gas_outcome_ptr_def]
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_ptr_at_def, bind_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (aug_place_memory_reads_error_cert |> SPEC_ALL |> Q.INST
    [`k` |-> `\v pt. ignore_bind (h v pt) (return ())`] |>
    CONV_RULE (DEPTH_CONV BETA_CONV) |>
    REWRITE_RULE [ignore_bind_def, bind_assoc]) >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Theorem aug_place_memory_outer_place_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL (PlaceR (MemoryPlace id path))) raw G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G2 tn2 (OK u) /\
  read_place cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL ptv,raw with gas_obs := []) /\
  gas_outcome_ptr D tops (ctx,fn) PG (k (MemoryPlace id path) cur ptv)
    (raw with gas_obs := [],u,G2,tn2) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_target_place cx bt) (\p.
      bind (read_place cx p) (\v. bind (place_type_value cx p) (k p v))))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> rewrite_tac[aug_place_target_bind_base] >>
  irule gas_outcome_ptr_bind_normal >> goal_assum (drule_at Any) >>
  simp[get_place_def, bind_return] >> reverse conj_tac
  >- (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
      irule aug_place_memory_reads_outcome_ptr >> simp[]) >>
  rpt strip_tac >> irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[get_place_def, bind_return]
QED

(* The target and RHS retain separate counted prefixes.  The RHS outcome
   includes its exceptional and exempt executions, not just its value case. *)
Theorem augassign_memory_rhs_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL (PlaceR (MemoryPlace id path))) raw G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G2 tn2 (OK u) /\
  read_place cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL ptv,raw with gas_obs := []) /\
  gas_outcome_ptr D tops (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx))
    (raw with gas_obs := [],u,G2,tn2) P E /\
  (!res ee G tn s. P res ee G tn s ==>
    ?rhs. res = INL rhs /\
      gas_outcome_ptr D tops (ctx,fn) PG
        (bind (lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          ptv bop cur rhs)) (write_place cx (MemoryPlace id path)))
        (ee,s,G,tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_memory_outer_place_outcome_ptr) >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
  rewrite_tac[GSYM bind_assoc] >>
  irule bodyPtrBytestringBuiltinsUnaryTheory.gas_outcome_ptr_value_bind >>
  goal_assum (drule_at Any) >> qexists_tac `P` >> simp[] >> metis_tac[]
QED

Theorem augassign_base_exit_outcome_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INR exc) fin G tn r /\
  exit_result r /\ R (INR exc) (fin with gas_obs := []) (G,tn) r ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> simp[Once evaluate_def, aug_place_target_bind_base] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  irule gas_summary_ptr_at_bind_exception >> goal_assum (drule_at Any) >> simp[]
QED

Theorem augassign_base_exempt_outcome_ptr:
  gas_exempt_cert F tops (ctx,fn)
    (ignore_bind (eval_base_place cx bt) (return ())) (es,s0)
    marks (err,ee) (leaf,fin) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  simp[ignore_bind_def, Once evaluate_def, bind_assoc,
       aug_place_target_bind_base] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED
