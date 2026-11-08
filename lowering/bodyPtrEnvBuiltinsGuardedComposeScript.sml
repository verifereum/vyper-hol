(* Zero-observation suffix composition retaining checked abort exits. *)
Theory bodyPtrEnvBuiltinsGuardedCompose
Ancestors bodyPtrEnvBuiltinsOperandCompose gasSummaryComposePtr
  bodyPtrDefs fragGasPathPtr gasSummary vyperInterpreter vyperState list
  exprSimDefs

Theorem guarded_suffix_marked_compose:
  gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
    marks (INL v) ee G tn (OK t) /\
  (!tail. next v (ee with gas_obs := tail) =
    (res,fin with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' r ==>
  gas_marked_exec_ptr D (ctx,fn) PG (bind source next)
    (es,s0,G0,tn0) marks res fin G' tn' r
Proof
  strip_tac >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
  qexistsl_tac [`G`, `ee`, `t`, `tn`, `v`] >> simp[] >>
  simp[gas_marked_exec_ptr_def]
QED

Theorem guarded_suffix_summary_compose:
  gas_summary_ptr_at D (ctx,fn) PG marks source (es,s0,G0,tn0) Q
    (\res ee gt r. expr_exit res r) /\
  (!res ee G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q (res : value + exception) (ee with gas_obs := []) G tn t ==>
    ?v res' fin G' tn' r. res = INL v /\
      (!tail. next v ((ee with gas_obs := []) with gas_obs := tail) =
        (res',fin with gas_obs := tail)) /\
      gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' r /\
      ((?u. r = OK u /\ Q' (res' : value + exception)
          (fin with gas_obs := []) G' tn' u) \/
       (exit_result r /\ expr_exit res' r))) ==>
  gas_summary_ptr_at D (ctx,fn) PG marks (bind source next)
    (es,s0,G0,tn0) Q' (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_summary_ptr_at_marked] >> strip_tac >> gvs[]
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all guarded_suffix_marked_compose >> strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> fs[expr_exit_def]
QED

Theorem guarded_suffix_outcome_compose:
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0) Q
    (\res ee gt r. expr_exit res r) /\
  (!marks res ee G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q (res : value + exception) (ee with gas_obs := []) G tn t ==>
    ?v res' fin G' tn' r. res = INL v /\
      (!tail. next v ((ee with gas_obs := []) with gas_obs := tail) =
        (res',fin with gas_obs := tail)) /\
      gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' r /\
      ((?u. r = OK u /\ Q' (res' : value + exception)
          (fin with gas_obs := []) G' tn' u) \/
       (exit_result r /\ expr_exit res' r))) /\
  (!marks err ee leaf finish.
    gas_exempt_cert F tops (ctx,fn) (ignore_bind source (return ()))
      (es,s0) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert F tops (ctx,fn) (ignore_bind (bind source next) (return ()))
      (es,s0) marks (err,ee) (leaf,finish)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (bind source next)
    (es,s0,G0,tn0) Q' (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule guarded_suffix_summary_compose >> goal_assum (drule_at Any) >>
      first_x_assum (qspec_then `marks` ACCEPT_TAC)) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  first_x_assum irule >> simp[]
QED
