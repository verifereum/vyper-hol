Theory bodyIntCallForceTransfer
Ancestors
  exprSimUnwrap bodyIntCallSemanticFrame exprSim loweringPosts fragExec
  vyperInterpreter vyperValueOperation vyperState exprLoweringProps

(* Reading a captured result is state preserving. A failed read makes
   vv_post impossible, so no extra abort execution is needed here.
   The callback is only successful Value forcing, not expression recursion. *)
Theorem unwrap_read_result_storage_frame_frag:
  read_result cx raw es' = (res,es') /\
  (!v. res = INL v ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\r. F)) ==>
  frag_exec ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `res`
  >- (rename1 `read_result cx raw es' = (INL v,es')` >>
      drule vv_post_read_result >> strip_tac >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
      irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]) >>
  irule frag_exec_conseq >> qexistsl [`\s. F`, `\s. F`, `\r. F`] >>
  simp[frag_exec_false_pre] >> metis_tac[vv_post_failed_read]
QED

(* All observations travel through the RAW fragment's own endpoint.
   Successful suffix correctness is a callback at that endpoint; no
   unrestricted expression simulation is assumed. *)
Theorem raw_to_forced_storage_frame_frag:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  eval_expr cx e es = (rawres,est) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\
  frag_exec ctx sa sm P
    (\s. ?raw. rawres = INL raw /\
         vv_post ctx func cenv cx e es sa sm s0 est raw vv s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit rawres) /\
  (!raw v. rawres = INL raw /\ read_result cx raw est = (INL v,est) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 est (Value v) vv s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\s. expr_post ctx func cenv cx e es sa sb s0 est v op s /\
           contract_storage s = saved /\ contract_transient s = savedT)
      (\r. F)) ==>
  frag_exec ctx sa sb P
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         contract_storage s = saved /\ contract_transient s = savedT)
    (expr_exit res)
Proof
  strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  Cases_on `rawres`
  >- (rename1 `eval_expr cx e es = (INL raw,est)` >>
      gvs[vyperStateTheory.bind_def] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      irule frag_exec_seq >>
      qexistsl [`\s. vv_post ctx func cenv cx e es sa sm s0 es' raw vv s /\
                    contract_storage s = saved /\ contract_transient s = savedT`, `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]) >>
      irule unwrap_read_result_storage_frame_frag >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[vyperStateTheory.bind_def] >>
  irule frag_exec_seq >> qexistsl [`\s. F`, `sm`] >> simp[] >> conj_tac
  >- (irule frag_exec_conseq >> first_assum (irule_at Any) >>
      simp[expr_exit_exception_transport]) >>
  simp[frag_exec_false_pre]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Framed forcing transfer has unproved dependencies"
  end) [unwrap_read_result_storage_frame_frag, raw_to_forced_storage_frame_frag];
