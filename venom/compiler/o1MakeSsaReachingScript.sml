Theory o1MakeSsaReaching
Ancestors
  makeSsaCurrentDefs o1MakeSsaOwnership o1MakeSsaFlags o1MakeSsaFormats
  venomInst list alist pair

(* Syntactic reaching-name boundaries.  Defaults are not eliminated. *)

Theorem reaching_outputs_absent:
  !vs s rs rt t names x.
    rename_current_outputs s rs vs = (rt,t,names) /\ ~MEM x vs ==>
    latest_current_name rt x = latest_current_name rs x
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule current_push_latest >> simp[]
QED

Theorem reaching_inst_absent:
  rename_current_inst s rs inst = (rt,t,out) /\ ~MEM x inst.inst_outputs ==>
  latest_current_name rt x = latest_current_name rs x
Proof
  simp[rename_current_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[reaching_outputs_absent]
QED

Theorem reaching_block_absent:
  !insts s rs rt t outs x.
    rename_current_block_insts s rs insts = (rt,t,outs) /\
    EVERY (\i. ~MEM x i.inst_outputs) insts ==>
    latest_current_name rt x = latest_current_name rs x
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all reaching_inst_absent >> simp[]
QED

(* The incoming name alternative is essential for uses without a definition. *)
Theorem reaching_outputs_source:
  !vs s rs rt t names x.
    rename_current_outputs s rs vs = (rt,t,names) ==>
    latest_current_name rt x = latest_current_name rs x \/
    MEM (x,latest_current_name rt x) (ZIP (vs,names))
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule rename_current_outputs_length >> strip_tac >> simp[ZIP] >>
  first_x_assum drule >> disch_then (qspec_then `x` strip_assume_tac)
  >- (drule current_push_latest >> disch_then (qspec_then `x` mp_tac) >>
      Cases_on `x = h` >> simp[]) >>
  simp[]
QED

Theorem reaching_outputs_append:
  !pre post s rs.
    rename_current_outputs s rs (pre ++ post) =
    let (mid,u,ns) = rename_current_outputs s rs pre in
    let (rt,t,ms) = rename_current_outputs u mid post in
      (rt,t,ns ++ ms)
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem reaching_outputs_last:
  rename_current_outputs s rs (pre ++ [x] ++ post) = (rt,t,names) /\
  ~MEM x post ==>
  ?before n after. names = before ++ [n] ++ after /\
    LENGTH before = LENGTH pre /\ latest_current_name rt x = n
Proof
  simp[reaching_outputs_append, rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all reaching_outputs_absent >> strip_tac >>
  drule current_push_latest >> disch_then (qspec_then `x` mp_tac) >> simp[] >>
  strip_tac >> drule rename_current_outputs_length >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem reaching_phi_pairs_update:
  !rs pred ops. phi_pairs (update_current_phi_for_pred rs pred ops) =
    MAP (\(l,v). (l, if l = pred then latest_current_name rs v else v))
      (phi_pairs ops)
Proof
  recInduct update_current_phi_for_pred_ind >>
  simp[update_current_phi_for_pred_def, phi_pairs_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[phi_pairs_def]
QED
