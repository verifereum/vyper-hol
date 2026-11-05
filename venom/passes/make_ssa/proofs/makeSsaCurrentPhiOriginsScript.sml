Theory makeSsaCurrentPhiOrigins
Ancestors
  makeSsaCurrentJointRuntime makeSsaCurrentPhiBatch venomWf
  venomExecSemantics venomState venomInst stateFrame list alist

Definition current_phi_origin_read_def:
  current_phi_origin_read incoming prev phi binding <=>
    ?src. phi.inst_outputs = [FST binding] /\
      resolve_phi prev phi.inst_operands = SOME (Var src) /\
      ALOOKUP incoming src = SOME (SND binding)
End

Theorem current_phi_resolve_var:
  !ops. phi_well_formed ops /\ resolve_phi prev ops = SOME op ==>
    ?src. op = Var src
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  rw[phi_well_formed_def, resolve_phi_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem current_phi_origin_read_eval:
  current_phi_origin_read M prev phi (dst,origin) /\
  current_origin_realizes V M st /\ st.vs_prev_bb = SOME prev ==>
  eval_one_phi st phi = OPTION_MAP (\value. (dst,value)) (V origin)
Proof
  rw[current_phi_origin_read_def, eval_one_phi_def] >>
  fs[current_origin_realizes_def] >>
  first_x_assum (qspec_then `src` mp_tac) >> simp[eval_operand_def] >>
  Cases_on `V origin` >> simp[]
QED

Theorem current_phi_origin_extract:
  phi.inst_opcode = PHI /\ inst_wf phi /\
  st.vs_prev_bb = SOME prev /\ current_origin_realizes V M st /\
  eval_one_phi st phi = SOME (dst,value) ==>
  ?origin. current_phi_origin_read M prev phi (dst,origin) /\
    V origin = SOME value
Proof
  strip_tac >>
  `LENGTH phi.inst_outputs = 1 /\ phi_well_formed phi.inst_operands`
    by gvs[inst_wf_def] >>
  Cases_on `phi.inst_outputs` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  drule_all current_phi_resolve_var >> strip_tac >> gvs[eval_operand_def] >>
  fs[current_origin_realizes_def] >>
  first_x_assum (qspec_then `src` mp_tac) >>
  Cases_on `ALOOKUP M src` >> simp[] >> strip_tac >>
  qexists `x` >> simp[current_phi_origin_read_def] >> metis_tac[]
QED

Theorem current_phi_origins_extract_list:
  !prefix. EVERY (\i. i.inst_opcode = PHI /\ inst_wf i) prefix /\
  st.vs_prev_bb = SOME prev /\ current_origin_realizes V M st /\
  EVERY IS_SOME (MAP (eval_one_phi st) prefix) ==>
  ?bindings. LIST_REL (current_phi_origin_read M prev) prefix bindings /\
    EVERY (\b. IS_SOME (V (SND b))) bindings /\
    MAP (THE o eval_one_phi st) prefix =
      MAP (\(dst,origin). (dst,THE (V origin))) bindings
Proof
  Induct >- simp[] >> rpt strip_tac >>
  fs[] >> Cases_on `eval_one_phi st h` >> fs[] >> PairCases_on `x` >>
  drule_all current_phi_origin_extract >> strip_tac >>
  qexists `(x0,origin)::bindings` >> simp[]
QED

Theorem current_phi_origin_writes_realize:
  !bindings st. current_origin_realizes V M st /\
    EVERY (\b. IS_SOME (V (SND b))) bindings ==>
    current_origin_realizes V (bindings ++ M)
      (FOLDR (\(dst,value) t. update_var dst value t) st
        (MAP (\(dst,origin). (dst,THE (V origin))) bindings))
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[] >> strip_tac >> irule current_origin_realizes_write >>
  first_x_assum drule_all >> Cases_on `V r` >> fs[]
QED

Theorem current_phi_writes_control:
  !writes. (FOLDR (\(out,value) t. update_var out value t) st writes).vs_current_bb = st.vs_current_bb /\
    (FOLDR (\(out,value) t. update_var out value t) st writes).vs_prev_bb = st.vs_prev_bb
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> fs[update_var_def]
QED

Theorem current_eval_phis_origin_batch:
  EVERY (\i. i.inst_opcode = PHI /\ inst_wf i) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  st.vs_prev_bb = SOME prev /\ current_origin_realizes V M st /\
  eval_phis st (prefix ++ suffix) = OK post ==>
  ?bindings. LIST_REL (current_phi_origin_read M prev) prefix bindings /\
    EVERY (\b. IS_SOME (V (SND b))) bindings /\
    current_origin_realizes V (bindings ++ M) post /\
    execution_frame post = execution_frame st /\
    post.vs_current_bb = st.vs_current_bb /\ post.vs_prev_bb = st.vs_prev_bb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `EVERY (\i. i.inst_opcode = PHI) prefix` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule current_eval_phis_batch >>
  disch_then (qspecl_then [`st`, `suffix`] mp_tac) >>
  impl_tac >- simp[] >>
  Cases_on `EVERY IS_SOME (MAP (eval_one_phi st) prefix)` >>
  asm_simp_tac std_ss [exec_result_11, exec_result_distinct] >>
  disch_then SUBST1_TAC >>
  pure_rewrite_tac[current_phi_writes_frame, current_phi_writes_control] >>
  drule_all current_phi_origins_extract_list >> strip_tac >>
  qexists `bindings` >> simp[] >>
  irule current_phi_origin_writes_realize >> simp[]
QED

(* Crossed reads use the immutable incoming map, not the preceding copy. *)
Theorem current_phi_origins_crossed_regression:
  LIST_REL
    (current_phi_origin_read
      [("x",(0,"entry",0,0)); ("y",(0,"entry",1,0))] "entry")
    [mk_inst 0 PHI [Label "entry"; Var "y"] ["x"];
     mk_inst 1 PHI [Label "entry"; Var "x"] ["y"]]
    [("x",(0,"entry",1,0)); ("y",(0,"entry",0,0))] /\
  ALOOKUP ([("x",(0,"entry",1,0)); ("y",(0,"entry",0,0))] ++
    [("x",(0,"entry",0,0)); ("y",(0,"entry",1,0))]) "y" =
    SOME (0,"entry",0,0)
Proof
  simp[current_phi_origin_read_def, mk_inst_def, resolve_phi_def]
QED

Theorem current_phi_origins_duplicate_regression:
  LIST_REL
    (current_phi_origin_read
      [("a",(0,"entry",0,0)); ("b",(0,"entry",1,0))] "entry")
    [mk_inst 0 PHI [Label "entry"; Var "a"] ["x"];
     mk_inst 1 PHI [Label "entry"; Var "b"] ["x"]]
    [("x",(0,"entry",0,0)); ("x",(0,"entry",1,0))] /\
  ALOOKUP ([("x",(0,"entry",0,0)); ("x",(0,"entry",1,0))] ++ M) "x" =
    SOME (0,"entry",0,0)
Proof
  simp[current_phi_origin_read_def, mk_inst_def, resolve_phi_def]
QED

Theorem current_phi_crossed_execution_regression:
  st.vs_prev_bb = SOME "entry" /\
  lookup_var "x" st = SOME 10w /\ lookup_var "y" st = SOME 20w ==>
  eval_phis st
    [mk_inst 0 PHI [Label "entry"; Var "y"] ["x"];
     mk_inst 1 PHI [Label "entry"; Var "x"] ["y"]] =
    OK (update_var "x" 20w (update_var "y" 10w st))
Proof
  simp[eval_phis_def, eval_one_phi_def, mk_inst_def, resolve_phi_def,
    eval_operand_def]
QED

Theorem current_phi_duplicate_execution_regression:
  st.vs_prev_bb = SOME "entry" /\
  lookup_var "a" st = SOME 10w /\ lookup_var "b" st = SOME 20w ==>
  eval_phis st
    [mk_inst 0 PHI [Label "entry"; Var "a"] ["x"];
     mk_inst 1 PHI [Label "entry"; Var "b"] ["x"]] =
    OK (update_var "x" 10w (update_var "x" 20w st)) /\
  lookup_var "x" (update_var "x" 10w (update_var "x" 20w st)) = SOME 10w
Proof
  simp[eval_phis_def, eval_one_phi_def, mk_inst_def, resolve_phi_def,
    eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
