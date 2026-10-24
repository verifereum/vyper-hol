(* TOP-LEVEL: dispatch_precompiles_supply, projecting existing account-frame preservation.
 *)
Theory vyperPrecompileSupply
Ancestors
  vyperExecutionSupply vfmStaticCalls vfmExecution vfmContext list

(* Reuse Verifereum's precompile frame theorem for every result, including
   exceptional halts; account and saved rollback maps are unchanged. *)
Theorem cp_execution_supply:
  cp action /\ execution_supply_bound budget st /\ st.contexts <> [] /\
  action st = (result,post) ==>
  execution_supply_bound budget post
Proof
  simp[cp_def] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `result`, `post`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `st.contexts` >> gvs[execution_supply_bound_def]
QED

Theorem cp_execution_supply_snd:
  cp action /\ execution_supply_bound budget st /\ st.contexts <> [] ==>
  execution_supply_bound budget (SND (action st))
Proof
  strip_tac >> Cases_on `action st` >>
  rename1 `action st = (result,post)` >> simp[] >>
  irule cp_execution_supply >>
  qexistsl_tac [`action`, `result`, `st`] >> simp[]
QED

Theorem dispatch_precompiles_supply:
  execution_supply_bound budget st /\ st.contexts <> [] ==>
  execution_supply_bound budget (SND (dispatch_precompiles address st))
Proof
  strip_tac >> irule cp_execution_supply_snd >> simp[]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperPrecompileSupply");
