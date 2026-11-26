(* Preserve a selected callee request when attaching its caller prefix. *)
Theory s1PrefixBoolChainInvokeSite
Ancestors
  s1PrefixDefs s1PrefixCompose s1PrefixIntCallReturnPrefix fragGasFocus fragGasOriginPtr

Theorem bool_chain_request_site_through_invoke:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
    marks (OK t,G1,tn1) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  ptr_inst_ok D lo 0 ctx func G1 tn1 inst t /\
  request_site (D,lo,explicit,ctx,callee,MAP (op_prov G1) arg_ops)
    cx H (entered,FEMPTY,tn1 with t_var := FEMPTY) k rq outcome ==>
  request_site (D,lo,explicit,ctx,func,PG) cx H (s,G,tn) k rq outcome
Proof
  strip_tac >>
  drule request_site_prepend_path >> disch_then irule >>
  qhdtm_x_assum `request_site` (strip_assume_tac o REWRITE_RULE [request_site_def]) >>
  rewrite_tac[request_site_def] >>
  rename1 `gas_origin_ptr_focus _ _ left (leaf,leafPG,leafG,leafTn,stop)` >>
  rename1 `step_inst fuel ctx site_inst stop = OK next` >>
  qexistsl_tac [`left`,`leaf`,`leafPG`,`leafG`,`leafTn`,`stop`,
    `site_inst`,`fuel`,`next`] >>
  simp[] >> irule intcall_invoke_focus >>
  qhdtm_assum `gas_origin_ptr_focus` (irule_at Any) >> simp[]
QED
