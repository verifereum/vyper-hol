(* Operational input to the grouped nonpayable check's revert rule. *)
Theory groupedValueRejectSite
Ancestors
  compileVyper compileEnv venomInst venomState fragExec loweringStateRelDefs
  fragGasOriginPtr ptrDiscipline finite_map

Definition grouped_value_reject_site_def:
  grouped_value_reject_site unit vs <=>
    ?fn bb m opened checked t G tn.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME "__entry" /\
      lookup_block "__entry" fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0 /\
      compile_entry_checks m F opened = ((),checked) /\
      fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
      ~block_is_terminated opened /\ fresh_vars_wrt opened t /\
      ~t.vs_halted /\ t.vs_current_bb = opened.cs_current_bb /\
      t.vs_inst_idx = 0 /\ allocas_from 0 t /\
      (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t) /\
      t.vs_call_ctx.cc_callvalue <> 0w /\
      (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
         FEMPTY,entry_taint) [] (OK t,G,tn))
End

Theorem grouped_value_reject_site_at:
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\
  compile_entry_checks m F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\ fresh_vars_wrt opened t /\
  ~t.vs_halted /\ t.vs_current_bb = opened.cs_current_bb /\
  t.vs_inst_idx = 0 /\ allocas_from 0 t /\
  (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t) /\
  t.vs_call_ctx.cc_callvalue <> 0w /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK t,G,tn)) ==>
  grouped_value_reject_site unit vs
Proof
  strip_tac >> pure_rewrite_tac[grouped_value_reject_site_def] >>
  qexistsl_tac [`fn`,`bb`,`m`,`opened`,`checked`,`t`,`G`,`tn`] >> simp[]
QED
