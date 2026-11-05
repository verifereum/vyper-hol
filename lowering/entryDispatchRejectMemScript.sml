Theory entryDispatchRejectMem
Ancestors
  entryDispatchMem entryValueCheckMem moduleLoweringProps emitHelperProps compileEnv

Theorem linear_dispatch_value_reject_mem_safe:
  compile_selector_dispatch_linear sels fallback sf = ((),sd) /\
  compile_entry_checks mc F sc = ((),sk) /\
  fn_has_code sf sd fn /\ fn_has_code sc sk fn /\ cs_extends sd sc /\
  sd.cs_next_var <= sc.cs_next_var /\
  sf.cs_current_insts = [] /\ sc.cs_current_insts = [] /\
  EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  fresh_vars_wrt sf ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = sf.cs_current_bb /\ ss.vs_inst_idx = 0 /\
  ss.vs_call_ctx.cc_callvalue <> 0w /\
  linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback = sc.cs_current_bb ==>
  !fuel. mem_safe_blocks fuel ctx fn ss
Proof
  strip_tac >>
  `!t. vars_pc_only ss t /\ fresh_vars_wrt sd t /\
       (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x ss) /\
       ~t.vs_halted /\
       t.vs_current_bb = linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback /\
       t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t` by
    (rpt strip_tac >> drule vars_pc_only_fields >> strip_tac >>
     `fresh_vars_wrt sc t` by
       (irule fresh_vars_wrt_mono >> qexists_tac `sd` >> simp[]) >>
     irule entry_checks_value_revert_mem_safe_blocks >> simp[] >>
     qexistsl_tac [`mc`, `sc`, `sk`] >> simp[]) >>
  `ss.vs_inst_idx = LENGTH sf.cs_current_insts` by simp[] >>
  drule_all compile_selector_dispatch_linear_mem_safe >> simp[]
QED
