(* Pointwise branch entry, retaining one correlated source/frame witness. *)
Theory gasFocusLowerDloadControlEntry
Ancestors
  gasFocusLowerDloadControlEntryExact
Libs lowerDloadReturnPackageLib

Theorem ld_focus_control_entry:
  o1_ctx_shape C /\
  (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
   code_layout_valid vs0) /\
  reserved_intervals_wf C.ctx_global_reserved /\ fixed_region_reserved lo C /\
  taint_ok fn tn inst s /\ fmp_free_ctx C /\
  raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s /\
  mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn) /\
  (!f. MEM f C.ctx_functions ==> ir_supply_covers_fn (Sigma f.fn_name) f) /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f A A (f::fs) /\
  fn' = ld_image f /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C' inst t = OK q /\ ~q.vs_halted /\
  enters_block fn' q t1 /\ active_inst fn' ti t1 /\
  s.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs) ==>
  ?lbl H' G' ni s1 g X.
    q = jump_to lbl t /\ step_inst fuel C inst s = OK (jump_to lbl s) /\
    enters_block fn (jump_to lbl s) s1 /\
    g = f with <|lf_src := s1; lf_tgt := t1; lf_H := H';
      lf_tv := (entry_taint_vars fn (jump_to lbl s) tn).t_var|> /\
    ld_sync lo P C vs0 stk PG G'
      (entry_taint_vars fn (jump_to lbl s) tn) fn ni s1 t1 A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs f A A (g::fs) /\
    fn' = ld_image g /\
    ld_envelope g.lf_supply fn s1 s1.vs_inst_idx X t1.vs_inst_idx /\
    ld_prefix C' fn' X t1.vs_inst_idx 0 t1 t1 /\ ti = EL 0 X /\
    s1.vs_gas_readings = t1.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (g::fs)
Proof
  strip_tac >> drule_all ld_focus_control_entry_exact >> strip_tac >>
  qexistsl_tac [`lbl`,`H'`,`entry_prov fn (jump_to lbl s) G`,`ni`,`s1`,`g`,`X`] >>
  asm_rewrite_tac[]
QED
