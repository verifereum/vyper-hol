Theory bodyPtrPopContextExclusion
Ancestors bodyPtrPopEntryInterface bodyPtrPopGuardedWindow
  venomExecProps venomInst compileEnv list

Theorem pop_clean_context_storage_exclusion:
  EVERY (\f. EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) f.fn_blocks)
    ctx.ctx_functions /\
  stmt_state_rel ctx fn ce cx es s /\
  compile_dynarray_pop (Var h) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code si sb fn ==> F
Proof
  rpt strip_tac >> drule pop_entry_function_lookup >> strip_tac >>
  drule venomInstTheory.lookup_function_MEM >> strip_tac >>
  drule_all pop_storage_guarded_fn_window >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[]
QED
