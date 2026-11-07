(* Separation interface for a generated aggregate buffer and its used prefix. *)
Theory exprSimAggregateBodyAlloc
Ancestors
  exprSimAlloc exprLoweringProps compileEnv fragExec venomInst
  vyperState valueEncoding

Theorem aggregate_body_alloc_immutable_prefix:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\ used <= sz ==>
  ce.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b used
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac >>
  `regions_disjoint io (type_memory_size itv) b sz` by
    (first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[mk_inst_def]) >>
  fs[regions_disjoint_def] >> decide_tac
QED
