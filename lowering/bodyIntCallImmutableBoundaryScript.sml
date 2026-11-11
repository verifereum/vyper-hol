(* Constructor immutable regions are below the allocation frontier and
   disjoint from recorded allocations and live locals.  This interface makes
   no assumption about the length of the lazily extended target memory. *)
Theory bodyIntCallImmutableBoundary
Ancestors
  exprLoweringProps compileEnv vyperState vyperAST venomState

Theorem initialized_immutable_regions:
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms) name =
    SOME (tv,v) ==>
  off + type_memory_size tv <= s.vs_alloca_next /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    regions_disjoint off (type_memory_size tv) b sz) /\
  (!id b sz. local_region cenv es.scopes s id b sz ==>
    regions_disjoint off (type_memory_size tv) b sz)
Proof
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >>
  rpt strip_tac >> res_tac
QED
