(* Consumer boundary for the immutable branch of the held pure-memory frame.
   Its frame premise is exactly the second conjunct of that interface. *)
Theory exprExtRequestImmutableFrame
Ancestors
  exprLoweringProps valueEncodingProofs

Theorem extrequest_immutable_memory_kept:
  immutable_alloca_sep func cenv cx ee s /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
    SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
             NONE => FEMPTY
           | SOME imms => get_source_immutables cenv.ce_module imms)
    name = SOME (tv,v) /\
  (!base len.
     (!inst b sz.
        MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sa.cs_next_id <= inst.inst_id /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint base len b sz) ==>
     mem_bytes_at base len s.vs_memory =
       mem_bytes_at base len s0.vs_memory) ==>
  mem_bytes_at off (type_memory_size tv) s.vs_memory =
    mem_bytes_at off (type_memory_size tv) s0.vs_memory
Proof
  strip_tac >> first_x_assum irule >>
  gvs[immutable_alloca_sep_def] >> metis_tac[]
QED
