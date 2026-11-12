Theory ctorDeployLoweringEntryRegisterSizes
Ancestors
  ctorDeployLoweringEntryCompleteRegister entryArgPtrs localPtrsProps
  exprLoweringProps compileEnv venomState venomInst finite_map words

Theorem deploy_ctor_literal_sizes_frame:
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
  t.vs_allocas = s.vs_allocas ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  metis_tac[]
QED

Theorem deploy_ctor_literal_sizes_update:
  fn_inst_ids_distinct func /\ MEM site (fn_insts func) /\
  site.inst_operands = [Lit (n2w cap)] /\ cap < dimword (:256) /\
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
  t.vs_allocas = s.vs_allocas |+ (site.inst_id,(off,cap)) ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  rpt strip_tac >> Cases_on `inst.inst_id = site.inst_id`
  >- (`inst = site` by metis_tac[fn_inst_ids_distinct_inj] >>
      gvs[FLOOKUP_UPDATE, w2n_n2w]) >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem deploy_ctor_register_alloc_literal_sizes:
  compile_alloc_buffer cap st = (buf,sa) /\ fn_has_code st sa func /\
  fn_inst_ids_distinct func /\ cap < dimword (:256) /\
  (!inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
  a.vs_allocas = initial.vs_allocas |+
    (st.cs_next_id,(initial.vs_alloca_next,cap)) ==>
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP a.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n
Proof
  strip_tac >> drule_all entry_alloc_buffer_inst >> strip_tac >>
  rpt strip_tac >>
  Cases_on `inst.inst_id = st.cs_next_id`
  >- (`inst = mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)]
        [STRING #"%" (toString st.cs_next_var)]` by
        (irule fn_inst_ids_distinct_inj >>
         conj_tac >- simp[mk_inst_def] >>
         qexists `func` >> asm_rewrite_tac[]) >>
      gvs[FLOOKUP_UPDATE, mk_inst_def, w2n_n2w]) >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED
