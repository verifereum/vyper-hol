(* Scratch credit comes from an actual literal ALLOCA of the function.
   Revisited sites use the size consistency clause, not an ID interval. *)
Theory tupleAssignImmutableDeployActualSite
Ancestors
  allocaFootprint abiCallerAllocation abiBuiltinEncodeStagedEffect
  exprLoweringProps localPtrsProps allocaHistory abiBuiltinAllocation
  venomState venomInst venomMemDefs allocaFrontierBound allocaBudgetProps
  venomInstIdsProps vyperCompiler
  finite_map list words arithmetic

Theorem tuple_immutable_actual_scratch_step:
  !ctx func start buf finish s.
    compile_alloc_buffer 32 start = (buf,finish) /\
    MEM (mk_inst start.cs_next_id ALLOCA [Lit (n2w 32)]
      [STRING #"%" (toString start.cs_next_var)]) (fn_insts func) /\
    fresh_vars_wrt start s /\ alloca_inv s /\ alloca_room ctx func s /\
    (!inst n base sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
    ?p t.
      run_inst_seq (emitted_insts start finish) s = OK t /\
      eval_operand buf.buf_operand t = SOME (n2w p) /\
      FLOOKUP t.vs_allocas start.cs_next_id = SOME (p,32) /\
      p + 32 <= t.vs_alloca_next /\ t.vs_alloca_next < dimword (:256) /\
      alloca_inv t /\ alloca_room ctx func t /\
      fresh_vars_wrt finish t /\ t.vs_memory = s.vs_memory /\
      (!id off sz. id <> start.cs_next_id /\
        FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
        FLOOKUP t.vs_allocas id = SOME (off,sz) /\
        (off + sz <= p \/ p + 32 <= off)) /\
      (fn_inst_ids_distinct func ==>
        !inst n base sz.
          MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          inst.inst_operands = [Lit n] /\
          FLOOKUP t.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n)
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `?p. FLOOKUP (abi_builtin_allocate_state start.cs_next_id 32 s).vs_allocas
      start.cs_next_id = SOME (p,32)` by
    (Cases_on `FLOOKUP s.vs_allocas start.cs_next_id`
     >- simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
     PairCases_on `x` >>
     `x1 = 32` by
       (qpat_x_assum `!inst n base sz. _` drule >> simp[mk_inst_def]) >>
     gvs[abi_builtin_allocate_state_def]) >>
  drule compile_alloc_buffer_mem_ok >>
  disch_then (qspecl_then [`s`,`p`] mp_tac) >>
  impl_tac >- gvs[alloca_inv_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK t` >>
  `alloca_inv t` by (irule history_base_alloca_inv >> metis_tac[]) >>
  `alloca_room ctx func t` by
    (Cases_on `FLOOKUP s.vs_allocas start.cs_next_id = NONE`
     >- (drule alloca_room_fresh >>
         disch_then (qspec_then
           `mk_inst start.cs_next_id ALLOCA [Lit (n2w 32)]
             [STRING #"%" (toString start.cs_next_var)]` mp_tac) >>
         `start.cs_next_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
         simp[mk_inst_def] >> strip_tac >>
         gvs[Abbr `t`, abi_builtin_allocate_state_def] >>
         irule alloca_room_fields >> goal_assum (drule_at Any) >> simp[]) >>
     irule alloca_room_fields >> qexists `s` >>
     simp[Abbr `t`, abi_builtin_allocate_state_def]) >>
  qexistsl [`p`,`t`] >>
  simp[run_inst_seq_def, Abbr `t`, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- metis_tac[alloca_room_next_lt, update_var_fields] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP (abi_builtin_allocate_state start.cs_next_id 32 s).vs_allocas id =
        SOME (off,sz)` by metis_tac[abi_builtin_allocate_state_outside] >>
      simp[] >>
      `alloca_inv (abi_builtin_allocate_state start.cs_next_id 32 s)` by
        (irule alloca_inv_fields >> goal_assum (drule_at Any) >> simp[]) >>
      metis_tac[abi_caller_allocation_separate]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id = start.cs_next_id`
  >- (`inst = mk_inst start.cs_next_id ALLOCA [Lit (n2w 32)]
          [STRING #"%" (toString start.cs_next_var)]` by
        (irule fn_inst_ids_distinct_inj >> simp[mk_inst_def] >>
         qexists `func` >> fs[mk_inst_def]) >>
      gvs[mk_inst_def]) >>
  rename1 `FLOOKUP _ inst.inst_id = SOME (off,sz)` >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (off,sz)` by
    metis_tac[abi_builtin_allocate_state_outside] >>
  metis_tac[]
QED

(* Exact charge conservation, including returning INVOKEs. The two existing
   sums differ only in the names of their identical literal-size functions. *)
Theorem tuple_immutable_actual_site_charge:
  !fuel ctx func inst s t.
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    step_inst fuel ctx inst s = OK t ==>
    t.vs_alloca_next + pending_alloca_size func t =
    s.vs_alloca_next + pending_alloca_size func s
Proof
  rpt strip_tac >>
  `alloca_lit_size = alloca_size` by
    simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def] >>
  simp[pending_alloca_size_def] >>
  rewrite_tac[GSYM remaining_alloca_budget_def] >>
  metis_tac[step_inst_alloca_budget, fn_inst_ids_distinct_all_distinct, ADD_COMM]
QED
