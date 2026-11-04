(* Replay-safe allocation boundaries for forcing deferred arguments. *)
Theory bodyIntCallForceFrame
Ancestors
  list finite_map words arithmetic exprLoweringProps localPtrsProps
  exprSimOperands loweringHalt fragExec compileEnv context venomExecSemantics
  venomMemDefs venomState venomInst

(* Both fresh execution and replay return the region of the requested size.
   The size agreement in stmt_state_rel is essential in the replay branch. *)
Theorem force_alloca_region:
  !ctx func cenv cx es s inst q n.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit (n2w n)] /\ inst.inst_outputs = [q] /\
    n < dimword (:256) ==>
    ?s' b. exec_alloca inst s (n2w n : bytes32) = OK s' /\
      lookup_var q s' = SOME (n2w b) /\
      FLOOKUP s'.vs_allocas inst.inst_id = SOME (b,n) /\
      b + n < dimword (:256) /\
      s.vs_alloca_next <= s'.vs_alloca_next /\
      s'.vs_memory = s.vs_memory /\
      (!r. r <> q ==> lookup_var r s' = lookup_var r s) /\
      (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
         FLOOKUP s'.vs_allocas aid = SOME (p,sz))
Proof
  rpt strip_tac >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (`alloca_room ctx func s` by fs[stmt_state_rel_def] >>
      `inst.inst_id NOTIN FDOM s.vs_allocas` by gvs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      simp[exec_alloca_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[FLOOKUP_DEF] >>
      metis_tac[ADD_COMM]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME pr` >>
  PairCases_on `pr` >>
  `pr1 = n` by
    (fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `pr0 + n <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[ADD_COMM]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  simp[exec_alloca_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  decide_tac
QED

(* Separation is valid after either execution branch, not just after a fresh
   bump.  Distinct instruction identities exclude local backing on replay. *)
Theorem force_alloca_frame:
  !func cenv scopes s s' inst q n b.
    exec_alloca inst s (n2w n : bytes32) = OK s' /\
    alloca_inv s /\ local_ptrs_rel func cenv scopes s /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q /\
    FLOOKUP s'.vs_allocas inst.inst_id = SOME (b,n) ==>
    alloca_inv s' /\ local_ptrs_rel func cenv scopes s' /\
    (!name lo sz. local_region cenv scopes s' name lo sz ==>
       regions_disjoint b n lo sz) /\
    (!aid p sz. aid <> inst.inst_id /\
       FLOOKUP s'.vs_allocas aid = SOME (p,sz) ==>
       regions_disjoint b n p sz)
Proof
  rpt strip_tac
  >- metis_tac[alloca_inv_exec_alloca]
  >- metis_tac[local_ptrs_rel_exec_alloca]
  >- (irule local_ptrs_rel_alloca_disjoint >>
      qexistsl_tac [`cenv`, `func`, `inst`, `name`, `q`, `scopes`, `s'`] >>
      metis_tac[alloca_inv_exec_alloca, local_ptrs_rel_exec_alloca]) >>
  `alloca_inv s'` by metis_tac[alloca_inv_exec_alloca] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, compileEnvTheory.regions_disjoint_def] >>
  metis_tac[]
QED

Theorem compile_alloc_buffer_member:
  !n sm buf sb func.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func ==>
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum drule >>
  gvs[get_instruction_def] >> metis_tac[MEM_EL]
QED

Theorem compile_alloc_buffer_step:
  !ctx func cenv cx es s n sm buf sb.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    n < dimword (:256) ==>
    ?s' b. step_inst_base
      (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sm.cs_next_var)]) s = OK s' /\
      eval_operand buf.buf_operand s' = SOME (n2w b) /\
      FLOOKUP s'.vs_allocas sm.cs_next_id = SOME (b,n) /\
      b + n < dimword (:256) /\
      alloca_inv s' /\ local_ptrs_rel func cenv es.scopes s' /\
      s.vs_alloca_next <= s'.vs_alloca_next /\ s'.vs_memory = s.vs_memory /\
      (!r. not_fresh_at sm r ==> lookup_var r s' = lookup_var r s) /\
      (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
        FLOOKUP s'.vs_allocas aid = SOME (p,sz)) /\
      (!name lo sz. local_region cenv es.scopes s' name lo sz ==>
        regions_disjoint b n lo sz) /\
      (!aid p sz. aid < sm.cs_next_id /\
        FLOOKUP s'.vs_allocas aid = SOME (p,sz) ==>
        regions_disjoint b n p sz)
Proof
  rpt strip_tac >>
  drule_all compile_alloc_buffer_member >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `~not_fresh_at sm (STRING #"%" (toString sm.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sm.cs_next_var))` by
    metis_tac[fresh_not_local_ptr] >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
   inst.inst_outputs = [STRING #"%" (toString sm.cs_next_var)]` by
    simp[Abbr `inst`, mk_inst_def] >>
  drule_all force_alloca_region >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all force_alloca_frame >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  qexistsl_tac [`s'`, `b`] >>
  fs[step_inst_base_def, Abbr `inst`, mk_inst_def, eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- metis_tac[] >>
  rpt strip_tac >>
  `aid <> sm.cs_next_id` by decide_tac >> metis_tac[]
QED

(* A fixed-start fragment contract keeps the function witnessing code
   membership explicit.  In particular, frag_exec's hidden function is not
   used as a substitute for the function in stmt_state_rel. *)
Theorem compile_alloc_buffer_replay_frag:
  !ctx func cenv cx es s0 n sm buf sb R.
    compile_alloc_buffer n sm = (buf,sb) /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
    n < dimword (:256) ==>
    frag_exec ctx sm sb (\s. s = s0)
      (\s. ?b. eval_operand buf.buf_operand s = SOME (n2w b) /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,n) /\
        b + n < dimword (:256) /\
        alloca_inv s /\ local_ptrs_rel func cenv es.scopes s /\
        s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_memory = s0.vs_memory /\
        (!r. not_fresh_at sm r ==> lookup_var r s = lookup_var r s0) /\
        (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) ==>
          FLOOKUP s.vs_allocas aid = SOME (p,sz)) /\
        (!name lo sz. local_region cenv es.scopes s name lo sz ==>
          regions_disjoint b n lo sz) /\
        (!aid p sz. aid < sm.cs_next_id /\
          FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
          regions_disjoint b n p sz)) R
Proof
  rpt strip_tac >> irule compile_alloc_buffer_frag >>
  qexistsl_tac [`buf`, `n`] >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all compile_alloc_buffer_step >> strip_tac >>
  qexists_tac `s'` >> simp[] >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  fs[eval_operand_def, lookup_var_def, local_ptrs_rel_inst_idx] >>
  conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s'` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name lo sz. local_region _ _ s' name lo sz ==> _` irule >>
      gvs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED
