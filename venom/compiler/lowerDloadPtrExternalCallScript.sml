Theory lowerDloadPtrExternalCall
Ancestors
  lowerDloadPtrCallBuffers lowerDloadPtrResidualInterfaces
  lowerDloadPtrStoreCommon lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrScalar
  lowerDloadPtrCall lowerDloadPtrBlockEntry lowerDloadPtrPhi
  ptrDiscipline venomExecSemantics venomCallOracleDefs venomState
  contextCodegenRel codegenRel memLocDefs finite_map pred_set list arithmetic

(* The call's local-frame footprint is independent of the oracle result. *)
Theorem dload_external_call_frame_fields:
  exec_ext_call i s gas addr value ao az ro rz st = OK s1 ==>
  s1.vs_fmp = s.vs_fmp /\ s1.vs_params = s.vs_params /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_call_ctx = s.vs_call_ctx /\
  (!v. ~MEM v i.inst_outputs ==> lookup_var v s1 = lookup_var v s)
Proof
  namedCases_on `i.inst_outputs` ["", "out outs"]
  >- simp[exec_ext_call_def] >>
  Cases_on `outs` >> simp[exec_ext_call_def, update_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem dload_external_call_ghosts:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp ==>
  step_prov PG G i s1 = set_prov G i.inst_outputs NONE /\
  step_taint i s s1 tn =
    <|t_mem := tn.t_mem DIFF
        {a | w2n ro <= a /\
             a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)};
      t_var := set_var_taint tn.t_var i.inst_outputs {};
      t_stor := if i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
                    s1.vs_requests <> s.vs_requests /\
                    s1.vs_outcomes <> s.vs_outcomes /\
                    (HD s.vs_outcomes).co_success then {} else tn.t_stor;
      t_trans := if i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
                    s1.vs_requests <> s.vs_requests /\
                    s1.vs_outcomes <> s.vs_outcomes /\
                    (HD s.vs_outcomes).co_success then {} else tn.t_trans;
      t_imm := tn.t_imm|>
Proof
  strip_tac >>
  `new_site_bytes s s1 = {}` by
    (gvs[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    (conj_tac >- (irule out_taint_opcode_exclusion >> simp[]) >>
     irule written_taint_opcode_exclusion >> simp[]) >>
  gvs[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
      step_writes_def, range_bytes_def, adopt_reset_def, store_taint_def,
      imm_taint_def]
QED

(* STATICCALL may consume an ordinary outcome, but never resets store taint.
   CALL's mode is the caller's static flag; both cases are covered here. *)
Theorem dload_external_call_adoption:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  (st <=> i.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  exec_ext_call i s gas addr value ao az ro rz st = OK s1 ==>
  ((i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
    s1.vs_requests <> s.vs_requests /\ s1.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success) <=>
   (~(st \/ s.vs_call_ctx.cc_static) /\
    ~computed_precompile (venom_call_request s addr value ao az st) /\
    s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n ro) (w2n rz) s` >>
  rename1 `consume_call_outcome _ _ _ s = (w,ss)` >>
  drule dload_consume_call_adopted >> strip_tac >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_ext_call_def] >> pure_asm_rewrite_tac[LET_THM] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >- simp[] >>
  Cases_on `outs` >> simp[] >> strip_tac >>
  qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
  gvs[update_var_def]
QED

Theorem dload_memory_match_taint_cong:
  tn.t_mem = sn.t_mem /\ un.t_mem = vn.t_mem ==>
  (dload_memory_match lo fs tn un s t <=>
   dload_memory_match lo fs sn vn s t)
Proof
  simp[dload_memory_match_def]
QED

Theorem dload_external_call_mem_ghost:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp ==>
  (step_taint i s s1 tn).t_mem = tn.t_mem DIFF
    {a | w2n ro <= a /\ a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_external_call_ghosts >> simp[]
QED

Theorem dload_external_call_memory:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  source_memory_write_ranges i t = [(w2n rt,w2n rz)] /\
  dload_memory_match lo fs tn un s t /\
  dload_live_layout lo sf tf fs /\ dload_value_word fs {} p q ro rt /\
  exec_ext_call i s gs addr value ao az ro rz st = OK s1 /\
  exec_ext_call i t gt addr value bo bz rt rz st = OK t1 /\
  s1.vs_returndata = t1.vs_returndata /\
  (w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n)) ==>
  dload_memory_match lo fs (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_exec_ext_call_memory_match >> strip_tac >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_fmp = s.vs_fmp /\
   t1.vs_allocas = t.vs_allocas /\ t1.vs_fmp = t.vs_fmp` by
    metis_tac[dload_ext_call_success_footprint, dload_external_call_frame_fields] >>
  `((step_taint i s s1 tn).t_mem =
      (tn with t_mem := tn.t_mem DIFF
        {a | w2n ro <= a /\ a < w2n ro + MIN (w2n rz) (LENGTH s1.vs_returndata)}).t_mem) /\
   ((step_taint i t t1 un).t_mem =
      (un with t_mem := un.t_mem DIFF
        {a | w2n rt <= a /\ a < w2n rt + MIN (w2n rz) (LENGTH s1.vs_returndata)}).t_mem)` by
    (conj_tac
     >- (qpat_x_assum `s1.vs_returndata = t1.vs_returndata` kall_tac >>
         simp[] >> irule dload_external_call_mem_ghost >> simp[]) >>
     qpat_x_assum `s1.vs_returndata = t1.vs_returndata` SUBST1_TAC >>
     simp[] >> irule dload_external_call_mem_ghost >> simp[]) >>
  metis_tac[dload_memory_match_taint_cong]
QED

Theorem dload_external_call_store_ghosts:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) ==>
  (step_taint i s s1 tn).t_stor =
    (if i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
        s1.vs_requests <> s.vs_requests /\ s1.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_stor) /\
  (step_taint i s s1 tn).t_trans =
    (if i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
        s1.vs_requests <> s.vs_requests /\ s1.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_trans) /\
  (step_taint i s s1 tn).t_imm = tn.t_imm
Proof
  strip_tac >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]
QED

Theorem dload_external_call_shared_store:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  (st <=> i.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n bz) t /\
  exec_ext_call i s gs addr value ao az ro rz st = OK s1 /\
  exec_ext_call i t gt addr value bo bz rt rz st = OK t1 /\
  ((~s.vs_call_ctx.cc_static /\ s1.vs_requests <> s.vs_requests /\
    s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~t.vs_call_ctx.cc_static /\ t1.vs_requests <> t.vs_requests /\
    t1.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success)) ==>
  dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `a = (i.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
    s1.vs_requests <> s.vs_requests /\ s1.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success)` >>
  `a <=> ~(st \/ s.vs_call_ctx.cc_static) /\
     ~computed_precompile (venom_call_request s addr value ao az st) /\
     s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success` by
    (unabbrev_all_tac >> irule dload_external_call_adoption >>
     metis_tac[]) >>
  `dload_shared_store
    (tn with <|t_stor := if a then {} else tn.t_stor;
               t_trans := if a then {} else tn.t_trans|>)
    (un with <|t_stor := if a then {} else un.t_stor;
               t_trans := if a then {} else un.t_trans|>) s1 t1` by
    (irule dload_exec_ext_call_shared_store >> metis_tac[]) >>
  gvs[dload_shared_store_def, dload_external_call_store_ghosts, Abbr `a`]
QED

(* Literal step_inst/exec_ext_call bridge.  Gas may differ between the runs. *)
Theorem dload_external_call_step:
  ((i.inst_opcode = CALL /\
    i.inst_operands = [gas;address;val;a;sz;r;rs] /\
    eval_operand val s = SOME value /\ eval_operand val t = SOME value /\
    (s.vs_call_ctx.cc_static ==> value = 0w) /\
    st = s.vs_call_ctx.cc_static) \/
   (i.inst_opcode = STATICCALL /\
    i.inst_operands = [gas;address;a;sz;r;rs] /\ value = 0w /\ st = T)) /\
  eval_operand gas s = SOME gs /\ eval_operand gas t = SOME gt /\
  eval_operand address s = SOME addr /\ eval_operand address t = SOME addr /\
  eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
  eval_operand sz s = SOME az /\ eval_operand sz t = SOME az /\
  eval_operand r s = SOME ro /\ eval_operand r t = SOME rt /\
  eval_operand rs s = SOME rz /\ eval_operand rs t = SOME rz /\
  dload_equal_environment s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n az) t /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    exec_ext_call i s gs addr value ao az ro rz st = OK s1 /\
    exec_ext_call i t gt addr value bo az rt rz st = OK t1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) /\
    ((~s.vs_call_ctx.cc_static /\ s1.vs_requests <> s.vs_requests /\
      s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
     (~t.vs_call_ctx.cc_static /\ t1.vs_requests <> t.vs_requests /\
      t1.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx] >>
  `step_inst fuel Cs i s = exec_ext_call i s gs addr value ao az ro rz st /\
   exec_ext_call i t gt addr value bo az rt rz st = OK t1` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[] >> fs[step_inst_non_invoke] >>
     qpat_x_assum `step_inst_base i t = OK t1` mp_tac >>
     pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.ISPECL [`ro:bytes32`,`gs:bytes32`]
    (Q.GENL [`rs`,`gs`] dload_exec_ext_call_environment)) >>
  disch_then (qspecl_then [`ro:bytes32`,`gs:bytes32`] strip_assume_tac) >>
  qexists `s1` >> simp[]
QED

Theorem dload_external_call_var_ghosts:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
   i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2 \/
   i.inst_opcode = DELEGATECALL) ==>
  step_prov PG G i s1 = set_prov G i.inst_outputs NONE /\
  (step_taint i s s1 tn).t_var = set_var_taint tn.t_var i.inst_outputs {}
Proof
  strip_tac >>
  `out_taint tn i s = {}` by
    (irule out_taint_opcode_exclusion >> simp[]) >>
  gvs[step_prov_def, out_prov_def, step_taint_def]
QED

Theorem dload_scalar_result_vars:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
   i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2 \/
   i.inst_opcode = DELEGATECALL) /\
  dload_vars_match fs V G H tn un s t /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (?out. i.inst_outputs = [out]) /\
  (!v. ~MEM v i.inst_outputs ==> lookup_var v s1 = lookup_var v s) /\
  (!v. ~MEM v i.inst_outputs ==> lookup_var v t1 = lookup_var v t) /\
  (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) ==>
  dload_vars_match fs V (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
  (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_prov PG G i s1 = set_prov G i.inst_outputs NONE /\
   (step_taint i s s1 tn).t_var = set_var_taint tn.t_var i.inst_outputs {}` by
    (irule dload_external_call_var_ghosts >> simp[]) >>
  `step_prov PH H i t1 = set_prov H i.inst_outputs NONE /\
   (step_taint i t t1 un).t_var = set_var_taint un.t_var i.inst_outputs {}` by
    (irule dload_external_call_var_ghosts >> simp[]) >>
  conj_tac
  >- (simp[dload_vars_match_def] >>
      gen_tac >> strip_tac >> Cases_on `MEM v i.inst_outputs`
      >- (gvs[] >> simp[set_var_taint_def, set_prov_def, op_taint_def,
               FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, dload_value_word_def,
               word_agree_except_def] >> rpt strip_tac >> gvs[]) >>
      `lookup_var v s1 = lookup_var v s /\ lookup_var v t1 = lookup_var v t` by
        metis_tac[] >>
      gvs[set_var_taint_def, set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
          op_taint_def, dload_vars_match_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `MEM v i.inst_outputs` >> metis_tac[]
QED

Theorem dload_external_call_vars:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  dload_vars_match fs V G H tn un s t /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  exec_ext_call i s gs addr value ao az ro rz st = OK s1 /\
  exec_ext_call i t gt addr value bo bz rt rz st = OK t1 /\
  (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) ==>
  dload_vars_match fs V (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
  (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?out. i.inst_outputs = [out]` by
    (namedCases_on `i.inst_outputs` ["", "out outs"]
     >- gvs[exec_ext_call_def] >>
     Cases_on `outs` >- metis_tac[] >> gvs[exec_ext_call_def]) >>
  irule dload_scalar_result_vars >>
  metis_tac[dload_external_call_frame_fields]
QED

Theorem dload_allocation_neutral_tables:
  dload_table_stack fs (s::ss) (t::ts) /\
  s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
  s1.vs_alloca_next = s.vs_alloca_next /\
  t1.vs_alloca_next = t.vs_alloca_next ==>
  dload_table_stack fs (s1::ss) (t1::ts)
Proof
  simp[dload_table_stack_def] >> strip_tac >> gen_tac >>
  Cases_on `k`
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]
QED

Theorem dload_external_call_boundary:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  (st <=> i.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
  source_memory_write_ranges i t = [(w2n rt,w2n rz)] /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_value_word fs {} p q ro rt /\
  (w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ p <> NONE) ==>
    ?b n. p = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n)) /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n bo) (w2n bz) t /\
  exec_ext_call i s gs addr value ao az ro rz st = OK s1 /\
  exec_ext_call i t gt addr value bo bz rt rz st = OK t1 /\
  dload_equal_environment s1 t1 /\
  (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) /\
  ((~s.vs_call_ctx.cc_static /\ s1.vs_requests <> s.vs_requests /\
    s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~t.vs_call_ctx.cc_static /\ t1.vs_requests <> t.vs_requests /\
    t1.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success)) ==>
  dload_boundary_core lo fs V Ws PG PH
    (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
  (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t /\
   dload_memory_match lo fs tn un s t /\
   dload_shared_store tn un s t /\ dload_equal_environment s t /\
   dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs` by
    metis_tac[dload_boundary_core_def] >>
  drule_all dload_external_call_vars >> strip_tac >>
  `s1.vs_returndata = t1.vs_returndata` by
    (qpat_x_assum `dload_equal_environment s1 t1` mp_tac >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `dload_memory_match lo fs (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (irule dload_external_call_memory >> metis_tac[]) >>
  `dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1` by
    (drule_all dload_external_call_shared_store >> simp[]) >>
  `s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
   s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
   s1.vs_params = s.vs_params /\ t1.vs_params = t.vs_params` by
    metis_tac[dload_ext_call_success_footprint, dload_external_call_frame_fields] >>
  simp[dload_boundary_core_def] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_boundary_core_def] >> strip_tac >>
  irule dload_allocation_neutral_tables >> metis_tac[]
QED


Theorem dload_external_call_write_range[local]:
  ((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;value;a;sz;r;rs]) \/
   (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;a;sz;r;rs])) /\
  eval_operand r s = SOME ro /\ eval_operand rs s = SOME rz /\
  (!op. MEM op i.inst_operands ==> eval_operand op s <> NONE) ==>
  source_memory_write_ranges i s = [(w2n ro,w2n rz)]
Proof
  strip_tac >> gvs[source_memory_write_ranges_def] >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr s` >> gvs[] >>
  Cases_on `eval_operand value s` >> gvs[] >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand sz s` >> gvs[]
QED


Theorem dload_boundary_core_external_call_shaped[local]:
  ((i.inst_opcode = CALL /\ i.inst_operands = [gas;address;value;a;sz;r;rs]) \/
   (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;address;a;sz;r;rs])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) (TL i.inst_operands) ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
    s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb /\
    s1.vs_prev_bb = s.vs_prev_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\ t1.vs_inst_idx = t.vs_inst_idx /\
    s1.vs_call_ctx = s.vs_call_ctx /\ t1.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_call_evaluated_inputs >> strip_tac >>
  `dload_equal_environment s t` by metis_tac[dload_boundary_core_def] >>
  `!op. MEM op i.inst_operands ==> eval_operand op t <> NONE` by
    (drule_at (Pat `step_inst _ _ _ _ = OK _`) dload_call_success_inputs >>
     (impl_tac >- metis_tac[]) >> simp[]) >>
  `?gs gt addr ao bo az ro rt rz.
    eval_operand gas s = SOME gs /\ eval_operand gas t = SOME gt /\
    eval_operand address s = SOME addr /\ eval_operand address t = SOME addr /\
    eval_operand a s = SOME ao /\ eval_operand a t = SOME bo /\
    eval_operand sz s = SOME az /\ eval_operand sz t = SOME az /\
    eval_operand r s = SOME ro /\ eval_operand r t = SOME rt /\
    eval_operand rs s = SOME rz /\ eval_operand rs t = SOME rz` by
    (Cases_on `eval_operand gas s` >> gvs[] >>
     Cases_on `eval_operand gas t` >> gvs[] >>
     Cases_on `eval_operand address s` >> gvs[] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand a t` >> gvs[] >>
     Cases_on `eval_operand sz s` >> gvs[] >>
     Cases_on `eval_operand r s` >> gvs[] >>
     Cases_on `eval_operand r t` >> gvs[] >>
     Cases_on `eval_operand rs s` >> gvs[] >> metis_tac[]) >>
  `?vv st.
    ((i.inst_opcode = CALL /\
      i.inst_operands = [gas;address;value;a;sz;r;rs] /\
      eval_operand value s = SOME vv /\ eval_operand value t = SOME vv /\
      (s.vs_call_ctx.cc_static ==> vv = 0w) /\ st = s.vs_call_ctx.cc_static) \/
     (i.inst_opcode = STATICCALL /\
      i.inst_operands = [gas;address;a;sz;r;rs] /\ vv = 0w /\ st = T))` by
    (Cases_on `i.inst_opcode = CALL` >> gvs[] >>
     Cases_on `eval_operand value s` >> gvs[] >> metis_tac[]) >>
  `?s1. step_inst fuel Cs i s = OK s1 /\
    exec_ext_call i s gs addr vv ao az ro rz st = OK s1 /\
    exec_ext_call i t gt addr vv bo az rt rz st = OK t1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1) /\
    ((~s.vs_call_ctx.cc_static /\ s1.vs_requests <> s.vs_requests /\
      s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
     (~t.vs_call_ctx.cc_static /\ t1.vs_requests <> t.vs_requests /\
      t1.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))` by
    (irule (Q.INST [`value` |-> `vv`] dload_external_call_step) >>
     simp[] >> metis_tac[]) >>
  `source_memory_write_ranges i s = [(w2n ro,w2n rz)] /\
   source_memory_write_ranges i t = [(w2n rt,w2n rz)]` by
    (conj_tac >> irule dload_external_call_write_range >> metis_tac[]) >>
  `dload_value_word fs {} (op_prov G r) (op_prov H r) ro rt` by
    (first_x_assum irule >> simp[]) >>
  `(w2n rz <> 0 ==> ((lo < w2n ro + w2n rz \/ op_prov G r <> NONE) ==>
    ?b n. op_prov G r = SOME (b,n) /\ b <= w2n ro /\ w2n ro + w2n rz <= b+n))` by
    (`?ops. mem_write_ops i = SOME ops /\ ops.iao_ofst = r` by
       (gvs[mem_write_ops_def] >> metis_tac[]) >>
     `MEM (w2n ro,w2n rz) (source_memory_write_ranges i s)` by simp[] >>
     qpat_assum `ops.iao_ofst = r` (SUBST1_TAC o SYM) >>
     rpt strip_tac >> irule dload_write_access_containment >> simp[] >>
     metis_tac[]) >>
  `dload_boundary_core lo fs V Ws PG PH
    (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
   (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE))` by
    (gvs[wordsTheory.w2n_eq_0] >>
     irule (Q.INST_TYPE [`:'a` |-> `:256`, `:'b` |-> `:bytes32`,
                        `:'c` |-> `:bytes32`] dload_external_call_boundary) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists `s1` >> simp[] >>
  qpat_x_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `exec_ext_call _ t _ _ _ _ _ _ _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  disch_then (fn th =>
    mp_then Any strip_assume_tac dload_ext_call_success_footprint th >>
    mp_then Any strip_assume_tac dload_external_call_frame_fields th) >>
  disch_then (fn th =>
    mp_then Any strip_assume_tac dload_ext_call_success_footprint th >>
    mp_then Any strip_assume_tac dload_external_call_frame_fields th) >>
  simp[]
QED

Theorem dload_boundary_core_external_call:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) (TL i.inst_operands) ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\ t1.vs_alloca_next = t.vs_alloca_next /\
    s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb /\
    s1.vs_prev_bb = s.vs_prev_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\ t1.vs_inst_idx = t.vs_inst_idx /\
    s1.vs_call_ctx = s.vs_call_ctx /\ t1.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?gas address value a sz r rs.
    ((i.inst_opcode = CALL /\ i.inst_operands = [gas;address;value;a;sz;r;rs]) \/
     (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;address;a;sz;r;rs]))` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `step_inst fuel Ct i t = OK t1` mp_tac >>
     simp[step_inst_non_invoke] >>
     pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
     Cases_on `i.inst_operands` >> simp[] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  irule dload_boundary_core_external_call_shaped >> metis_tac[]
QED

val _ = List.app (fn (n,th) =>
  if null (hyp th) then print (n ^ ": closed\n")
  else raise Fail (n ^ ": nonempty hypotheses"))
  [("frame_fields",dload_external_call_frame_fields),
   ("ghosts",dload_external_call_ghosts),
   ("adoption",dload_external_call_adoption),
   ("memory_cong",dload_memory_match_taint_cong),
   ("memory_ghost",dload_external_call_mem_ghost),
   ("memory",dload_external_call_memory),
   ("store_ghosts",dload_external_call_store_ghosts),
   ("store",dload_external_call_shared_store),
   ("var_ghosts",dload_external_call_var_ghosts),
   ("vars",dload_external_call_vars),
   ("tables",dload_allocation_neutral_tables),
   ("scalar_vars",dload_scalar_result_vars),
   ("write_range",dload_external_call_write_range),
   ("inputs",dload_call_evaluated_inputs),
   ("environment",dload_exec_ext_call_environment),
   ("bridge",dload_external_call_step),
   ("boundary",dload_external_call_boundary),
   ("shaped",dload_boundary_core_external_call_shaped),
   ("external_call",dload_boundary_core_external_call)];
