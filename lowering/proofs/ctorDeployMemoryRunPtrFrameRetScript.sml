(* The constructor's exit block with the pointer ghost: from the exit
 * label's start with deploy_ptr_inv, the optional unlock and the epilogue
 * (an ALLOCA at the frontier, an MCOPY of the immutables region from its
 * literal base past the runtime size, a CODECOPY of the runtime code, and
 * the RETURN) run pointer-safely to a halt.  The returned bytes are tainted
 * only where the region was, past the runtime code, which deploy_dead's
 * d_ret marks dead.  Every return from the constructor body and its
 * fall-through end here.
 * TOP-LEVEL: constructor_exit_run_ptr.
 *)
Theory ctorDeployMemoryRunPtrFrameRet
Ancestors
  ctorDeployMemoryRunPtrDefs ctorDeployLoweringDefs ctorDeployDefs ptrSafeRun
  ptrDiscipline stmtSimDefs bodySim moduleLowering ctorReturnFrame
  immutableDeployExecution nonreentrantSource loweringHalt allocaSiteResource
  exprLoweringProps fragExec compileEnv loweringStateRelDefs emitHelper e2eDeployDefs
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel memLocDefs
  valueEncoding valueEncodingDefs
  vyperStorageLayoutSafety vyperContext vyperState

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

(* Rewrite step_inst_base of the instruction an assumption gives opcode opc. *)
fun opc_tac opc =
  FIRST_ASSUM (fn th => rewrite_tac [MATCH_MP (opcode_eq opc) th]);

Theorem storage_dead_in_deploy[local]:
  !cx d tr st j b.
    storage_dead (cx with in_deploy := d) tr st j b <=> storage_dead cx tr st j b
Proof
  rpt gen_tac >>
  `!mid n subs. declared_storage_region (cx with in_deploy := d) mid n subs =
                declared_storage_region cx mid n subs` by
    simp[declared_storage_region_def, get_module_code_def, get_tenv_def,
         lookup_var_slot_from_layout_def] >>
  simp[storage_dead_def]
QED

(* The epilogue's ALLOCA: its site starts at or past lo, and the bytes it
   allocates afresh lie in it. *)
Theorem epilogue_alloca_step[local]:
  !ctx func cenv cx es u inst N buf lo.
    stmt_state_rel ctx func cenv cx es u /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w N)] /\
    inst.inst_outputs = [buf] /\ N < dimword(:256) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next ==>
    ?t b A nx.
      step_inst_base inst u = OK t /\
      t = update_var buf (n2w b)
            (u with <| vs_allocas := A; vs_alloca_next := nx |>) /\
      FLOOKUP A inst.inst_id = SOME (b, N) /\
      lo <= b /\ b + N < dimword(:256) /\ allocas_from lo t /\
      new_site_bytes u t SUBSET {i | b <= i /\ i < b + N}
Proof
  rpt strip_tac >>
  `alloca_room ctx func u /\ alloca_inv u` by fs[stmt_state_rel_def] >>
  `!b sz. FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = w2n (n2w N : bytes32)` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> strip_tac >>
     qpat_x_assum `!inst n base sz. _` drule >>
     disch_then (qspecl_then [`n2w N`, `b`, `sz`] mp_tac) >>
     simp[]) >>
  drule_all alloca_site_execute >> strip_tac >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (n2w N : bytes32) = N` by simp[] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `step_inst_base inst u = OK t` by
    (opc_tac ``ALLOCA`` >> asm_rewrite_tac [] >> simp[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac >>
  rpt (qpat_x_assum `alloca_room _ _ _` kall_tac) >>
  rpt (qpat_x_assum `alloca_inv _` kall_tac) >>
  qpat_x_assum `MEM _ _` kall_tac >>
  `b + N < dimword(:256)` by decide_tac >>
  qexistsl_tac [`t`, `b`, `t.vs_allocas`, `t.vs_alloca_next`] >>
  asm_rewrite_tac [] >>
  qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
  asm_rewrite_tac [exec_alloca_def] >>
  Cases_on `FLOOKUP u.vs_allocas inst.inst_id` >> asm_rewrite_tac []
  >- (simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
      `b = u.vs_alloca_next` by
        (qpat_x_assum `FLOOKUP t.vs_allocas _ = _` mp_tac >>
         qpat_x_assum `_ = t` (fn th => rewrite_tac [GSYM th]) >>
         simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
      qpat_x_assum `_ = t` (assume_tac o SYM) >>
      rpt conj_tac
      >- (qpat_x_assum `t = _` (fn th => rewrite_tac [th]) >>
          simp[update_var_def, venom_state_component_equality])
      >- simp[]
      >- (qpat_x_assum `t = _` (fn th => rewrite_tac [th]) >>
          simp[allocas_from_def, update_var_def,
               finite_mapTheory.FLOOKUP_UPDATE] >>
          rw[] >> fs[allocas_from_def] >> metis_tac[]) >>
      qpat_x_assum `t = _` (fn th => rewrite_tac [th]) >>
      simp[new_site_bytes_def, pred_setTheory.SUBSET_DEF, update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[] >> gvs[finite_mapTheory.flookup_thm, AllCaseEqs()]) >>
  rename1 `FLOOKUP u.vs_allocas inst.inst_id = SOME p` >>
  PairCases_on `p` >> simp_tac (srw_ss()) [] >> strip_tac >>
  `p0 = b` by
    (qpat_x_assum `FLOOKUP t.vs_allocas _ = _` mp_tac >>
     qpat_x_assum `_ = t` (fn th => rewrite_tac [GSYM th]) >>
     simp[update_var_def]) >>
  qpat_x_assum `_ = t` (assume_tac o SYM) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_fmp = u.vs_fmp /\
   t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `t = _` (fn th => rewrite_tac [th]) >> simp[update_var_def]) >>
  rpt conj_tac
  >- (qpat_x_assum `t = _` (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
      simp[update_var_def, venom_state_component_equality])
  >- (fs[allocas_from_def] >> metis_tac[])
  >- (qpat_x_assum `t = _` kall_tac >>
      qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def]) >>
  qpat_x_assum `t = _` kall_tac >>
  simp[new_site_bytes_def, pred_setTheory.SUBSET_DEF] >>
  rw[] >> gvs[finite_mapTheory.flookup_thm]
QED

(* ---- Epilogue: one lemma per instruction kind. ---- *)

val eval_lit = cj 1 eval_operand_def;
val eval_label = cj 3 eval_operand_def;

fun rw_asm q = qpat_x_assum q (fn th => rewrite_tac [th]);

Theorem range_bytes_nil[local]:
  range_bytes [] = {}
Proof
  simp[range_bytes_def]
QED

Theorem range_bytes_single[local]:
  range_bytes [(a,l)] = {i | a <= i /\ i < a + l}
Proof
  simp[range_bytes_def, pred_setTheory.EXTENSION]
QED

Theorem new_site_bytes_same[local]:
  !s s'. s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
         new_site_bytes s s' = {}
Proof
  rw[new_site_bytes_def, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> gvs[finite_mapTheory.flookup_thm]
QED

Theorem idx_frame[local]:
  lookup_var x (s with vs_inst_idx := n) = lookup_var x s /\
  eval_operand op (s with vs_inst_idx := n) = eval_operand op s /\
  (allocas_from lo (s with vs_inst_idx := n) <=> allocas_from lo s)
Proof
  Cases_on `op` >> simp[lookup_var_def, eval_operand_def, allocas_from_def]
QED

Theorem update_var_frame[local]:
  lookup_var x (update_var y v s) =
    (if x = y then SOME v else lookup_var x s) /\
  (allocas_from lo (update_var y v s) <=> allocas_from lo s) /\
  (update_var y v s).vs_current_bb = s.vs_current_bb /\
  (update_var y v s).vs_labels = s.vs_labels /\
  (update_var y v s).vs_code = s.vs_code /\
  (update_var y v s).vs_memory = s.vs_memory /\
  (update_var y v s).vs_requests = s.vs_requests /\
  (update_var y v s).vs_call_ctx = s.vs_call_ctx /\
  (update_var y v s).vs_accounts = s.vs_accounts /\
  (update_var y v s).vs_transient = s.vs_transient /\
  (update_var y v s).vs_immutables = s.vs_immutables /\
  (update_var y v s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[update_var_def, lookup_var_def, allocas_from_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[]
QED

Theorem wm_frame[local]:
  lookup_var x (write_memory_with_expansion p bs s) = lookup_var x s /\
  (allocas_from lo (write_memory_with_expansion p bs s) <=>
   allocas_from lo s) /\
  (write_memory_with_expansion p bs s).vs_current_bb = s.vs_current_bb /\
  (write_memory_with_expansion p bs s).vs_labels = s.vs_labels /\
  (write_memory_with_expansion p bs s).vs_code = s.vs_code /\
  (write_memory_with_expansion p bs s).vs_requests = s.vs_requests /\
  (write_memory_with_expansion p bs s).vs_call_ctx = s.vs_call_ctx /\
  (write_memory_with_expansion p bs s).vs_accounts = s.vs_accounts /\
  (write_memory_with_expansion p bs s).vs_transient = s.vs_transient /\
  (write_memory_with_expansion p bs s).vs_immutables = s.vs_immutables /\
  (write_memory_with_expansion p bs s).vs_inst_idx = s.vs_inst_idx /\
  (write_memory_with_expansion p bs s).vs_allocas = s.vs_allocas /\
  (write_memory_with_expansion p bs s).vs_fmp = s.vs_fmp
Proof
  simp[write_memory_with_expansion_def, lookup_var_def, allocas_from_def]
QED

Theorem taint_ok_clean[local]:
  !fn tn inst s.
    (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
    (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
       off <= i /\ i < off + len /\ i IN tn.t_mem ==>
       inst.inst_opcode = MCOPY \/ inst.inst_opcode = RETURN) /\
    inst.inst_opcode <> DELEGATECALL /\ inst.inst_opcode <> CREATE /\
    inst.inst_opcode <> CREATE2 ==>
    taint_ok fn tn inst s
Proof
  rw[taint_ok_def] >> metis_tac[]
QED

(* A non-terminator step that keeps the requests: the check passes it when
   the accesses and taints are fine, given the check from the next
   instruction with the stepped ghost. *)
Theorem ptr_safe_block_plain_step[local]:
  !D lo fuel ctx fn PG G tn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ s'.vs_requests = s.vs_requests /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    ptr_safe_block D lo fuel ctx fn PG (step_prov PG G inst s')
      (step_taint inst s s' tn) bb
      (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb s
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s = OK s'` by simp[step_inst_non_invoke] >>
  drule_all ptr_safe_block_step >> disch_then (fn th => rewrite_tac [th]) >>
  drule_all ghost_step_non_invoke >> disch_then (fn th => rewrite_tac [th]) >>
  asm_rewrite_tac [pairTheory.FST, pairTheory.SND] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def]
QED

(* A halting step passes the check when the halt clauses hold. *)
Theorem ptr_safe_block_halt_step[local]:
  !D lo fuel ctx fn PG G tn bb s inst sh.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt sh /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    (step_taint inst s sh tn).t_stor SUBSET
       D.d_stor sh.vs_call_ctx.cc_address
         (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
    (step_taint inst s sh tn).t_trans SUBSET
       D.d_trans sh.vs_call_ctx.cc_address
         (sh.vs_transient sh.vs_call_ctx.cc_address) /\
    (step_taint inst s sh tn).t_imm SUBSET D.d_imm sh.vs_immutables /\
    ret_taint tn inst s SUBSET D.d_ret sh.vs_returndata ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb s
Proof
  rpt strip_tac >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def, ptr_inst_ok_def,
       step_inst_non_invoke]
QED

Theorem epi_alloca_facts[local]:
  !lo G fn tn PG inst u t buf b N A nx.
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w N)] /\
    inst.inst_outputs = [buf] /\
    t = update_var buf (n2w b)
          (u with <| vs_allocas := A; vs_alloca_next := nx |>) /\
    FLOOKUP A inst.inst_id = SOME (b,N) ==>
    t.vs_requests = u.vs_requests /\
    access_ok lo G fn inst u /\ taint_ok fn tn inst u /\
    step_prov PG G inst t = G |+ (buf,(b,N)) /\
    step_taint inst u t tn =
      tn with <| t_mem := tn.t_mem UNION new_site_bytes u t;
                 t_var := tn.t_var |+ (buf,{}) |>
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- simp[update_var_def]
  >- simp[access_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]
  >- (irule taint_ok_clean >>
      simp[source_memory_read_ranges_def, op_taint_def])
  >- simp[step_prov_def, out_prov_def, set_prov_def, update_var_def] >>
  qpat_x_assum `t = _` kall_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_nil, set_var_taint_def,
       out_taint_def, eval_lit, store_taint_def, adopt_reset_def,
       imm_taint_def, ptrDisciplineTheory.taint_component_equality]
QED

Theorem epi_add_facts[local]:
  !lo G fn tn PG inst s s' x y k a site.
    inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Lit k] /\
    inst.inst_outputs = [y] /\ s' = update_var y (a + k) s /\
    eval_operand (Var x) s = SOME a /\
    FLOOKUP G x = SOME site /\ op_taint tn (Var x) = {} ==>
    step_inst_base inst s = OK s' /\ s'.vs_requests = s.vs_requests /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    step_prov PG G inst s' = G |+ (y,site) /\
    step_taint inst s s' tn = tn with t_var := tn.t_var |+ (y,{})
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (opc_tac ``ADD`` >> asm_rewrite_tac [exec_pure2_def] >> simp[eval_lit])
  >- simp[update_var_frame]
  >- simp[access_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]
  >- (irule taint_ok_clean >>
      simp[source_memory_read_ranges_def] >> rw[] >> fs[op_taint_def])
  >- simp[step_prov_def, out_prov_def, set_prov_def, first_prov_def,
          op_prov_def] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_nil, set_var_taint_def,
       out_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       ptrDisciplineTheory.taint_component_equality, new_site_bytes_same,
       update_var_def]
QED

Theorem epi_mcopy_facts[local]:
  !lo G fn tn PG inst s s' d src n p b sz.
    inst.inst_opcode = MCOPY /\
    inst.inst_operands = [Var d; src; Lit (n2w n)] /\
    inst.inst_outputs = [] /\ s' = mcopy p 0 n s /\
    eval_operand (Var d) s = SOME (n2w p) /\ eval_operand src s = SOME 0w /\
    w2n (n2w p : bytes32) = p /\ w2n (n2w n : bytes32) = n /\
    FLOOKUP G d = SOME (b,sz) /\ b <= p /\ p + n <= b + sz /\ n <= lo /\
    op_prov G src = NONE /\ op_taint tn (Var d) = {} /\
    op_taint tn src = {} ==>
    step_inst_base inst s = OK s' /\ s'.vs_requests = s.vs_requests /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    step_prov PG G inst s' = G /\
    step_taint inst s s' tn =
      tn with t_mem := (tn.t_mem DIFF {i | p <= i /\ i < p + n}) UNION
                       {p + i | i < n /\ i IN tn.t_mem}
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (opc_tac ``MCOPY`` >> asm_rewrite_tac [] >> simp[eval_lit])
  >- simp[mcopy_def, wm_frame]
  >- (simp[access_ok_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, sized_source_write_range_def,
           mem_write_ops_def, mem_read_ops_def, eval_lit] >>
      rw[] >> fs[])
  >- (irule taint_ok_clean >>
      simp[source_memory_read_ranges_def] >> rw[] >> fs[op_taint_def])
  >- simp[step_prov_def, out_prov_def, set_prov_def,
          pred_setTheory.COMPL_EMPTY, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_lit, range_bytes_single, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, pred_setTheory.COMPL_EMPTY,
       finite_mapTheory.DRESTRICT_UNIV,
       ptrDisciplineTheory.taint_component_equality, new_site_bytes_same,
       mcopy_def, wm_frame]
QED

Theorem epi_codecopy_facts[local]:
  !lo G fn tn PG inst s s' d l c n p b sz.
    inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [Var d; Label l; Lit (n2w n)] /\
    inst.inst_outputs = [] /\
    s' = write_memory_with_expansion p
           (TAKE n (DROP (w2n c) s.vs_code ++ REPLICATE n 0w)) s /\
    eval_operand (Var d) s = SOME (n2w p) /\ FLOOKUP s.vs_labels l = SOME c /\
    w2n (n2w p : bytes32) = p /\ w2n (n2w n : bytes32) = n /\
    FLOOKUP G d = SOME (b,sz) /\ b <= p /\ p + n <= b + sz /\
    op_taint tn (Var d) = {} ==>
    step_inst_base inst s = OK s' /\ s'.vs_requests = s.vs_requests /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    step_prov PG G inst s' = G /\
    step_taint inst s s' tn =
      tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p + n}
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (opc_tac ``CODECOPY`` >> asm_rewrite_tac [] >>
      simp[eval_lit, eval_label])
  >- simp[wm_frame]
  >- (simp[access_ok_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, sized_source_write_range_def,
           mem_write_ops_def, eval_lit, eval_label] >>
      rw[] >> fs[])
  >- (irule taint_ok_clean >>
      simp[source_memory_read_ranges_def] >> rw[] >> fs[op_taint_def])
  >- simp[step_prov_def, out_prov_def, set_prov_def,
          pred_setTheory.COMPL_EMPTY, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_lit, eval_label, range_bytes_single, set_var_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       pred_setTheory.COMPL_EMPTY, finite_mapTheory.DRESTRICT_UNIV,
       ptrDisciplineTheory.taint_component_equality, new_site_bytes_same,
       wm_frame]
QED

Theorem epi_return_facts[local]:
  !lo G fn tn inst s d n p b sz sh.
    inst.inst_opcode = RETURN /\ inst.inst_operands = [Var d; Lit (n2w n)] /\
    eval_operand (Var d) s = SOME (n2w p) /\
    w2n (n2w p : bytes32) = p /\ w2n (n2w n : bytes32) = n /\
    FLOOKUP G d = SOME (b,sz) /\ b <= p /\ p + n <= b + sz /\
    op_taint tn (Var d) = {} /\
    sh = halt_state (set_returndata
           (TAKE n (DROP p s.vs_memory ++ REPLICATE n 0w)) s) ==>
    step_inst_base inst s = Halt sh /\
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    (step_taint inst s sh tn).t_stor = tn.t_stor /\
    (step_taint inst s sh tn).t_trans = tn.t_trans /\
    (step_taint inst s sh tn).t_imm = tn.t_imm /\
    ret_taint tn inst s = {i | i < n /\ p + i IN tn.t_mem}
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (opc_tac ``RETURN`` >> asm_rewrite_tac [] >> simp[eval_lit])
  >- (simp[access_ok_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, memory_range_of_operands_def,
           mem_read_ops_def, eval_lit] >>
      rw[] >> fs[])
  >- (irule taint_ok_clean >>
      simp[source_memory_read_ranges_def] >> rw[] >> fs[op_taint_def])
  >- simp[step_taint_def, store_taint_def, adopt_reset_def]
  >- simp[step_taint_def, store_taint_def, adopt_reset_def]
  >- simp[step_taint_def, imm_taint_def] >>
  simp[ret_taint_def, eval_lit]
QED

Theorem op_taint_var_other[local]:
  !tn tn' x y m. tn'.t_var = tn.t_var |+ (y,m) /\ x <> y ==>
    op_taint tn' (Var x) = op_taint tn (Var x)
Proof
  simp[op_taint_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem drop_take_pad[local]:
  !n l m (x:'a). DROP n (TAKE n (l ++ REPLICATE n x) ++ m) = m
Proof
  rpt gen_tac >>
  `LENGTH (TAKE n (l ++ REPLICATE n x)) = n` by
    simp[listTheory.LENGTH_TAKE_EQ] >>
  metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* The returned bytes past the runtime code are tainted only where the
   region was. *)
Theorem epi_ret_dead[local]:
  !X Y Z b rt cap P.
    Z = (((X UNION Y) DIFF {i | b + rt <= i /\ i < b + rt + cap}) UNION
         {b + rt + j | j < cap /\ j IN X UNION Y}) DIFF
        {i | b <= i /\ i < b + rt} /\
    (!j. j < cap /\ j IN X ==> P j) /\ cap <= b /\
    Y SUBSET {i | b <= i /\ i < b + (rt + cap)} ==>
    !i. i < rt + cap /\ b + i IN Z ==> rt <= i /\ P (i - rt)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `~(b + i < b + rt)` by (qpat_x_assum `b + i IN Z` mp_tac >> simp[]) >>
  `rt <= i` by decide_tac >>
  `?j. b + i = b + rt + j /\ j < cap /\ j IN X UNION Y` by
    (qpat_x_assum `b + i IN Z` mp_tac >> simp[]) >>
  `j IN X` by
    (spose_not_then assume_tac >>
     `j IN Y` by fs[] >>
     fs[pred_setTheory.SUBSET_DEF] >> res_tac >> decide_tac) >>
  `i - rt = j` by decide_tac >>
  simp[]
QED

(* The epilogue from its start, with the invariant, passes the check. *)
Theorem epilogue_ptr_safe[local]:
  !tops runtime_bc am tx ctx func cenv cx es u G tn imm st st'.
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm st =
      ((),st') /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    ~block_is_terminated st /\
    stmt_state_rel ctx func cenv cx es u /\ cenv.ce_is_ctor /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       (!x. imm = Var x ==> not_fresh_at st x)) /\
    ~u.vs_halted /\ u.vs_current_bb = st.cs_current_bb /\
    u.vs_inst_idx = LENGTH st.cs_current_insts /\
    ~ctx_has_dalloca ctx /\
    deploy_ptr_inv tops runtime_bc am tx imm G tn u ==>
    !fuel. ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops)
             fuel ctx func [] G tn u
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_x_assum `deploy_ptr_inv _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_ptr_inv_def]) >>
  `immutable_base_zero cenv u` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `u`, `st`, `st'`,
               `LENGTH runtime_bc`, `imm_len tops`, `imm`]
    mp_tac compile_constructor_epilogue_padded_run_from >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  rename1 `run_from fuel0 ctx func u = Halt final` >>
  drule_all compile_constructor_epilogue_append >> strip_tac >>
  drule_all compile_constructor_epilogue_alloca_member >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `u`,
     `mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (LENGTH runtime_bc + imm_len tops))]
        ["%" ++ toString st.cs_next_var]`,
     `LENGTH runtime_bc + imm_len tops`, `"%" ++ toString st.cs_next_var`,
     `imm_len tops`] mp_tac epilogue_alloca_step >>
  impl_tac >- (asm_rewrite_tac [] >> simp[mk_inst_def]) >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `MEM _ _` kall_tac >>
  qpat_x_assum `immutable_base_zero _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_base_zero_def]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by
    asm_rewrite_tac [] >>
  pure_rewrite_tac [ptr_safe_run_def] >>
  qpat_assum `lookup_block u.vs_current_bb _ = _`
    (fn th => rewrite_tac [th]) >>
  simp_tac (srw_ss()) [] >>
  `lookup_var ("%" ++ toString st.cs_next_var) t = SOME (n2w b) /\
   (!x. x <> "%" ++ toString st.cs_next_var ==>
        lookup_var x t = lookup_var x u) /\
   t.vs_current_bb = u.vs_current_bb /\ t.vs_labels = u.vs_labels /\
   t.vs_code = u.vs_code /\ t.vs_memory = u.vs_memory /\
   t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_immutables = u.vs_immutables` by
    (qpat_x_assum `t = _` (fn th => rewrite_tac [th]) >>
     simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `imm_len tops = 0`
  >- (
    (* No immutables: ALLOCA, CODECOPY, RETURN. *)
    qpat_x_assum `imm_len tops = 0` (fn th =>
      RULE_ASSUM_TAC (REWRITE_RULE [th, arithmeticTheory.ADD_0]) >>
      rewrite_tac [th]) >>
    drule_all compile_constructor_epilogue_zero_insts >> strip_tac >>
    qabbrev_tac `rt = LENGTH runtime_bc` >>
    qabbrev_tac `L = LENGTH st.cs_current_insts` >>
    qabbrev_tac `buf = "%" ++ toString st.cs_next_var` >>
    qabbrev_tac `id = st.cs_next_id` >>
    qabbrev_tac `D = deploy_dead tops runtime_bc am tx` >>
    qabbrev_tac `i0 = mk_inst id ALLOCA [Lit (n2w rt)] [buf]` >>
    qabbrev_tac `i1 = mk_inst (id + 1) CODECOPY
                   [Var buf; Label "runtime_begin"; Lit (n2w rt)] []` >>
    qabbrev_tac `i2 = mk_inst (id + 2) RETURN [Var buf; Lit (n2w rt)] []` >>
    `i0.inst_opcode = ALLOCA /\ i0.inst_operands = [Lit (n2w rt)] /\
     i0.inst_outputs = [buf] /\
     i1.inst_opcode = CODECOPY /\ i1.inst_outputs = [] /\
     i1.inst_operands = [Var buf; Label "runtime_begin"; Lit (n2w rt)] /\
     i2.inst_opcode = RETURN /\ i2.inst_operands = [Var buf; Lit (n2w rt)]` by
      simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
    `get_instruction bb L = SOME i0 /\ get_instruction bb (L + 1) = SOME i1 /\
     get_instruction bb (L + 2) = SOME i2` by
      (qpat_x_assum `!i. i < LENGTH (emitted_insts st st') ==> _` mp_tac >>
       qpat_x_assum `emitted_insts st st' = _` (fn th => rewrite_tac [th]) >>
       rpt (pop_assum kall_tac) >> strip_tac >> rpt conj_tac
       >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
       >- (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
       first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
    `D.d_imm = K UNIV` by simp[Abbr `D`, deploy_dead_def] >>
    `b < dimword(:256) /\ rt < dimword(:256)` by decide_tac >>
    `w2n (n2w b : bytes32) = b /\ w2n (n2w rt : bytes32) = rt` by simp[] >>
    (* ALLOCA *)
    qspecl_then [`0`, `G`, `func`, `tn`, `[]`, `i0`, `u`, `t`, `buf`, `b`,
                 `rt`, `A`, `nx`] mp_tac epi_alloca_facts >>
    impl_tac >- asm_rewrite_tac [] >> strip_tac >>
    qpat_x_assum `t = _` kall_tac >>
    qspecl_then [`D`, `0`, `fuel`, `ctx`, `func`, `[]`, `G`, `tn`, `bb`, `u`,
                 `i0`, `t`] mp_tac ptr_safe_block_plain_step >>
    impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
    disch_then match_mp_tac >>
    rw_asm `step_prov _ _ i0 _ = _` >> rw_asm `step_taint i0 _ _ _ = _` >>
    qpat_assum `u.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
    qabbrev_tac `G1 = G |+ (buf,(b,rt))` >>
    qabbrev_tac `tn1 = tn with <| t_mem := tn.t_mem UNION new_site_bytes u t;
                                  t_var := tn.t_var |+ (buf,{}) |>` >>
    qabbrev_tac `s1 = t with vs_inst_idx := SUC L` >>
    `s1.vs_inst_idx = L + 1 /\ allocas_from 0 s1 /\
     eval_operand (Var buf) s1 = SOME (n2w b) /\
     FLOOKUP s1.vs_labels "runtime_begin" = SOME codepos` by
      simp[Abbr `s1`, idx_frame, eval_operand_def] >>
    (* CODECOPY *)
    qabbrev_tac `t2 = write_memory_with_expansion b
       (TAKE rt (DROP (w2n codepos) s1.vs_code ++ REPLICATE rt 0w)) s1` >>
    qspecl_then [`0`, `G1`, `func`, `tn1`, `[]`, `i1`, `s1`, `t2`, `buf`,
                 `"runtime_begin"`, `codepos`, `rt`, `b`, `b`, `rt`]
      mp_tac epi_codecopy_facts >>
    impl_tac
    >- (asm_rewrite_tac [] >>
        simp[Abbr `G1`, Abbr `tn1`, Abbr `t2`, op_taint_def,
             finite_mapTheory.FLOOKUP_UPDATE]) >>
    strip_tac >>
    qspecl_then [`D`, `0`, `fuel`, `ctx`, `func`, `[]`, `G1`, `tn1`, `bb`,
                 `s1`, `i1`, `t2`] mp_tac ptr_safe_block_plain_step >>
    impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
    disch_then match_mp_tac >>
    rw_asm `step_prov _ _ i1 _ = _` >> rw_asm `step_taint i1 _ _ _ = _` >>
    qpat_assum `s1.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
    qabbrev_tac `tn2 = tn1 with t_mem := tn1.t_mem DIFF {i | b <= i /\ i < b + rt}` >>
    qabbrev_tac `s2 = t2 with vs_inst_idx := SUC (L + 1)` >>
    `s2.vs_inst_idx = L + 2 /\ allocas_from 0 s2 /\
     eval_operand (Var buf) s2 = SOME (n2w b) /\
     s2.vs_call_ctx = u.vs_call_ctx /\ s2.vs_accounts = u.vs_accounts /\
     s2.vs_transient = u.vs_transient /\ s2.vs_immutables = u.vs_immutables` by
      simp[Abbr `s2`, Abbr `t2`, Abbr `s1`, idx_frame, wm_frame,
           eval_operand_def] >>
    (* RETURN *)
    qabbrev_tac `sh = halt_state (set_returndata
       (TAKE rt (DROP b s2.vs_memory ++ REPLICATE rt 0w)) s2)` >>
    qspecl_then [`0`, `G1`, `func`, `tn2`, `i2`, `s2`, `buf`, `rt`, `b`, `b`,
                 `rt`, `sh`] mp_tac epi_return_facts >>
    impl_tac
    >- (asm_rewrite_tac [] >>
        simp[Abbr `G1`, Abbr `tn2`, Abbr `tn1`, Abbr `sh`, op_taint_def,
             finite_mapTheory.FLOOKUP_UPDATE]) >>
    strip_tac >>
    qspecl_then [`D`, `0`, `fuel`, `ctx`, `func`, `[]`, `G1`, `tn2`, `bb`,
                 `s2`, `i2`, `sh`] mp_tac ptr_safe_block_halt_step >>
    impl_tac
    >- (asm_rewrite_tac [] >>
        `tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans` by
          simp[Abbr `tn2`, Abbr `tn1`] >>
        `{i | i < rt /\ b + i IN tn2.t_mem} = {}` by
          (simp[Abbr `tn2`, pred_setTheory.EXTENSION] >> gen_tac >>
           Cases_on `x < rt` >> simp[]) >>
        asm_rewrite_tac [pred_setTheory.EMPTY_SUBSET, pred_setTheory.SUBSET_UNIV,
                         combinTheory.K_THM] >>
        simp[Abbr `sh`, halt_state_def, set_returndata_def]) >>
    simp[]) >>
  (* With immutables: ALLOCA, ADD, MCOPY, CODECOPY, RETURN. *)
  `0 < imm_len tops` by decide_tac >>
  drule_all compile_constructor_epilogue_positive_insts >> strip_tac >>
  `cenv.ce_imm_alloca = SOME imm /\ !x. imm = Var x ==> not_fresh_at st x` by
    (qpat_x_assum `imm_len tops <> 0 ==> _` mp_tac >> asm_rewrite_tac []) >>
  `eval_operand imm u = SOME 0w` by
    (qpat_x_assum `!base. _` (qspec_then `imm` mp_tac) >> asm_rewrite_tac []) >>
  `!x. imm = Var x ==>
       x <> "%" ++ toString st.cs_next_var /\
       x <> "%" ++ toString (st.cs_next_var + 1) /\
       FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by
    (qpat_x_assum `!x. imm = Var x ==> not_fresh_at _ _` mp_tac >>
     qpat_x_assum `!x. imm = Var x ==> FLOOKUP _ _ = _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[not_fresh_at_def] >> gvs[] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  qabbrev_tac `rt = LENGTH runtime_bc` >>
  qabbrev_tac `cap = imm_len tops` >>
  qabbrev_tac `L = LENGTH st.cs_current_insts` >>
  qabbrev_tac `buf = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `tmp = "%" ++ toString (st.cs_next_var + 1)` >>
  qabbrev_tac `id = st.cs_next_id` >>
  qabbrev_tac `D = deploy_dead tops runtime_bc am tx` >>
  qabbrev_tac `i0 = mk_inst id ALLOCA [Lit (n2w (rt + cap))] [buf]` >>
  qabbrev_tac `i1 = mk_inst (id + 1) ADD [Var buf; Lit (n2w rt)] [tmp]` >>
  qabbrev_tac `i2 = mk_inst (id + 2) MCOPY [Var tmp; imm; Lit (n2w cap)] []` >>
  qabbrev_tac `i3 = mk_inst (id + 3) CODECOPY
                 [Var buf; Label "runtime_begin"; Lit (n2w rt)] []` >>
  qabbrev_tac `i4 = mk_inst (id + 4) RETURN
                 [Var buf; Lit (n2w (rt + cap))] []` >>
  `i0.inst_opcode = ALLOCA /\ i0.inst_operands = [Lit (n2w (rt + cap))] /\
   i0.inst_outputs = [buf] /\
   i1.inst_opcode = ADD /\ i1.inst_operands = [Var buf; Lit (n2w rt)] /\
   i1.inst_outputs = [tmp] /\
   i2.inst_opcode = MCOPY /\ i2.inst_operands = [Var tmp; imm; Lit (n2w cap)] /\
   i2.inst_outputs = [] /\
   i3.inst_opcode = CODECOPY /\ i3.inst_outputs = [] /\
   i3.inst_operands = [Var buf; Label "runtime_begin"; Lit (n2w rt)] /\
   i4.inst_opcode = RETURN /\
   i4.inst_operands = [Var buf; Lit (n2w (rt + cap))]` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`, mk_inst_def] >>
  `get_instruction bb L = SOME i0 /\ get_instruction bb (L + 1) = SOME i1 /\
   get_instruction bb (L + 2) = SOME i2 /\
   get_instruction bb (L + 3) = SOME i3 /\
   get_instruction bb (L + 4) = SOME i4` by
    (qpat_x_assum `!i. i < LENGTH (emitted_insts st st') ==> _` mp_tac >>
     qpat_x_assum `emitted_insts st st' = _` (fn th => rewrite_tac [th]) >>
     rpt (pop_assum kall_tac) >> strip_tac >> rpt conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
     >- (first_x_assum (qspec_then `1` mp_tac) >> simp[])
     >- (first_x_assum (qspec_then `2` mp_tac) >> simp[])
     >- (first_x_assum (qspec_then `3` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `4` mp_tac) >> simp[]) >>
  `buf <> tmp` by simp[Abbr `buf`, Abbr `tmp`] >>
  `!r. D.d_ret r = {i | rt <= i /\ imm_section_dead tops (DROP rt r) (i - rt)}` by
    simp[Abbr `D`, Abbr `rt`, deploy_dead_def] >>
  `D.d_imm = K UNIV` by simp[Abbr `D`, deploy_dead_def] >>
  `b < dimword(:256) /\ rt < dimword(:256) /\ cap < dimword(:256) /\
   b + rt < dimword(:256) /\ rt + cap < dimword(:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b /\ w2n (n2w rt : bytes32) = rt /\
   w2n (n2w cap : bytes32) = cap /\ w2n (n2w (b + rt) : bytes32) = b + rt /\
   w2n (n2w (rt + cap) : bytes32) = rt + cap` by simp[] >>
  (* ALLOCA *)
  qspecl_then [`cap`, `G`, `func`, `tn`, `[]`, `i0`, `u`, `t`, `buf`, `b`,
               `rt + cap`, `A`, `nx`] mp_tac epi_alloca_facts >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `t = _` kall_tac >>
  qspecl_then [`D`, `cap`, `fuel`, `ctx`, `func`, `[]`, `G`, `tn`, `bb`, `u`,
               `i0`, `t`] mp_tac ptr_safe_block_plain_step >>
  impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
  disch_then match_mp_tac >>
  rw_asm `step_prov _ _ i0 _ = _` >> rw_asm `step_taint i0 _ _ _ = _` >>
  qpat_assum `u.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
  qabbrev_tac `G1 = G |+ (buf,(b,rt + cap))` >>
  qabbrev_tac `tn1 = tn with <| t_mem := tn.t_mem UNION new_site_bytes u t;
                                t_var := tn.t_var |+ (buf,{}) |>` >>
  qabbrev_tac `s1 = t with vs_inst_idx := SUC L` >>
  `s1.vs_inst_idx = L + 1 /\ allocas_from cap s1 /\
   lookup_var buf s1 = SOME (n2w b) /\
   eval_operand (Var buf) s1 = SOME (n2w b)` by
    simp[Abbr `s1`, idx_frame, eval_operand_def] >>
  (* ADD *)
  qabbrev_tac `t2 = update_var tmp (n2w b + n2w rt) s1` >>
  qspecl_then [`cap`, `G1`, `func`, `tn1`, `[]`, `i1`, `s1`, `t2`, `buf`,
               `tmp`, `n2w rt`, `n2w b`, `(b, rt + cap)`]
    mp_tac epi_add_facts >>
  impl_tac
  >- (asm_rewrite_tac [] >>
      simp[Abbr `G1`, Abbr `tn1`, Abbr `t2`, op_taint_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  strip_tac >>
  qspecl_then [`D`, `cap`, `fuel`, `ctx`, `func`, `[]`, `G1`, `tn1`, `bb`,
               `s1`, `i1`, `t2`] mp_tac ptr_safe_block_plain_step >>
  impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
  disch_then match_mp_tac >>
  rw_asm `step_prov _ _ i1 _ = _` >> rw_asm `step_taint i1 _ _ _ = _` >>
  qpat_assum `s1.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
  qabbrev_tac `G2 = G1 |+ (tmp,(b,rt + cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (tmp,{})` >>
  qabbrev_tac `s2 = t2 with vs_inst_idx := SUC (L + 1)` >>
  `s2.vs_inst_idx = L + 2 /\ allocas_from cap s2 /\
   eval_operand (Var tmp) s2 = SOME (n2w (b + rt)) /\
   eval_operand (Var buf) s2 = SOME (n2w b)` by
    simp[Abbr `s2`, Abbr `t2`, idx_frame, update_var_frame, eval_operand_def,
         wordsTheory.word_add_n2w] >>
  `eval_operand imm s2 = SOME 0w` by
    (qpat_x_assum `eval_operand imm u = _` mp_tac >>
     qpat_x_assum `!x. imm = Var x ==> x <> buf /\ _` mp_tac >>
     Cases_on `imm` >>
     simp[Abbr `s2`, Abbr `t2`, Abbr `s1`, idx_frame, update_var_frame,
          eval_operand_def]) >>
  `op_taint tn2 (Var tmp) = {}` by
    simp[Abbr `tn2`, op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `op_prov G2 imm = NONE /\ op_taint tn2 imm = {}` by
    (Cases_on `imm`
     >- simp[op_prov_def, op_taint_def]
     >- (qpat_x_assum `!x. Var _ = Var x ==> x <> buf /\ _`
           (qspec_then `s` (strip_assume_tac o
              REWRITE_RULE [operand_11, boolTheory.IMP_CLAUSES])) >>
         `op_taint tn2 (Var s) = op_taint tn1 (Var s)` by
           (qspecl_then [`tn1`, `tn2`, `s`, `tmp`, `{}`] mp_tac
              op_taint_var_other >> simp[Abbr `tn2`]) >>
         `op_taint tn1 (Var s) = op_taint tn (Var s)` by
           (qspecl_then [`tn`, `tn1`, `s`, `buf`, `{}`] mp_tac
              op_taint_var_other >> simp[Abbr `tn1`]) >>
         `FLOOKUP G2 s = NONE` by
           simp[Abbr `G2`, Abbr `G1`, finite_mapTheory.FLOOKUP_UPDATE] >>
         asm_rewrite_tac [op_prov_def] >> simp[]) >>
     simp[op_prov_def, op_taint_def]) >>
  (* MCOPY *)
  qabbrev_tac `t3 = mcopy (b + rt) 0 cap s2` >>
  qspecl_then [`cap`, `G2`, `func`, `tn2`, `[]`, `i2`, `s2`, `t3`, `tmp`,
               `imm`, `cap`, `b + rt`, `b`, `rt + cap`]
    mp_tac epi_mcopy_facts >>
  impl_tac
  >- (asm_rewrite_tac [] >>
      simp[Abbr `G2`, Abbr `t3`, finite_mapTheory.FLOOKUP_UPDATE]) >>
  strip_tac >>
  qspecl_then [`D`, `cap`, `fuel`, `ctx`, `func`, `[]`, `G2`, `tn2`, `bb`,
               `s2`, `i2`, `t3`] mp_tac ptr_safe_block_plain_step >>
  impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
  disch_then match_mp_tac >>
  rw_asm `step_prov _ _ i2 _ = _` >> rw_asm `step_taint i2 _ _ _ = _` >>
  qpat_assum `s2.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
  qabbrev_tac `tn3 = tn2 with t_mem :=
    (tn2.t_mem DIFF {i | b + rt <= i /\ i < b + rt + cap}) UNION
    {b + rt + i | i < cap /\ i IN tn2.t_mem}` >>
  qabbrev_tac `s3 = t3 with vs_inst_idx := SUC (L + 2)` >>
  `s3.vs_inst_idx = L + 3 /\ allocas_from cap s3 /\
   lookup_var buf s3 = SOME (n2w b) /\
   eval_operand (Var buf) s3 = SOME (n2w b) /\
   FLOOKUP s3.vs_labels "runtime_begin" = SOME codepos` by
    simp[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `t2`, Abbr `s1`, idx_frame,
         update_var_frame, mcopy_def, wm_frame, eval_operand_def] >>
  (* CODECOPY *)
  qabbrev_tac `t4 = write_memory_with_expansion b
     (TAKE rt (DROP (w2n codepos) s3.vs_code ++ REPLICATE rt 0w)) s3` >>
  qspecl_then [`cap`, `G2`, `func`, `tn3`, `[]`, `i3`, `s3`, `t4`, `buf`,
               `"runtime_begin"`, `codepos`, `rt`, `b`, `b`, `rt + cap`]
    mp_tac epi_codecopy_facts >>
  impl_tac
  >- (asm_rewrite_tac [] >>
      simp[Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `t4`,
           op_taint_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  strip_tac >>
  qspecl_then [`D`, `cap`, `fuel`, `ctx`, `func`, `[]`, `G2`, `tn3`, `bb`,
               `s3`, `i3`, `t4`] mp_tac ptr_safe_block_plain_step >>
  impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
  disch_then match_mp_tac >>
  rw_asm `step_prov _ _ i3 _ = _` >> rw_asm `step_taint i3 _ _ _ = _` >>
  qpat_assum `s3.vs_inst_idx = _` (fn th => rewrite_tac [th]) >>
  qabbrev_tac `tn4 = tn3 with t_mem := tn3.t_mem DIFF {i | b <= i /\ i < b + rt}` >>
  qabbrev_tac `s4 = t4 with vs_inst_idx := SUC (L + 3)` >>
  `s4.vs_inst_idx = L + 4 /\ allocas_from cap s4 /\
   eval_operand (Var buf) s4 = SOME (n2w b)` by
    simp[Abbr `s4`, Abbr `t4`, idx_frame, wm_frame, eval_operand_def] >>
  (* RETURN *)
  qabbrev_tac `sh = halt_state (set_returndata
     (TAKE (rt + cap) (DROP b s4.vs_memory ++ REPLICATE (rt + cap) 0w)) s4)` >>
  qspecl_then [`cap`, `G2`, `func`, `tn4`, `i4`, `s4`, `buf`, `rt + cap`, `b`,
               `b`, `rt + cap`, `sh`] mp_tac epi_return_facts >>
  impl_tac
  >- (asm_rewrite_tac [] >>
      simp[Abbr `G2`, Abbr `G1`, Abbr `tn4`, Abbr `tn3`, Abbr `tn2`,
           Abbr `tn1`, Abbr `sh`, op_taint_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  strip_tac >>
  (* The run from u halts in sh, so sh is final. *)
  `s1.vs_current_bb = u.vs_current_bb /\ s2.vs_current_bb = u.vs_current_bb /\
   s3.vs_current_bb = u.vs_current_bb /\ s4.vs_current_bb = u.vs_current_bb` by
    simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `t2`,
         Abbr `s1`, update_var_frame, mcopy_def, wm_frame] >>
  `run_from fuel0 ctx func u = run_from fuel0 ctx func s1` by
    (qspecl_then [`fuel0`, `ctx`, `func`, `u`, `bb`, `i0`, `t`]
       mp_tac run_from_step >>
     impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
     simp[Abbr `s1`]) >>
  `run_from fuel0 ctx func s1 = run_from fuel0 ctx func s2` by
    (qspecl_then [`fuel0`, `ctx`, `func`, `s1`, `bb`, `i1`, `t2`]
       mp_tac run_from_step >>
     impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
     simp[Abbr `s2`]) >>
  `run_from fuel0 ctx func s2 = run_from fuel0 ctx func s3` by
    (qspecl_then [`fuel0`, `ctx`, `func`, `s2`, `bb`, `i2`, `t3`]
       mp_tac run_from_step >>
     impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
     simp[Abbr `s3`]) >>
  `run_from fuel0 ctx func s3 = run_from fuel0 ctx func s4` by
    (qspecl_then [`fuel0`, `ctx`, `func`, `s3`, `bb`, `i3`, `t4`]
       mp_tac run_from_step >>
     impl_tac >- (asm_rewrite_tac [] >> simp[is_terminator_def]) >>
     simp[Abbr `s4`]) >>
  `run_from fuel0 ctx func s4 = Halt sh` by
    (irule run_from_halt >> qexistsl_tac [`bb`, `i4`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `final = sh` by
    (qpat_x_assum `run_from fuel0 ctx func u = Halt final` mp_tac >>
     asm_rewrite_tac [] >> simp[]) >>
  qpat_x_assum `final = sh` SUBST_ALL_TAC >>
  qspecl_then [`D`, `cap`, `fuel`, `ctx`, `func`, `[]`, `G2`, `tn4`, `bb`,
               `s4`, `i4`, `sh`] mp_tac ptr_safe_block_halt_step >>
  impl_tac
  >- (asm_rewrite_tac [] >>
      `tn4.t_stor = tn.t_stor /\ tn4.t_trans = tn.t_trans` by
        simp[Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >>
      asm_rewrite_tac [pred_setTheory.SUBSET_UNIV,
                       combinTheory.K_THM] >>
      rewrite_tac [drop_take_pad] >>
      `mem_bytes_at 0 cap u.vs_memory =
         TAKE cap (u.vs_memory ++ REPLICATE cap 0w)` by
        simp[mem_bytes_at_def] >>
      pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      qspecl_then [`tn.t_mem`, `new_site_bytes u t`, `tn4.t_mem`, `b`, `rt`,
                   `cap`, `imm_section_dead tops
                             (TAKE cap (u.vs_memory ++ REPLICATE cap 0w))`]
        mp_tac epi_ret_dead >>
      impl_tac
      >- (asm_rewrite_tac [] >>
          simp[Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]) >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  simp[]
QED


Theorem deploy_dead_trans_unlock[local]:
  !tops runtime_bc am tx nkey X a st v.
    storage_layout_safe (deploy_evaluation_context tops am tx) /\
    (deploy_evaluation_context tops am tx).nonreentrant_slot = SOME nkey /\
    X SUBSET (deploy_dead tops runtime_bc am tx).d_trans a st ==>
    key_update X (n2w nkey) {} SUBSET
      (deploy_dead tops runtime_bc am tx).d_trans a
        (update_storage (n2w nkey) v st)
Proof
  rw[deploy_dead_def, pred_setTheory.SUBSET_DEF, key_update_def,
     pairTheory.FORALL_PROD] >>
  first_x_assum drule >> rw[] >>
  fs[deploy_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `storage_dead cx0 T _ _ _` >>
  `(cx0 with in_deploy := T).nonreentrant_slot = SOME nkey` by simp[] >>
  drule_all nonreentrant_storage_dead_frame >> strip_tac >>
  fs[storage_dead_in_deploy]
QED

Theorem constructor_exit_run_ptr:
  !tops runtime_bc am tx ctx func cenv body_cenv cx es s G tn nr nkey ut
   st_exit st_epilogue st_final imm.
    cenv.ce_is_ctor /\ same_frame cenv body_cenv /\
    st_exit.cs_current_insts = [] /\
    (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
      st_exit = ((), st_epilogue) /\
    compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
      st_epilogue = ((), st_final) /\
    fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       (!x. imm = Var x ==> not_fresh_at st_epilogue x)) /\
    cx = deploy_evaluation_context tops am tx /\
    stmt_state_rel ctx func body_cenv cx es s /\ ~s.vs_halted /\
    s.vs_current_bb = st_exit.cs_current_bb /\ s.vs_inst_idx = 0 /\
    deploy_ptr_inv tops runtime_bc am tx imm G tn s ==>
    ?fuel final.
      run_from fuel ctx func s = Halt final /\
      ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
        ctx func [] G tn s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  drule_all constructor_exit_run >> strip_tac >>
  qexistsl_tac [`fuel`, `final`] >> simp[] >>
  `nr ==> ut` by simp[] >>
  drule_all ctorReturnFrameTheory.constructor_exit_code >> strip_tac >>
  `body_cenv.ce_is_ctor /\
   (imm_len tops <> 0 ==> body_cenv.ce_imm_alloca = SOME imm /\
      (!x. imm = Var x ==> not_fresh_at st_epilogue x))` by
    (qpat_x_assum `same_frame cenv body_cenv` mp_tac >>
     qpat_x_assum `cenv.ce_is_ctor` mp_tac >>
     qpat_x_assum `imm_len tops <> 0 ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[same_frame_def, compile_env_component_equality] >> gvs[]) >>
  `allocas_from (imm_len tops) s` by fs[deploy_ptr_inv_def] >>
  reverse (Cases_on `nr`)
  >- ((* no unlock: the epilogue from the exit block's start *)
      qpat_x_assum `(if F then _ else _) _ = _` mp_tac >>
      simp[comp_return_def] >> strip_tac >>
      qspecl_then [`tops`, `runtime_bc`, `am`, `tx`, `ctx`, `func`, `body_cenv`,
                   `deploy_evaluation_context tops am tx`, `es`, `s`, `G`,
                   `tn`, `imm`, `st_epilogue`, `st_final`]
        mp_tac epilogue_ptr_safe >>
      impl_tac >- fs[] >> simp[]) >>
  (* the unlock's TSTORE, then the epilogue *)
  RULE_ASSUM_TAC (REWRITE_RULE []) >>
  POP_ASSUM_LIST (MAP_EVERY strip_assume_tac) >>
  `st_epilogue = st_exit with
     <| cs_current_insts := st_exit.cs_current_insts ++
          [mk_inst st_exit.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []];
        cs_next_id := st_exit.cs_next_id + 1 |>` by
    (qspecl_then [`T`, `nkey`, `ut`, `F`, `st_exit`, `st_epilogue`] mp_tac
       optional_unlock_code >> simp[] >> disch_then irule >>
     qpat_x_assum `compile_nonreentrant_unlock _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac []) >>
  qabbrev_tac `i0 = mk_inst st_exit.cs_next_id TSTORE
                      [Lit (n2w nkey); Lit 0w] []` >>
  `st_epilogue.cs_current_bb = st_exit.cs_current_bb /\
   st_epilogue.cs_current_insts = [i0]` by
    (qpat_x_assum `st_epilogue = _` (fn th => rewrite_tac [th]) >> simp[]) >>
  qabbrev_tac `u = tstore (n2w nkey) 0w s with vs_inst_idx := 1` >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `step_inst_base i0 s = OK (tstore (n2w nkey) 0w s)` by
    (simp[Abbr `i0`, mk_inst_def] >>
     simp[opcode_eq ``TSTORE``, exec_write2_def, eval_operand_def]) >>
  `~is_terminator i0.inst_opcode /\ i0.inst_opcode <> INVOKE` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  `step_inst fuel ctx i0 s = OK (tstore (n2w nkey) 0w s)` by
    simp[step_inst_non_invoke] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i0` by
    (qspecl_then [`st_exit`, `st_epilogue`, `func`, `[i0]`] mp_tac
       fn_has_code_same_block >>
     impl_tac >- simp[] >> strip_tac >> qexists_tac `bb` >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[ptr_safe_run_def] >>
  drule_all ptr_safe_block_step >>
  disch_then (fn th => rewrite_tac [th]) >>
  `ghost_step fuel ctx [] G tn i0 s =
   (G, tn with t_trans := key_update tn.t_trans (n2w nkey) {})` by
    (drule_all ghost_step_non_invoke >>
     disch_then (fn th => rewrite_tac [th]) >>
     simp[step_prov_def, set_prov_def, step_taint_def, Abbr `i0`,
          mk_inst_def, ptrDisciplineTheory.taint_component_equality,
          mem_taint_def, new_site_bytes_def, step_writes_def,
          source_memory_write_ranges_def, range_bytes_def,
          written_taint_def, set_var_taint_def, adopt_reset_def,
          store_taint_def, imm_taint_def, eval_operand_def, op_taint_def,
          tstore_def, finite_mapTheory.DRESTRICT_UNIV] >>
     rw[pred_setTheory.EXTENSION] >> gvs[finite_mapTheory.flookup_thm] >>
     metis_tac[]) >>
  pop_assum (fn th => rewrite_tac [th]) >> simp[] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def,
           taint_ok_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, mem_write_ops_def,
           mem_read_ops_def, Abbr `i0`, mk_inst_def, op_taint_def] >>
      simp[tstore_def] >> rw[] >> fs[]) >>
  `ptr_safe_block (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
     ctx func [] G (tn with t_trans := key_update tn.t_trans (n2w nkey) {})
     bb (tstore (n2w nkey) 0w s with vs_inst_idx := SUC s.vs_inst_idx) =
   ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
     ctx func [] G (tn with t_trans := key_update tn.t_trans (n2w nkey) {})
     u` by
    (simp[ptr_safe_run_def, Abbr `u`, tstore_def] >>
     qpat_x_assum `s.vs_current_bb = _` (SUBST1_TAC o SYM) >>
     rw_asm `lookup_block s.vs_current_bb _ = SOME _` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`, `ctx`, `func`, `body_cenv`,
               `deploy_evaluation_context tops am tx`,
               `es with tStorage :=
                  ((deploy_evaluation_context tops am tx).txn.target =+
                   update_storage (n2w nkey) 0w
                     (es.tStorage (deploy_evaluation_context tops am tx).txn.target))
                  es.tStorage`,
               `u`, `G`,
               `tn with t_trans := key_update tn.t_trans (n2w nkey) {}`,
               `imm`, `st_epilogue`, `st_final`] mp_tac epilogue_ptr_safe >>
  impl_tac >- (
    simp[Abbr `u`, stmt_state_rel_inst_idx] >>
    conj_tac
    >- (simp[GSYM tstore_def] >>
        irule constructor_unlock_stmt_state_rel >> simp[]) >>
    conj_tac >- simp[tstore_def] >>
    (* the invariant after the unlock *)
    qpat_x_assum `deploy_ptr_inv _ _ _ _ _ _ _ s` mp_tac >>
    simp[deploy_ptr_inv_def, allocas_from_def, op_taint_def, tstore_def,
         combinTheory.APPLY_UPDATE_THM] >>
    strip_tac >> conj_tac
    >- (irule deploy_dead_trans_unlock >> asm_rewrite_tac []) >>
    qpat_x_assum `allocas_from _ s` mp_tac >>
    rewrite_tac [allocas_from_def]) >>
  disch_then (qspec_then `fuel` mp_tac) >>
  simp[ptr_safe_run_def, Abbr `u`, tstore_def] >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = SOME _` mp_tac >>
  qpat_x_assum `s.vs_current_bb = _` (fn th => rewrite_tac [th]) >>
  disch_then (fn th => rewrite_tac [th]) >> simp[]
QED
