(*
 * Joint gas-origin/pointer paths of the counted word copy loop that
 * compile_word_copy_loop emits between storage (or transient storage) and
 * memory, in both directions, at any reserved bound lo.
 *
 * TOP-LEVEL:
 *   storage_copy_loop_origin_ptr -- SLOAD/TLOAD + MSTORE per slot
 *   memory_copy_loop_origin_ptr -- MLOAD + SSTORE/TSTORE per slot
 *   inst_seq_ptr_lower_bound_transport -- a pointer-checked straight-line
 *     run at a lower reserved bound is checked at a higher one
 *)
Theory fragGasCopyLoop
Ancestors
  emitHelperProps stmtSimStoreCopy bodyMemAssignTopCopyCompiler
  bodyMemAssignTopCopyLoop fragGasPathPtr wordLoadStorePtr assignBasePtrWordStore codegenRel
  contextCodegenRel exprSimPtrTopLevelStorageCopy exprSimPtrTopLevelCopy exprSimStorageCopy
  bodyStorageCopyMemory bodyMemAssignTopCopyPaths
  fragGasSeqPtr fragGasSeqAbort fragGasOriginPtr fragGasOrigin
  ptrSafetyTransport instMemFrontier fragExecMem fragExec memSafeRun
  gasEvents gasCount ptrSafeRun ptrDiscipline bodyPtrDefs typedCopyPtr
  decoderGhostFramePtr exprLoweringProps venomMemProps
  venomExecSemantics venomExecProofs venomState venomInst
  words arithmetic list rich_list finite_map pred_set pair

(* ===== Generic pieces ===== *)

Theorem inst_seq_ptr_lower_bound_transport:
  !code s G tn G' tn'.
    lo0 <= lo /\ allocas_from lo s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
    inst_seq_ptr D lo0 ctx fn PG G tn code s G' tn' ==>
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (irule ptr_inst_ok_lower_bound_transport >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem run_inst_seq_allocas_from[local]:
  !code s t.
    allocas_from lo s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
    run_inst_seq code s = OK t ==>
    allocas_from lo t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >> qexists_tac `u` >> simp[] >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

(* A checked straight-line run without GAS, ALLOCA or calls, checked at the
   reserved bound 0, is a zero-mark joint path at any bound lo below every
   ALLOCA site. *)
Theorem run_inst_seq_origin_ptr_lift:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\ allocas_from lo s /\
  inst_seq_ptr D 0 ctx func PG G tn code s G' tn' /\
  run_inst_seq code s = OK t ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn') /\
  allocas_from lo t
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_MEM] >>
  reverse conj_tac >- metis_tac[run_inst_seq_allocas_from] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  `inst_seq_ptr D lo ctx func PG G tn code s G' tn'` by
    (irule inst_seq_ptr_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
     (MAP (\i. (func.fn_name, i.inst_id) IN explicit)
        (FILTER (\i. i.inst_opcode = GAS) code))
     (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),G',tn')` by
    (irule run_inst_seq_gas_origin_ptr_path >> metis_tac[]) >>
  gvs[]
QED

(* A jump checked at the reserved bound 0 is a zero-mark joint edge at lo. *)
Theorem copy_jump_origin_ptr:
  ~s.vs_halted /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  ptr_inst_ok D 0 0 ctx func G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     gvs[inst_dload_in_section_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)` by
    (simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, gas_count_step_def,
          mem_safe_step_non_invoke, ptr_safe_step_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem copy_jmp_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >> irule copy_jump_origin_ptr >> simp[] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, ptr_inst_ok_def, access_ok_def,
       taint_ok_def, allocas_from_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, jump_to_def, op_taint_def]
QED

Theorem origin_ptr_path_then[local]:
  gas_origin_ptr_path cx st [] (OK mid,G1,tn1) /\
  gas_origin_ptr_path cx (mid,G1,tn1) [] (r,G2,tn2) ==>
  gas_origin_ptr_path cx st [] (r,G2,tn2)
Proof
  strip_tac >>
  qpat_x_assum `gas_origin_ptr_path cx st _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >> simp[] >>
  disch_then drule >> simp[]
QED

(* The counted loop: the header either exits at the count or enters the
   body, and the body returns to the header one step further. *)
Theorem copy_loop_iterate_origin_ptr:
  !Inv cx (n:num) hdr loop_body exit remaining k G tn s.
  (!j G tn q. j <= n /\ Inv j G tn q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r G1 tn1. gas_origin_ptr_path cx (q,G,tn) [] (OK r,G1,tn1) /\
         Inv j G1 tn1 r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body)) /\
  (!j G tn q. j < n /\ Inv j G tn q /\ ~q.vs_halted /\
          q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r G1 tn1. gas_origin_ptr_path cx (q,G,tn) [] (OK r,G1,tn1) /\
         Inv (j+1) G1 tn1 r /\ ~r.vs_halted /\
         r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t Gf tnf. gas_origin_ptr_path cx (s,G,tn) [] (OK t,Gf,tnf) /\
      Inv n Gf tnf t /\ ~t.vs_halted /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  ntac 6 gen_tac >> Induct
  >- (rpt gen_tac >> strip_tac >>
      `k = n` by decide_tac >>
      qpat_x_assum `!j G tn q. j <= n /\ _ ==> _`
        (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl_tac [`r`, `G1`, `tn1`] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `k < n /\ k <= n /\ (k+1)+remaining = n` by decide_tac >>
  qpat_assum `!j G tn q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `G`, `tn`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`r`, `G1`, `tn1`] strip_assume_tac) >>
  qpat_assum `!j G tn q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `G1`, `tn1`, `r`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
  qpat_x_assum `!k G tn s. (_ /\ _ /\ k + remaining = n /\ _) ==> _`
    (qspecl_then [`k+1`, `G2`, `tn2`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >>
  metis_tac[origin_ptr_path_then]
QED

(* ===== Storage to memory ===== *)

Theorem storage_copy_init_origin_ptr[local]:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id ASSIGN [Lit 0w] [cv]; mk_inst (id+1) JMP [Label hdr] []] ==>
  !loc D explicit PG. ?t G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
     allocas_from lo t) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s = OK (update_var cv 0w s)` by
    simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst id ASSIGN [Lit 0w] [cv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst id ASSIGN [Lit 0w] [cv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by
    (`DROP (s.vs_inst_idx+1) bb.bb_instructions =
        [mk_inst (id+1) JMP [Label hdr] []]` by
       (`s.vs_inst_idx+1 <= LENGTH bb.bb_instructions` by
          (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
           simp[]) >>
        qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
        simp[rich_listTheory.DROP_DROP, arithmeticTheory.ADD_COMM]) >>
     `isPREFIX [mk_inst (id+1) JMP [Label hdr] []]
        (DROP (s.vs_inst_idx+1) bb.bb_instructions)` by simp[] >>
     drule instruction_prefix_cursor >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id ASSIGN [Lit 0w] [cv]` >>
  qabbrev_tac `u0 = update_var cv 0w s` >>
  qabbrev_tac `G1 = step_prov PG G i0 u0` >>
  qabbrev_tac `tn1 = step_taint i0 s u0 tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s = OK u0` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t0 = u0 with vs_inst_idx := s.vs_inst_idx + LENGTH [i0]` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t0,G1,tn1) []
     (OK (jump_to hdr t0),G1,tn1)` by
    (irule copy_jmp_origin_ptr >>
     simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  qexistsl_tac [`jump_to hdr t0`, `G1`, `tn1`] >>
  conj_tac >- metis_tac[origin_ptr_path_then] >>
  simp[Abbr `t0`, Abbr `u0`, Abbr `G1`, Abbr `tn1`, Abbr `i0`] >>
  rpt conj_tac
  >- (pure_rewrite_tac[GSYM update_var_def] >>
      irule toplevel_copy_init_inv >> simp[] >> metis_tac[])
  >- (gvs[allocas_from_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  simp[jump_to_def, update_var_def]
QED

Theorem storage_copy_header_origin_ptr[local]:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 r /\
     allocas_from lo r) /\
    ~r.vs_halted /\ r.vs_inst_idx = 0 /\
    r.vs_current_bb = (if k=n then exit_lbl else body_lbl)
Proof
  rpt strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_counter >> strip_tac >>
  `((n2w k):256 word = n2w n) <=> k=n` by
    (`k < 2**256` by decide_tac >>
     pure_rewrite_tac[n2w_11, dimword_def] >>
     gvs[arithmeticTheory.LESS_MOD]) >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s =
     OK (update_var tv (bool_to_word (k=n)) s)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def,
         eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `run_inst_seq_mem_ok [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id EQ [Var cv;Lit (n2w n)] [tv]` >>
  qabbrev_tac `u = update_var tv (bool_to_word (k=n)) s` >>
  qabbrev_tac `G1 = step_prov PG G i0 u` >>
  qabbrev_tac `tn1 = step_taint i0 s u tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s = OK u` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t = u with vs_inst_idx := s.vs_inst_idx + LENGTH [i0]` >>
  `toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 t` by
    (simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u`, Abbr `i0`] >>
     irule toplevel_copy_test_inv >> simp[] >> metis_tac[]) >>
  `op_taint tn1 (Var tv) = {}` by
    simp[Abbr `tn1`, Abbr `i0`, step_taint_def, set_var_taint_def, out_taint_def,
         mk_inst_def, op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ allocas_from lo t /\
    lookup_var tv t = SOME (bool_to_word (k=n))` by
    (simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t =
    OK (jump_to (if k=n then exit_lbl else body_lbl) t)` by
    (Cases_on `k=n` >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
    (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
     (OK (jump_to (if k=n then exit_lbl else body_lbl) t),G1,tn1)` by
    (irule copy_jump_origin_ptr >> simp[] >>
     qexistsl_tac [`bb`, `mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []`] >>
     simp[mk_inst_def] >> gvs[mk_inst_def]) >>
  qexistsl_tac [`jump_to (if k=n then exit_lbl else body_lbl) t`, `G1`, `tn1`] >>
  conj_tac >- (irule origin_ptr_path_then >> qexistsl_tac [`G1`, `t`, `tn1`] >>
               gvs[Abbr `t`]) >>
  gvs[jump_to_def, allocas_from_def] >> metis_tac[]
QED

Theorem storage_copy_body_origin_ptr[local]:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := s.vs_current_bb; bb_instructions :=
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var dst;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv];
       mk_inst (id+7) JMP [Label hdr] []]|> ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 (k+1) G1 tn1 r /\
     allocas_from lo r) /\
    ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  drule toplevel_copy_inv_source >> strip_tac >>
  drule toplevel_copy_inv_destination >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  `eval_operand (Var dst) s = SOME (n2w b) /\
   eval_operand (Var cv) s = SOME (n2w k)` by simp[eval_operand_def] >>
  qspecl_then [`if loc = LocStorage then SLOAD else TLOAD`, `src`, `Var dst`,
    `a`, `n2w b`, `cv`, `sv`, `vv`, `mv`, `dv`, `nv`, `id`, `s`, `n2w k`]
    mp_tac storage_copy_body_run >>
  (impl_tac >- (Cases_on `loc = LocStorage` >> gvs[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `r` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq _ s = OK r` mp_tac >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code s` >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all toplevel_copy_body_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `run_inst_seq_mem_ok code s` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     irule body_storage_iteration_mem_ok >> rpt conj_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[])
     >- gvs[]
     >- (qexistsl_tac [`b`, `k`] >> gvs[eval_operand_def, dimword_def]) >>
     gvs[]) >>
  `isPREFIX code (DROP s.vs_inst_idx
     (code ++ [mk_inst (id+7) JMP [Label hdr] []]))` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    (qpat_x_assum `code = _` SUBST1_TAC >>
     Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME
     <|bb_label := s.vs_current_bb;
       bb_instructions := code ++ [mk_inst (id+7) JMP [Label hdr] []]|>` by
    (qpat_x_assum `code = _` SUBST1_TAC >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (r with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tnf) /\
   allocas_from lo r` by
    (irule run_inst_seq_origin_ptr_lift >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `<|bb_label := s.vs_current_bb;
       bb_instructions := code ++ [mk_inst (id+7) JMP [Label hdr] []]|>` >>
     fs[]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) [] _` mp_tac >>
  asm_rewrite_tac[ADD_CLAUSES] >> strip_tac >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH code` >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 7 /\
   allocas_from lo t` by
    (simp[Abbr `t`] >> gvs[allocas_from_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gf,tnf) []
     (OK (jump_to hdr t),Gf,tnf)` by
    (irule copy_jmp_origin_ptr >> simp[] >>
     qexists_tac `id+7` >> simp[get_instruction_def] >>
     qpat_x_assum `code = _` SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`jump_to hdr t`, `Gf`, `tnf`] >>
  conj_tac >- (irule origin_ptr_path_then >> qexistsl_tac [`Gf`, `t`, `tnf`] >>
               gvs[Abbr `t`]) >>
  gvs[Abbr `t`, jump_to_def, allocas_from_def] >> metis_tac[]
QED

Theorem storage_copy_loop_origin_ptr:
  compile_word_copy_loop src (Var dst) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  not_fresh_at sa dst /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf cv ds.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    toplevel_copy_inv cv ds dst src loc a b n s G tn n Gf tnf t /\
    (!x. not_fresh_at sa x ==> ~MEM x ds) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_compile_blocks >> strip_tac >>
  drule_all toplevel_copy_layout_freshness >> strip_tac >>
  drule_all toplevel_copy_layout_lookups >> strip_tac >>
  drule_all toplevel_copy_compile_exit >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_blocks sa sb =
    [<|bb_label := loop_body; bb_instructions := body_code|>;
     <|bb_label := hdr; bb_instructions := hdr_code|>;
     <|bb_label := initial; bb_instructions := init_code|>]` >>
  `MEM cv [cv;tv;sv;vv;mv;dv;nv] /\ dst <> cv /\
   (!x. src = Var x ==> x <> cv)` by metis_tac[MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions =
     [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv];
      mk_inst (sa.cs_next_id+1) JMP [Label hdr] []]` by simp[] >>
  drule_all storage_copy_init_origin_ptr >>
  disch_then (qspecl_then [`loc`, `D`, `explicit`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t` >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `emitted_blocks _ _ = _` kall_tac >>
  qpat_x_assum `_ = GENLIST _ _` kall_tac >>
  `!j Gj tj q. j <= n /\
     (toplevel_copy_inv cv ds dst src loc a b n s G tn j Gj tj q /\
      allocas_from lo q) /\
     ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) []
         (OK r,Gr,tr) /\
       (toplevel_copy_inv cv ds dst src loc a b n s G tn j Gr tr r /\
        allocas_from lo r) /\
       ~r.vs_halted /\ r.vs_inst_idx = 0 /\
       r.vs_current_bb = (if j=n then exit else loop_body)` by
    (rpt strip_tac >>
     `cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds` by
       (simp[Abbr `ds`] >> metis_tac[MEM, ALL_DISTINCT]) >>
     `isPREFIX [mk_inst (sa.cs_next_id+2) EQ [Var cv;Lit (n2w n)] [tv];
        mk_inst ((sa.cs_next_id+2)+1) JNZ [Var tv;Label exit;Label loop_body] []]
        (DROP q.vs_inst_idx
          <|bb_label := hdr; bb_instructions := hdr_code|>.bb_instructions)` by
       simp[Abbr `hdr_code`] >>
     `lookup_block q.vs_current_bb func.fn_blocks =
        SOME <|bb_label := hdr; bb_instructions := hdr_code|>` by metis_tac[] >>
     drule storage_copy_header_origin_ptr >> disch_then drule_all >>
     disch_then (qspecl_then [`D`, `explicit`, `PG`] strip_assume_tac) >>
     metis_tac[]) >>
  `!j Gj tj q. j < n /\
     (toplevel_copy_inv cv ds dst src loc a b n s G tn j Gj tj q /\
      allocas_from lo q) /\
     ~q.vs_halted /\ q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) []
         (OK r,Gr,tr) /\
       (toplevel_copy_inv cv ds dst src loc a b n s G tn (j+1) Gr tr r /\
        allocas_from lo r) /\
       ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (rpt strip_tac >>
     `ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
      EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
      ~MEM dst [cv;sv;vv;mv;dv;nv] /\
      (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv])` by
       (qpat_x_assum `ALL_DISTINCT ds` mp_tac >>
        qpat_x_assum `~MEM dst ds` mp_tac >>
        qpat_x_assum `!x. src = Var x ==> ~MEM x ds` mp_tac >>
        unabbrev_all_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[ALL_DISTINCT] >> metis_tac[]) >>
     `lookup_block q.vs_current_bb func.fn_blocks = SOME
        <|bb_label := q.vs_current_bb; bb_instructions :=
          [mk_inst (sa.cs_next_id+4) ADD [src;Var cv] [sv];
           mk_inst ((sa.cs_next_id+4)+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
           mk_inst ((sa.cs_next_id+4)+2) MUL [Var cv;Lit 32w] [mv];
           mk_inst ((sa.cs_next_id+4)+3) ADD [Var dst;Var mv] [dv];
           mk_inst ((sa.cs_next_id+4)+4) MSTORE [Var dv;Var vv] [];
           mk_inst ((sa.cs_next_id+4)+5) ADD [Var cv;Lit 1w] [nv];
           mk_inst ((sa.cs_next_id+4)+6) ASSIGN [Var nv] [cv];
           mk_inst ((sa.cs_next_id+4)+7) JMP [Label hdr] []]|>` by
       (simp[Abbr `body_code`] >> metis_tac[]) >>
     drule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _|>`)
       storage_copy_body_origin_ptr >>
     disch_then drule_all >>
     disch_then (qspecl_then [`D`, `explicit`, `PG`] strip_assume_tac) >>
     metis_tac[]) >>
  qspecl_then [`\j Gj tj q. toplevel_copy_inv cv ds dst src loc a b n s G tn j Gj tj q /\
                            allocas_from lo q`,
               `(D,lo,explicit,ctx,func,PG)`, `n`, `hdr`, `loop_body`, `exit`,
               `n`, `0`, `G1`, `tn1`, `t`] mp_tac copy_loop_iterate_origin_ptr >>
  BETA_TAC >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  disch_then (qx_choosel_then [`t2`, `Gf`, `tnf`] strip_assume_tac) >>
  qexistsl_tac [`t2`, `Gf`, `tnf`, `cv`, `ds`] >> simp[] >>
  metis_tac[origin_ptr_path_then]
QED

(* ===== Memory to storage ===== *)

Theorem copy_store_step_ptr[local]:
  (opc = SSTORE \/ opc = TSTORE) /\ ~s.vs_call_ctx.cc_static /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME w /\
  op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
  ?z. step_inst_base (mk_inst id opc [a; v] []) s = OK z /\
      z.vs_vars = s.vs_vars /\ z.vs_allocas = s.vs_allocas /\
      z.vs_fmp = s.vs_fmp /\
      !D fuel fn G. ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a; v] []) s
Proof
  strip_tac >>
  `?z. step_inst_base (mk_inst id opc [a; v] []) s = OK z /\
       z.vs_vars = s.vs_vars /\ z.vs_allocas = s.vs_allocas /\ z.vs_fmp = s.vs_fmp` by
    (gvs[] >>
     simp[stepInstBaseLib.simp_opcode_clause ``SSTORE``,
          stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def,
          exec_write2_def, sstore_def, tstore_def]) >>
  qexists_tac `z` >> simp[] >> rpt gen_tac >>
  irule assign_base_ptr_inst_ok_storage_word >> gvs[]
QED

(* The comparison and the load write no memory, storage or immutables. *)
Theorem copy_register_taint_frame[local]:
  MEM inst.inst_opcode [EQ; MLOAD] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint inst s t tn).t_mem = tn.t_mem /\
  (step_taint inst s t tn).t_stor = tn.t_stor /\
  (step_taint inst s t tn).t_trans = tn.t_trans /\
  (step_taint inst s t tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = h::ops` >>
  Cases_on `ops` >> simp[] >>
  rename1 `inst.inst_operands = h::h1::ops1` >>
  Cases_on `ops1` >> simp[] >>
  rename1 `inst.inst_operands = h::h1::h2::ops2` >>
  Cases_on `ops2` >> simp[]
QED

Theorem copy_store_taint_bound_step[local]:
  X SUBSET (T0 DIFF {(k + n2w i, j) | (i,j) | i < m}) UNION
           {(k + n2w i, j) | (i,j) | i < m /\ j < 32 /\ c + 32*i + j IN M} ==>
  key_update X (k + n2w m) (mem_word_taint M (c + 32*m)) SUBSET
    (T0 DIFF {(k + n2w i, j) | (i,j) | i < m + 1}) UNION
    {(k + n2w i, j) | (i,j) | i < m + 1 /\ j < 32 /\ c + 32*i + j IN M}
Proof
  simp[SUBSET_DEF, key_update_def, mem_word_taint_def, PULL_EXISTS,
       FORALL_PROD] >>
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> rpt strip_tac >> gvs[] >>
          `i < m \/ i = m` by decide_tac >> gvs[] >> metis_tac[])
      >> disj2_tac >> qexists_tac `i` >> simp[])
  >> disj2_tac >> qexists_tac `m` >> simp[]
QED

(* The pointer check and ghost of one memory-to-storage iteration: the
   source offset stays inside the source pointer's region, the stored
   slot takes the loaded word's memory taint, and nothing else changes. *)
Theorem memory_copy_body_ptr[local]:
  !loc ctx cv mv sv vv dv nv x dst G tn s n b k i.
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\ ~MEM x [cv;mv;sv;vv;dv;nv] /\
  (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ lookup_var x s = SOME b /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w i) /\ op_taint tn (Var cv) = {} /\
  i < n /\ w2n b + 32*n < dimword (:256) /\ ~s.vs_call_ctx.cc_static ==>
  !id D fn PG. ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+1) ADD [Var x;Var mv] [sv];
       mk_inst (id+2) MLOAD [Var sv] [vv];
       mk_inst (id+3) ADD [dst;Var cv] [dv];
       mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
         [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s Gf tnf /\
    op_taint tnf (Var cv) = {} /\
    (!y. ~MEM y [cv;mv;sv;vv;dv;nv] ==>
         FLOOKUP Gf y = FLOOKUP G y /\
         op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans
     else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      key_update (toplevel_copy_source_taint loc tn) (k + n2w i)
        (mem_word_taint tn.t_mem (w2n b + 32*i))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `x <> cv /\ x <> mv /\ x <> sv /\ x <> vv /\ x <> dv /\ x <> nv /\
   cv <> mv /\ cv <> sv /\ cv <> vv /\ cv <> dv /\ cv <> nv /\
   mv <> sv /\ mv <> vv /\ mv <> dv /\ mv <> nv /\
   sv <> vv /\ sv <> dv /\ sv <> nv /\ vv <> dv /\ vv <> nv /\ dv <> nv` by
    gvs[] >>
  `w2n (b + n2w (32*i)) = w2n b + 32*i` by
    (`w2n b + 32*i < dimword (:256)` by decide_tac >>
     Cases_on `b` >> gvs[word_add_n2w] >> decide_tac) >>
  (* MUL [cv; 32] -> mv *)
  qabbrev_tac `i1 = mk_inst id MUL [Var cv;Lit 32w] [mv]` >>
  qabbrev_tac `u = update_var mv (n2w (32*i)) s` >>
  `step_inst_base i1 s = OK u` by
    (simp[Abbr `i1`, Abbr `u`, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operands_def] >>
     simp[NoAsms, eval_operand_def, word_mul_n2w]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i1 s` by
    (simp[Abbr `i1`] >> irule toplevel_copy_ptr_inst_ok_mul >> simp[]) >>
  qabbrev_tac `G1 = step_prov PG G i1 u` >>
  qabbrev_tac `tn1 = step_taint i1 s u tn` >>
  qabbrev_tac `u1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp[Abbr `tn1`] >> irule toplevel_copy_register_taint_frame >>
     simp[Abbr `i1`, Abbr `u`, mk_inst_def, update_var_def]) >>
  `op_taint tn1 (Var mv) = {}` by
    simp[Abbr `tn1`, Abbr `i1`, toplevel_counter_offset_ghost] >>
  `ptr_covers G1 tn1 x u1 (32*n)` by
    (`ptr_covers G1 tn1 x u (32*n)` by
       (simp[Abbr `G1`, Abbr `tn1`] >> irule ptr_covers_step_frame >>
        simp[Abbr `i1`, Abbr `u`, mk_inst_def, lookup_var_update_var]) >>
     gvs[Abbr `u1`, ptr_covers_def, lookup_var_def]) >>
  `lookup_var x u1 = SOME b /\ eval_operand (Var x) u1 = SOME b /\
   eval_operand (Var mv) u1 = SOME (n2w (32*i))` by
    (simp[Abbr `u1`, Abbr `u`, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  (* ADD [x; mv] -> sv *)
  qabbrev_tac `i2 = mk_inst (id+1) ADD [Var x;Var mv] [sv]` >>
  qabbrev_tac `v = update_var sv (b + n2w (32*i)) u1` >>
  `step_inst_base i2 u1 = OK v` by
    (simp[Abbr `i2`, Abbr `v`] >> irule step_ADD >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 i2 u1` by
    (simp[Abbr `i2`] >> irule ptr_inst_ok_copy_len_binop >>
     gvs[ptr_covers_def]) >>
  qabbrev_tac `G2 = step_prov PG G1 i2 v` >>
  qabbrev_tac `tn2 = step_taint i2 u1 v tn1` >>
  qabbrev_tac `v1 = v with vs_inst_idx := SUC u1.vs_inst_idx` >>
  `tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (mp_tac (Q.INST [`inst` |-> `i2`, `s` |-> `u1`, `t` |-> `v`,
       `tn` |-> `tn1`] toplevel_copy_register_taint_frame) >>
     impl_tac >- simp[Abbr `i2`, Abbr `v`, mk_inst_def, update_var_def] >>
     strip_tac >> fs[Abbr `tn2`]) >>
  `ptr_covers G2 tn2 sv v1 32` by
    (`ptr_covers G2 tn2 sv v 32` by
       (simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `v`] >>
        irule toplevel_destination_offset_covers >>
        conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `n` >> fs[]) >>
     gvs[Abbr `v1`, ptr_covers_def, lookup_var_def]) >>
  `eval_operand (Var sv) v1 = SOME (b + n2w (32*i))` by
    simp[Abbr `v1`, Abbr `v`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  (* MLOAD [sv] -> vv *)
  qabbrev_tac `i3 = mk_inst (id+2) MLOAD [Var sv] [vv]` >>
  qabbrev_tac `w = update_var vv (mload (w2n (b + n2w (32*i))) v1) v1` >>
  `step_inst_base i3 v1 = OK w` by
    simp[Abbr `i3`, Abbr `w`, stepInstBaseLib.simp_opcode_clause ``MLOAD``,
         mk_inst_def, exec_read1_def] >>
  `ptr_inst_ok D 0 0 ctx fn G2 tn2 i3 v1` by
    (simp[Abbr `i3`] >> irule ptr_inst_ok_mload >> simp[]) >>
  qabbrev_tac `G3 = step_prov PG G2 i3 w` >>
  qabbrev_tac `tn3 = step_taint i3 v1 w tn2` >>
  qabbrev_tac `w1 = w with vs_inst_idx := SUC v1.vs_inst_idx` >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (mp_tac (Q.INST [`inst` |-> `i3`, `s` |-> `v1`, `t` |-> `w`,
       `tn` |-> `tn2`] copy_register_taint_frame) >>
     impl_tac >- simp[Abbr `i3`, Abbr `w`, Abbr `v1`, mk_inst_def, update_var_def] >>
     strip_tac >> fs[Abbr `tn3`]) >>
  `op_taint tn3 (Var vv) = mem_word_taint tn.t_mem (w2n b + 32*i)` by
    simp[Abbr `tn3`, Abbr `i3`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE] >>
  (* ADD [dst; cv] -> dv *)
  `eval_operand dst w1 = SOME k /\ op_taint tn3 dst = {}` by
    (Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`, Abbr `u1`, Abbr `u`,
         Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
         step_taint_other_output, mk_inst_def] >>
     simp[op_taint_def]) >>
  `eval_operand (Var cv) w1 = SOME (n2w i) /\ op_taint tn3 (Var cv) = {}` by
    (simp[Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`, Abbr `u1`, Abbr `u`,
          Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          step_taint_other_output, mk_inst_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `i4 = mk_inst (id+3) ADD [dst;Var cv] [dv]` >>
  qabbrev_tac `y0 = update_var dv (k + n2w i) w1` >>
  `step_inst_base i4 w1 = OK y0` by
    (simp[Abbr `i4`, Abbr `y0`] >> irule step_ADD >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G3 tn3 i4 w1` by
    (simp[Abbr `i4`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  qabbrev_tac `G4 = step_prov PG G3 i4 y0` >>
  qabbrev_tac `tn4 = step_taint i4 w1 y0 tn3` >>
  qabbrev_tac `y1 = y0 with vs_inst_idx := SUC w1.vs_inst_idx` >>
  `tn4.t_mem = tn3.t_mem /\ tn4.t_stor = tn3.t_stor /\
   tn4.t_trans = tn3.t_trans /\ tn4.t_imm = tn3.t_imm` by
    (mp_tac (Q.INST [`inst` |-> `i4`, `s` |-> `w1`, `t` |-> `y0`,
       `tn` |-> `tn3`] toplevel_copy_register_taint_frame) >>
     impl_tac >- simp[Abbr `i4`, Abbr `y0`, mk_inst_def, update_var_def] >>
     strip_tac >> fs[Abbr `tn4`]) >>
  `op_taint tn4 (Var dv) = {}` by
    (simp[Abbr `tn4`, Abbr `i4`] >> irule toplevel_copy_source_add_clean >>
     simp[]) >>
  `op_taint tn4 (Var vv) = mem_word_taint tn.t_mem (w2n b + 32*i) /\
   op_taint tn4 (Var cv) = {}` by
    simp[Abbr `tn4`, Abbr `i4`, step_taint_other_output, mk_inst_def] >>
  (* SSTORE/TSTORE [dv; vv] *)
  qabbrev_tac `i5 = mk_inst (id+4)
    (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []` >>
  `eval_operand (Var dv) y1 = SOME (k + n2w i) /\
   eval_operand (Var vv) y1 = SOME (mload (w2n (b + n2w (32*i))) v1) /\
   ~y1.vs_call_ctx.cc_static` by
    simp[Abbr `y1`, Abbr `y0`, Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`,
         Abbr `u1`, Abbr `u`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `?z. step_inst_base i5 y1 = OK z /\
       z.vs_vars = y1.vs_vars /\ z.vs_allocas = y1.vs_allocas /\
       z.vs_fmp = y1.vs_fmp /\
       !D fuel fn G. ptr_inst_ok D 0 fuel ctx fn G tn4 i5 y1` by
    (simp[Abbr `i5`] >> irule copy_store_step_ptr >> rw[] >> fs[] >>
     metis_tac[]) >>
  qabbrev_tac `G5 = step_prov PG G4 i5 z` >>
  qabbrev_tac `tn5 = step_taint i5 y1 z tn4` >>
  qabbrev_tac `z1 = z with vs_inst_idx := SUC y1.vs_inst_idx` >>
  `op_taint tn5 (Var cv) = {}` by
    simp[Abbr `tn5`, Abbr `i5`, step_taint_other_output, mk_inst_def] >>
  `tn5.t_mem = tn4.t_mem /\ tn5.t_imm = tn4.t_imm /\
   (if loc = LocStorage then tn5.t_trans = tn4.t_trans
    else tn5.t_stor = tn4.t_stor) /\
   toplevel_copy_source_taint loc tn5 =
     key_update (toplevel_copy_source_taint loc tn4) (k + n2w i)
       (mem_word_taint tn.t_mem (w2n b + 32*i))` by
    (`tn5 = if loc = LocStorage
            then tn4 with t_stor := key_update tn4.t_stor (k + n2w i)
                   (op_taint tn4 (Var vv))
            else tn4 with t_trans := key_update tn4.t_trans (k + n2w i)
                   (op_taint tn4 (Var vv))` by
       (qunabbrev_tac `tn5` >> qunabbrev_tac `i5` >>
        qspecl_then [`if loc = LocStorage then SSTORE else TSTORE`, `id+4`,
          `Var dv`, `Var vv`, `y1`, `z`, `PG`, `G4`, `tn4`, `k + n2w i`]
          mp_tac assign_base_storage_word_ghost >>
        Cases_on `loc = LocStorage` >> simp[]) >>
     Cases_on `loc = LocStorage` >> gvs[toplevel_copy_source_taint_def]) >>
  (* ADD [cv; 1] -> nv *)
  `eval_operand (Var cv) z1 = SOME (n2w i)` by
    (simp[Abbr `z1`, eval_operand_def, lookup_var_def] >>
     gvs[Abbr `y1`, Abbr `y0`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `i6 = mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]` >>
  qabbrev_tac `h = update_var nv (n2w i + 1w) z1` >>
  `step_inst_base i6 z1 = OK h` by
    (simp[Abbr `i6`, Abbr `h`] >> irule step_ADD >> simp[eval_operand_lit]) >>
  `ptr_inst_ok D 0 0 ctx fn G5 tn5 i6 z1` by
    (simp[Abbr `i6`] >> irule ptr_inst_ok_copy_len_binop >> simp[] >>
     simp[op_taint_def]) >>
  qabbrev_tac `G6 = step_prov PG G5 i6 h` >>
  qabbrev_tac `tn6 = step_taint i6 z1 h tn5` >>
  qabbrev_tac `h1 = h with vs_inst_idx := SUC z1.vs_inst_idx` >>
  `tn6.t_mem = tn5.t_mem /\ tn6.t_stor = tn5.t_stor /\
   tn6.t_trans = tn5.t_trans /\ tn6.t_imm = tn5.t_imm` by
    (mp_tac (Q.INST [`inst` |-> `i6`, `s` |-> `z1`, `t` |-> `h`,
       `tn` |-> `tn5`] toplevel_copy_register_taint_frame) >>
     impl_tac >- simp[Abbr `i6`, Abbr `h`, Abbr `z1`, mk_inst_def, update_var_def] >>
     strip_tac >> fs[Abbr `tn6`]) >>
  `op_taint tn6 (Var nv) = {}` by
    simp[Abbr `tn6`, Abbr `i6`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE] >>
  (* ASSIGN [nv] -> cv *)
  qabbrev_tac `i7 = mk_inst (id+6) ASSIGN [Var nv] [cv]` >>
  qabbrev_tac `t = update_var cv (n2w i + 1w) h1` >>
  `step_inst_base i7 h1 = OK t` by
    simp[Abbr `i7`, Abbr `t`, Abbr `h1`, Abbr `h`, step_inst_base_def,
         mk_inst_def, exec_read1_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn G6 tn6 i7 h1` by
    (simp[Abbr `i7`] >> irule toplevel_copy_ptr_inst_ok_assign >> simp[]) >>
  qabbrev_tac `G7 = step_prov PG G6 i7 t` >>
  qabbrev_tac `tn7 = step_taint i7 h1 t tn6` >>
  `tn7.t_mem = tn6.t_mem /\ tn7.t_stor = tn6.t_stor /\
   tn7.t_trans = tn6.t_trans /\ tn7.t_imm = tn6.t_imm` by
    (mp_tac (Q.INST [`inst` |-> `i7`, `s` |-> `h1`, `t` |-> `t`,
       `tn` |-> `tn6`] toplevel_copy_register_taint_frame) >>
     impl_tac >- simp[Abbr `i7`, Abbr `t`, Abbr `h1`, mk_inst_def, update_var_def] >>
     strip_tac >> fs[Abbr `tn7`]) >>
  `op_taint tn7 (Var cv) = {}` by
    (simp[Abbr `tn7`, Abbr `i7`, step_taint_def, set_var_taint_def,
          out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `eval_operand (Var nv) h1` >> gvs[op_taint_def]) >>
  `!y. ~MEM y [cv;mv;sv;vv;dv;nv] ==>
       FLOOKUP G7 y = FLOOKUP G y /\
       op_taint tn7 (Var y) = op_taint tn (Var y)` by
    (rpt gen_tac >> strip_tac >> fs[] >>
     simp[Abbr `G7`, Abbr `G6`, Abbr `G5`, Abbr `G4`, Abbr `G3`, Abbr `G2`,
          Abbr `G1`, Abbr `tn7`, Abbr `tn6`, Abbr `tn5`, Abbr `tn4`,
          Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
          Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`, Abbr `i5`, Abbr `i6`,
          Abbr `i7`, step_prov_other_output, step_taint_other_output,
          mk_inst_def]) >>
  qexistsl_tac [`G7`, `tn7`] >>
  (conj_tac
  >- (fs[Abbr `G7`, Abbr `tn7`, Abbr `G6`, Abbr `tn6`,
        Abbr `G5`, Abbr `tn5`, Abbr `G4`, Abbr `tn4`,
        Abbr `G3`, Abbr `tn3`, Abbr `G2`, Abbr `tn2`, Abbr `G1`, Abbr `tn1`,
        Abbr `h1`, Abbr `z1`, Abbr `y1`, Abbr `w1`, Abbr `v1`, Abbr `u1`,
        inst_seq_ptr_def]) >>
  simp[] >>
  Cases_on `loc = LocStorage` >> gvs[toplevel_copy_source_taint_def])
QED

(* The pieces the two loop directions share: the counter's initialisation
   and the header's test and branch. *)
Theorem copy_init_origin_ptr[local]:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+1) =
    SOME (mk_inst (id+1) JMP [Label hdr] []) ==>
  !D explicit PG G tn.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to hdr
           (update_var cv 0w s with vs_inst_idx := s.vs_inst_idx + 1)),
     step_prov PG G (mk_inst id ASSIGN [Lit 0w] [cv]) (update_var cv 0w s),
     step_taint (mk_inst id ASSIGN [Lit 0w] [cv]) s (update_var cv 0w s) tn)
Proof
  strip_tac >> rpt gen_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s =
     OK (update_var cv 0w s)` by
    simp[stepInstBaseLib.simp_opcode_clause ``ASSIGN``, mk_inst_def,
         eval_operand_lit] >>
  `ptr_inst_ok D 0 0 ctx func G tn (mk_inst id ASSIGN [Lit 0w] [cv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst id ASSIGN [Lit 0w] [cv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id ASSIGN [Lit 0w] [cv]` >>
  qabbrev_tac `u0 = update_var cv 0w s` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s
     (step_prov PG G i0 u0) (step_taint i0 s u0 tn)` by
    simp[inst_seq_ptr_def] >>
  `run_inst_seq [i0] s = OK u0` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t0 = u0 with vs_inst_idx := s.vs_inst_idx + 1` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK t0,step_prov PG G i0 u0,step_taint i0 s u0 tn)` by
    fs[Abbr `t0`] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (t0,step_prov PG G i0 u0,step_taint i0 s u0 tn) []
     (OK (jump_to hdr t0),step_prov PG G i0 u0,step_taint i0 s u0 tn)` by
    (irule copy_jmp_origin_ptr >> simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  metis_tac[origin_ptr_path_then]
QED

Theorem copy_header_origin_ptr[local]:
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand (Var cv) s = SOME (n2w m) /\ op_taint tn (Var cv) = {} /\
  m < dimword (:256) /\ n < dimword (:256) /\ cv <> tv /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted ==>
  !D explicit PG G.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if m = n then exit_lbl else body_lbl)
           (update_var tv (bool_to_word (m = n)) s with
              vs_inst_idx := SUC s.vs_inst_idx)),
     step_prov PG G (mk_inst id EQ [Var cv;Lit (n2w n)] [tv])
       (update_var tv (bool_to_word (m = n)) s),
     step_taint (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s
       (update_var tv (bool_to_word (m = n)) s) tn)
Proof
  strip_tac >> rpt gen_tac >>
  `((n2w m):bytes32 = n2w n) <=> (m = n)` by simp[n2w_11, LESS_MOD] >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s =
     OK (update_var tv (bool_to_word (m = n)) s)` by
    (qpat_assum `(n2w m = n2w n) <=> (m = n)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> simp[eval_operand_lit]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `run_inst_seq_mem_ok [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id EQ [Var cv;Lit (n2w n)] [tv]` >>
  qabbrev_tac `u = update_var tv (bool_to_word (m = n)) s` >>
  qabbrev_tac `G1 = step_prov PG G i0 u` >>
  qabbrev_tac `tn1 = step_taint i0 s u tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s = OK u` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK t,G1,tn1)` by fs[Abbr `t`, ADD1] >>
  `op_taint tn1 (Var tv) = {}` by
    simp[Abbr `tn1`, Abbr `i0`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
         eval_operand_def] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ allocas_from lo t /\
    lookup_var tv t = SOME (bool_to_word (m = n))` by
    (simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t =
    OK (jump_to (if m = n then exit_lbl else body_lbl) t)` by
    (Cases_on `m = n` >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
    (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
     (OK (jump_to (if m = n then exit_lbl else body_lbl) t),G1,tn1)` by
    (irule copy_jump_origin_ptr >> simp[] >>
     qexistsl_tac [`bb`,
       `mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []`] >>
     simp[mk_inst_def] >> gvs[mk_inst_def]) >>
  metis_tac[origin_ptr_path_then]
QED

Theorem memory_copy_loop_origin_ptr:
  compile_word_copy_loop (Var x) dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  lookup_var x s = SOME b /\ ptr_covers G tn x s (32*n) /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  n < dimword(:256) /\ w2n b + 32*n < dimword(:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
                               op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf SUBSET
      (toplevel_copy_source_taint loc tn DIFF {(k + n2w i, j) | (i,j) | i < n}) UNION
      {(k + n2w i, j) | (i,j) | i < n /\ j < 32 /\ w2n b + 32*i + j IN tn.t_mem}
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_code_certificate >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fn_has_code _ _ _`] >>
  `!y. not_fresh_at sa y ==>
       y <> cv /\ y <> tv /\ y <> mv /\ y <> sv /\ y <> vv /\ y <> dv /\
       y <> nv` by (fs[] >> metis_tac[]) >>
  `x <> cv /\ x <> tv /\ x <> mv /\ x <> sv /\ x <> vv /\ x <> dv /\
   x <> nv` by metis_tac[] >>
  `cv <> tv /\ ALL_DISTINCT [cv;mv;sv;vv;dv;nv]` by fs[ALL_DISTINCT] >>
  qabbrev_tac `Inv = \m Gm tm q.
    store_copy_frame sa loc b k s m q /\
    eval_operand (Var cv) q = SOME (n2w m) /\
    op_taint tm (Var cv) = {} /\ allocas_from lo q /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gm y = FLOOKUP G y /\
                               op_taint tm (Var y) = op_taint tn (Var y)) /\
    tm.t_mem = tn.t_mem /\ tm.t_imm = tn.t_imm /\
    (if loc = LocStorage then tm.t_trans = tn.t_trans
     else tm.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tm SUBSET
      (toplevel_copy_source_taint loc tn DIFF
         {(k + n2w i, j) | (i,j) | i < m}) UNION
      {(k + n2w i, j) | (i,j) | i < m /\ j < 32 /\
                        w2n b + 32*i + j IN tn.t_mem}` >>
  (* the header: test the counter and branch *)
  `!j Gj tj q. j <= n /\ Inv j Gj tj q /\ ~q.vs_halted /\
     q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) []
         (OK r,Gr,tr) /\ Inv j Gr tr r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
       r.vs_current_bb = (if j = n then exit else loop_body)` by
    (qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
     `j < dimword (:256)` by decide_tac >>
     `isPREFIX [mk_inst hi EQ [Var cv;Lit (n2w n)] [tv];
        mk_inst (hi+1) JNZ [Var tv;Label exit;Label loop_body] []]
        (DROP q.vs_inst_idx hbb.bb_instructions)` by
       (irule topcopy_instruction_prefix >> simp[]) >>
     `lookup_block q.vs_current_bb func.fn_blocks = SOME hbb` by simp[] >>
     drule_all copy_header_origin_ptr >>
     disch_then (qspecl_then [`D`, `explicit`, `PG`, `Gj`] assume_tac) >>
     qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK r,Gr,tr)` >>
     `tr.t_mem = tj.t_mem /\ tr.t_stor = tj.t_stor /\
      tr.t_trans = tj.t_trans /\ tr.t_imm = tj.t_imm` by
       (simp[Abbr `tr`] >>
        qmatch_goalsub_abbrev_tac `step_taint ii ss tt tj` >>
        mp_tac (Q.INST [`inst` |-> `ii`, `s` |-> `ss`, `t` |-> `tt`,
                        `tn` |-> `tj`] copy_register_taint_frame) >>
        impl_tac >- simp[Abbr `ii`, Abbr `tt`, mk_inst_def, update_var_def] >>
        strip_tac >> fs[]) >>
     `!y. y <> tv ==> FLOOKUP Gr y = FLOOKUP Gj y /\
                      op_taint tr (Var y) = op_taint tj (Var y)` by
       simp[Abbr `Gr`, Abbr `tr`, step_prov_other_output,
            step_taint_other_output, mk_inst_def] >>
     `toplevel_copy_source_taint loc tr = toplevel_copy_source_taint loc tj` by
       simp[toplevel_copy_source_taint_def] >>
     `store_copy_frame sa loc b k s j r` by
       (simp[Abbr `r`] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
     `!y. not_fresh_at sa y ==> FLOOKUP Gr y = FLOOKUP G y /\
                                op_taint tr (Var y) = op_taint tn (Var y)` by
       metis_tac[] >>
     `op_taint tr (Var cv) = {}` by metis_tac[] >>
     `(if loc = LocStorage then tr.t_trans = tn.t_trans
       else tr.t_stor = tn.t_stor)` by (Cases_on `loc = LocStorage` >> gvs[]) >>
     `r.vs_allocas = q.vs_allocas /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if j = n then exit else loop_body) /\
      lookup_var cv r = lookup_var cv q` by
       (simp[Abbr `r`, jump_to_def, update_var_def, lookup_var_def,
             FLOOKUP_UPDATE] >> rw[]) >>
     `allocas_from lo r` by
       (qpat_x_assum `allocas_from lo q` mp_tac >>
        qpat_x_assum `r.vs_allocas = _` (fn th => simp[allocas_from_def, th])) >>
     `eval_operand (Var cv) r = SOME (n2w j)` by
       (qpat_x_assum `eval_operand (Var cv) q = _` mp_tac >>
        qpat_x_assum `lookup_var cv r = _` (fn th => simp[eval_operand_def, th])) >>
     `tr.t_mem = tn.t_mem /\ tr.t_imm = tn.t_imm` by metis_tac[] >>
     qexistsl_tac [`r`, `Gr`, `tr`] >>
     qpat_x_assum `toplevel_copy_source_taint loc tr = _`
       (fn th => REWRITE_TAC [th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* the body and the jump back to the header *)
  `!j Gj tj q. j < n /\ Inv j Gj tj q /\ ~q.vs_halted /\
     q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) []
         (OK r,Gr,tr) /\ Inv (j+1) Gr tr r /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (qpat_x_assum `!j Gj tj q. j <= n /\ _ ==> _` kall_tac >>
     qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
     `eval_operand (Var x) s = SOME b` by simp[eval_operand_def] >>
     `!y. Var x = Var y \/ dst = Var y ==> not_fresh_at sa y` by
       (rpt strip_tac >> gvs[]) >>
     `!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]` by
       (simp[] >> metis_tac[]) >>
     qspecl_then [`sa`, `loc`, `b`, `k`, `s`, `j`, `q`, `Var x`, `dst`, `cv`,
                  `mv`, `sv`, `vv`, `dv`, `nv`, `bi`] mp_tac topcopy_body_run >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
     disch_then (qx_choose_then `r0` strip_assume_tac) >>
     `lookup_var x q = lookup_var x s` by fs[store_copy_frame_def] >>
     `lookup_var x q = SOME b /\ eval_operand (Var x) q = SOME b` by
       gvs[eval_operand_def] >>
     `q.vs_alloca_next = s.vs_alloca_next` by
       metis_tac[topcopy_frame_frontier] >>
     `w2n b + 32*(j+1) <= q.vs_alloca_next` by decide_tac >>
     `eval_operand dst q = SOME k` by
       (irule topcopy_frame_operand >> metis_tac[]) >>
     `~q.vs_call_ctx.cc_static` by metis_tac[topcopy_frame_call_ctx] >>
     `ptr_covers Gj tj x q (32*n)` by metis_tac[ptr_covers_frame] >>
     `op_taint tj dst = {}` by
       (Cases_on `dst` >> gvs[] >> simp[op_taint_def]) >>
     `~MEM x [cv;mv;sv;vv;dv;nv] /\
      (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv])` by
       (simp[] >> metis_tac[]) >>
     qspecl_then [`loc`, `ctx`, `cv`, `mv`, `sv`, `vv`, `dv`, `nv`, `x`, `dst`,
                  `Gj`, `tj`, `q`, `n`, `b`, `k`, `j`] mp_tac
       memory_copy_body_ptr >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
     disch_then (qspecl_then [`bi`, `D`, `func`, `PG`] strip_assume_tac) >>
     `run_inst_seq_mem_ok
        [mk_inst bi MUL [Var cv;Lit 32w] [mv];
         mk_inst (bi+1) ADD [Var x;Var mv] [sv];
         mk_inst (bi+2) MLOAD [Var sv] [vv];
         mk_inst (bi+3) ADD [dst;Var cv] [dv];
         mk_inst (bi+4) (if loc = LocStorage then SSTORE else TSTORE)
           [Var dv;Var vv] [];
         mk_inst (bi+5) ADD [Var cv;Lit 1w] [nv];
         mk_inst (bi+6) ASSIGN [Var nv] [cv]] q` by
       (irule body_mem_storage_iteration_mem_ok_modular >> simp[] >>
        qexists_tac `j` >> `j < dimword (:256)` by decide_tac >> fs[]) >>
     `isPREFIX
        [mk_inst bi MUL [Var cv;Lit 32w] [mv];
         mk_inst (bi+1) ADD [Var x;Var mv] [sv];
         mk_inst (bi+2) MLOAD [Var sv] [vv];
         mk_inst (bi+3) ADD [dst;Var cv] [dv];
         mk_inst (bi+4) (if loc = LocStorage then SSTORE else TSTORE)
           [Var dv;Var vv] [];
         mk_inst (bi+5) ADD [Var cv;Lit 1w] [nv];
         mk_inst (bi+6) ASSIGN [Var nv] [cv]]
        (DROP q.vs_inst_idx bbb.bb_instructions)` by
       (irule isPREFIX_TRANS >>
        qexists_tac `[mk_inst bi MUL [Var cv;Lit 32w] [mv];
         mk_inst (bi+1) ADD [Var x;Var mv] [sv];
         mk_inst (bi+2) MLOAD [Var sv] [vv];
         mk_inst (bi+3) ADD [dst;Var cv] [dv];
         mk_inst (bi+4) (if loc = LocStorage then SSTORE else TSTORE)
           [Var dv;Var vv] [];
         mk_inst (bi+5) ADD [Var cv;Lit 1w] [nv];
         mk_inst (bi+6) ASSIGN [Var nv] [cv];
         mk_inst (bi+7) JMP [Label hdr] []]` >>
        conj_tac >- simp[] >>
        irule topcopy_instruction_prefix >>
        qpat_assum `q.vs_inst_idx = 0` (fn th => REWRITE_TAC [th, ADD_CLAUSES]) >>
        rpt strip_tac >> qpat_assum `!j. j < 8 ==> _` irule >>
        qpat_x_assum `_ < LENGTH _` mp_tac >> simp[]) >>
     qabbrev_tac `code =
        [mk_inst bi MUL [Var cv;Lit 32w] [mv];
         mk_inst (bi+1) ADD [Var x;Var mv] [sv];
         mk_inst (bi+2) MLOAD [Var sv] [vv];
         mk_inst (bi+3) ADD [dst;Var cv] [dv];
         mk_inst (bi+4) (if loc = LocStorage then SSTORE else TSTORE)
           [Var dv;Var vv] [];
         mk_inst (bi+5) ADD [Var cv;Lit 1w] [nv];
         mk_inst (bi+6) ASSIGN [Var nv] [cv]]` >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                 i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
       (simp[Abbr `code`] >> Cases_on `loc = LocStorage` >>
        simp[mk_inst_def, is_terminator_def]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) []
        (OK (r0 with vs_inst_idx := q.vs_inst_idx + LENGTH code),Gf,tnf) /\
      allocas_from lo r0` by
       (irule run_inst_seq_origin_ptr_lift >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexists_tac `bbb` >> fs[]) >>
     qabbrev_tac `t1 = r0 with vs_inst_idx := q.vs_inst_idx + LENGTH code` >>
     `~t1.vs_halted /\ t1.vs_current_bb = loop_body /\ t1.vs_inst_idx = 7 /\
      allocas_from lo t1` by
       (simp[Abbr `t1`, Abbr `code`] >> gvs[allocas_from_def] >> metis_tac[]) >>
     `get_instruction bbb 7 = SOME (mk_inst (bi+7) JMP [Label hdr] [])` by
       (qpat_assum `!j. j < 8 ==> _` (qspec_then `7` mp_tac) >> simp[]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,Gf,tnf) []
        (OK (jump_to hdr t1),Gf,tnf)` by
       (irule copy_jmp_origin_ptr >> simp[] >> metis_tac[]) >>
     `!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
                                op_taint tnf (Var y) = op_taint tn (Var y)` by
       (rpt gen_tac >> strip_tac >>
        `~MEM y [cv;mv;sv;vv;dv;nv]` by metis_tac[] >>
        metis_tac[]) >>
     `(if loc = LocStorage then tnf.t_trans = tn.t_trans
       else tnf.t_stor = tn.t_stor)` by (Cases_on `loc = LocStorage` >> gvs[]) >>
     `tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm` by gvs[] >>
     `toplevel_copy_source_taint loc tnf SUBSET
        (toplevel_copy_source_taint loc tn DIFF
           {(k + n2w i, jj) | (i,jj) | i < j + 1}) UNION
        {(k + n2w i, jj) | (i,jj) | i < j + 1 /\ jj < 32 /\
                           w2n b + 32*i + jj IN tn.t_mem}` by
       (qpat_x_assum `toplevel_copy_source_taint loc tnf = _`
          (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum `tj.t_mem = tn.t_mem` (fn th => REWRITE_TAC [th]) >>
        irule copy_store_taint_bound_step >> first_assum ACCEPT_TAC) >>
     `store_copy_frame sa loc b k s (j+1) (jump_to hdr t1)` by
       (simp[Abbr `t1`] >> fs[ADD1]) >>
     `eval_operand (Var cv) (jump_to hdr t1) = SOME (n2w (j+1))` by
       (qpat_x_assum `eval_operand (Var cv) r0 = _` mp_tac >>
        simp[Abbr `t1`, jump_to_def, eval_operand_def, lookup_var_def, ADD1]) >>
     `allocas_from lo (jump_to hdr t1)` by
       (qpat_x_assum `allocas_from lo t1` mp_tac >>
        simp[allocas_from_def, jump_to_def]) >>
     qexistsl_tac [`jump_to hdr t1`, `Gf`, `tnf`] >>
     conj_tac >- metis_tac[origin_ptr_path_then] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[jump_to_def]) >>
  (* the counter's initialisation and the jump to the header *)
  `?t0 G0 tn0.
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t0,G0,tn0) /\ Inv 0 G0 tn0 t0 /\ ~t0.vs_halted /\
     t0.vs_current_bb = hdr /\ t0.vs_inst_idx = 0` by
    (qpat_x_assum `!j Gj tj q. j <= n /\ _ ==> _` kall_tac >>
     qpat_x_assum `!j Gj tj q. j < n /\ _ ==> _` kall_tac >>
     qunabbrev_tac `Inv` >> BETA_TAC >>
     qpat_assum `!j. j < 2 ==> get_instruction ebb _ = _`
       (qspec_then `0` (assume_tac o SRULE [])) >>
     qpat_assum `!j. j < 2 ==> get_instruction ebb _ = _`
       (qspec_then `1` (assume_tac o SRULE [])) >>
     `isPREFIX [mk_inst ei ASSIGN [Lit 0w] [cv]]
        (DROP s.vs_inst_idx ebb.bb_instructions)` by
       (irule topcopy_instruction_prefix >> simp[]) >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME ebb` by simp[] >>
     `get_instruction ebb (s.vs_inst_idx+1) =
        SOME (mk_inst (ei+1) JMP [Label hdr] [])` by simp[] >>
     drule_all copy_init_origin_ptr >>
     disch_then (qspecl_then [`D`, `explicit`, `PG`, `G`, `tn`] assume_tac) >>
     qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t0,G0,tn0)` >>
     `tn0.t_mem = tn.t_mem /\ tn0.t_stor = tn.t_stor /\
      tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm` by
       (simp[Abbr `tn0`] >>
        qmatch_goalsub_abbrev_tac `step_taint ii ss tt tn` >>
        mp_tac (Q.INST [`inst` |-> `ii`, `s` |-> `ss`, `t` |-> `tt`,
                        `tn` |-> `tn`] toplevel_copy_register_taint_frame) >>
        impl_tac >- simp[Abbr `ii`, Abbr `tt`, mk_inst_def, update_var_def] >>
        strip_tac >> fs[]) >>
     `op_taint tn0 (Var cv) = {}` by
       simp[Abbr `tn0`, step_taint_def, set_var_taint_def, out_taint_def,
            mk_inst_def, op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
     `!y. not_fresh_at sa y ==> FLOOKUP G0 y = FLOOKUP G y /\
                                op_taint tn0 (Var y) = op_taint tn (Var y)` by
       (rpt gen_tac >> strip_tac >> `y <> cv` by metis_tac[] >>
        simp[Abbr `G0`, Abbr `tn0`, step_prov_other_output,
             step_taint_other_output, mk_inst_def]) >>
     `store_copy_frame sa loc b k s 0 t0` by
       (simp[Abbr `t0`] >> irule topcopy_frame_update >> simp[] >>
        metis_tac[]) >>
     `~t0.vs_halted` by
       (qpat_x_assum `~s.vs_halted` mp_tac >>
        simp[Abbr `t0`, jump_to_def, update_var_def]) >>
     `t0.vs_allocas = s.vs_allocas /\ t0.vs_current_bb = hdr /\
      t0.vs_inst_idx = 0 /\ eval_operand (Var cv) t0 = SOME (n2w 0)` by
       simp[Abbr `t0`, jump_to_def, update_var_def, eval_operand_def,
            lookup_var_def, FLOOKUP_UPDATE] >>
     `allocas_from lo t0` by
       (qpat_x_assum `allocas_from lo s` mp_tac >>
        qpat_x_assum `t0.vs_allocas = _` (fn th => simp[allocas_from_def, th])) >>
     `(if loc = LocStorage then tn0.t_trans = tn.t_trans
       else tn0.t_stor = tn.t_stor)` by
       (IF_CASES_TAC >> first_assum ACCEPT_TAC) >>
     `toplevel_copy_source_taint loc tn0 = toplevel_copy_source_taint loc tn` by
       (qpat_x_assum `tn0.t_stor = _` mp_tac >>
        qpat_x_assum `tn0.t_trans = _` mp_tac >>
        simp[toplevel_copy_source_taint_def]) >>
     qexistsl_tac [`t0`, `G0`, `tn0`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_x_assum `toplevel_copy_source_taint loc tn0 = _`
       (fn th => REWRITE_TAC [th]) >>
     simp[SUBSET_DEF]) >>
  qspecl_then [`Inv`, `(D,lo,explicit,ctx,func,PG)`, `n`, `hdr`, `loop_body`,
               `exit`, `n`, `0`, `G0`, `tn0`, `t0`] mp_tac
    copy_loop_iterate_origin_ptr >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  conj_tac >- metis_tac[origin_ptr_path_then] >>
  qpat_x_assum `Inv n Gf tnf t` mp_tac >>
  qunabbrev_tac `Inv` >> BETA_TAC >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED
