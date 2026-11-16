(* Robust control loads for recursive live-slot stores.  The endpoint and
   ghosts are independent of the dead mask and the reserved constructor frame. *)
Theory fullStoreSlotsProbe
Ancestors
  fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport wordLoadStorePtr
  representationCleanPtr typedCopyLayoutPtr instMemFrontier fragExecMem
  bodyPtrDefs ptrDiscipline ptrCoverage venomState venomInst venomExecSemantics
  unitTransformDefs codegenRel contextCodegenRel memSafeRun valueEncodingDefs
  typedCopyOriginPtrBase placeStoreSlots compileEnv exprLoweringProps
  loweringShapeRules loweringStateRelDefs typedMemoryCopy emitHelperProps fragExec
  finite_map pred_set list arithmetic words fullStoreSlotsControlLayout

Theorem store_slots_robust_load_origin_ptr:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       mem_word_at (w2n a) m = w) ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> rpt gen_tac >>
  `mload (w2n a) s = w` by
    (qpat_x_assum `!m. mem_agree_outside _ _ m ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, mem_word_at_def]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[ptr_inst_ok_mload]) >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s = OK (update_var out w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
  `inst_mem_below_frontier (mk_inst id MLOAD [Var src] [out]) s /\
   inst_dload_in_section (mk_inst id MLOAD [Var src] [out]) s` by
    simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      eval_operand_def] >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
     Cases_on `x < 32` >> simp[] >> first_x_assum irule >> decide_tac) >>
  `step_prov PG G (mk_inst id MLOAD [Var src] [out]) (update_var out w s) =
       DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id MLOAD [Var src] [out]) s (update_var out w s) tn =
       (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      set_var_taint_def, out_taint_def, mk_inst_def, mem_taint_def,
      imm_taint_def, store_taint_def, adopt_reset_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      new_site_bytes_def, eval_operand_def, update_var_def,
      FLOOKUP_DEF, SF CONJ_ss, taint_component_equality]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
       DRESTRICT G (COMPL {out}), tn with t_var := tn.t_var |+ (out,{}))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_origin_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >> strip_tac >>
     gvs[mk_inst_def] >> first_x_assum drule_all >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[gas_origin_ptr_path_rules, update_var_def]
QED

(* The zero-count case never enters the recursive store.  The endpoint is
   fixed before D is chosen, so this applies to every finite horizon. *)
Theorem store_slots_zero_control_origin_ptr:
  emit_inst ASSIGN [Lit 0w] [cv] a = ((),b) /\
  emit_inst JMP [Label hdr] [] b = ((),c) /\
  emit_op LT [Var cv;cnt] h = (Var lv,h1) /\
  emit_op ISZERO [Var lv] h1 = (Var dv,h2) /\
  emit_inst JNZ [Var dv;Label exit;Label blabel] [] h2 = ((),hj) /\
  h.cs_current_bb = hdr /\ h.cs_current_insts = [] /\
  fn_has_code a c func /\ fn_has_code h hj func /\
  eval_operand cnt s = SOME 0w /\ op_prov G cnt = NONE /\
  op_taint tn cnt = {} /\ (!x. cnt = Var x ==> x <> cv) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s ==>
  !D explicit PG.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to exit (update_var dv 1w
             (update_var lv 0w (jump_to hdr (update_var cv 0w s))))),
       DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {lv})) (COMPL {dv}),
       tn with t_var := ((tn.t_var |+ (cv,{})) |+ (lv,{})) |+ (dv,{}))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all typed_copy_origin_ptr_counter_init_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
  `eval_operand cnt t = SOME 0w /\ op_prov Gf cnt = NONE /\
   op_taint tnf cnt = {}` by
    (Cases_on `cnt` >> gvs[eval_operand_def, op_prov_def, op_taint_def,
       jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT]) >>
  `allocas_from lo t` by
    (gvs[allocas_from_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (gvs[allocas_below_fmp_def, jump_to_def, update_var_def, lookup_var_def] >> (metis_tac[allocas_below_fmp_def, jump_to_def, update_var_def, lookup_var_def])) >>
  `t.vs_current_bb = h.cs_current_bb /\
   t.vs_inst_idx = LENGTH h.cs_current_insts` by simp[] >>
  drule_all (Q.INST [`k` |-> `0`, `N` |-> `0`]
    typed_copy_origin_ptr_header_branch_path |> SRULE []) >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[] >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem store_slots_zero_elements_origin_ptr:
  compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME 0w /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s ==>
  ?t Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule store_slots_elements_layout >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  `cs_extends sa init /\ init.cs_current_bb = sa.cs_current_bb /\
   init.cs_current_insts = sa.cs_current_insts` by
    gvs[fresh_label_def, fresh_var_def, cs_extends_def] >>
  imp_res_tac cs_extends_emit_inst >>
  imp_res_tac cs_extends_new_block >>
  imp_res_tac typed_copy_emit_op_mono >>
  `cs_extends init q /\ cs_extends h hj /\ cs_extends hj sc /\
   cs_extends sc sb /\ cs_extends sa h` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code init q func /\ fn_has_code h hj func` by
    (conj_tac >> irule fn_has_code_mid >> metis_tac[cs_extends_trans]) >>
  qpat_assum `emit_op LT _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  rename1 `lt = Var lv` >> rename1 `done = Var dv` >>
  `~not_fresh_at sa lv /\ ~not_fresh_at sa dv` by
    (imp_res_tac fresh_label_props >> fs[fresh_var_def] >>
     imp_res_tac emit_inst_extends >> imp_res_tac new_block_props >>
     gvs[not_fresh_at_def] >> conj_tac >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  imp_res_tac new_block_props >>
  `(!x. cnt = Var x ==> x <> cv) /\
   s.vs_current_bb = init.cs_current_bb /\
   s.vs_inst_idx = LENGTH init.cs_current_insts` by metis_tac[] >>
  qexistsl_tac [
    `jump_to exit (update_var dv 1w
      (update_var lv 0w (jump_to hdr (update_var cv 0w s))))`,
    `DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {lv})) (COMPL {dv})`,
    `tn with t_var := ((tn.t_var |+ (cv,{})) |+ (lv,{})) |+ (dv,{})`] >>
  conj_tac >- (rpt gen_tac >> irule store_slots_zero_control_origin_ptr >> metis_tac[]) >>
  simp[jump_to_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> `x <> cv /\ x <> lv /\ x <> dv` by metis_tac[] >> simp[]
QED
