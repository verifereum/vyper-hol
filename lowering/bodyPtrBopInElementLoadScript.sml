(* Memory membership producers: actual compiler arithmetic prefixes preserve
   the loop frame and registers. Coverage/nonwrap come from located source
   posts, not arbitrary ghost-region bounds. Low-level positioned load
   boundaries retain explicit coverage and typed cleanliness obligations. *)
Theory bodyPtrBopInElementLoad
Ancestors bodyPtrBopInLiveMemory bodyPtrBopInLoadRun
  bodyPtrBopInRepresentation stmtSimReturn arithmetic
  allocationPtr exprLoweringProps contextCodegenRel venomState words
  typedCopyLoopHeaderPtr bodyPtrBopInLiteralSuffix venomExecSemantics
  venomInst fragGasSeqPtr ptrSafeRun ptrDiscipline finite_map
  typedCopyPtr decoderGhostFramePtr fragGasPathPtr stmtAppendStorageRunPtr
  bodyPtrBopInLoopContract

Theorem dynamic_word_element_mload_path_clean:
  emit_op MLOAD [Var src] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  ptr_mem_ok cx aty (ArrayV (DynArrayV vs)) baseop G tn s /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  eval_operand baseop s = SOME bw /\ i < LENGTH vs /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type tv (EL i vs) /\
  w2n w = w2n bw + 32 + i * type_memory_size tv /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (drule_all memory_dynamic_typed_element_clean >> simp[]) >>
  irule mload_path_clean >>
  qpat_assum `emit_op MLOAD _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The located representation, not an arbitrary ghost-region bound, owns
   the read footprint. Both array layouts have capacity-sized footprints. *)
Theorem membership_memory_array_child_covers:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx aty sa sb es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\
  ((bd = Fixed cap /\ prefix = 0) \/
   (bd = Dynamic cap /\ prefix = 32)) /\ i < cap /\
  p.ptr_operand = Var src /\ lookup_var src s = SOME w /\
  lookup_var dst t = SOME (w + n2w (prefix + 32*i)) /\
  FLOOKUP G' dst = FLOOKUP G src /\ op_taint tn' (Var dst) = {} ==>
  ptr_covers G' tn' dst t 32
Proof
  strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_type_sizes] >>
  `prefix + 32*i + 32 <=
     val_footprint (ArrayTV tv bd) (ArrayV av)` by
    (gvs[loweringPostsTheory.val_footprint_def,
         valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `0 < (32:num)` by decide_tac >>
  drule_all membership_memory_offset_covers >> simp[]
QED

Theorem membership_memory_offset_nonwrap:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx ty sa sb es tvv (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\
  read_result cx tvv es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  p.ptr_operand = Var src /\ lookup_var src s = SOME w /\
  off < val_footprint tv v ==>
  w2n (w + n2w off) = w2n w + off
Proof
  strip_tac >>
  `expr_val_at cenv cx ty sa sb es v (Var src) s` by
    (drule_all membership_memory_value_at >> gvs[]) >>
  `eval_operand (Var src) s = SOME w` by simp[eval_operand_def] >>
  `w2n w <= w2n w + off /\
   w2n w + off < w2n w + val_footprint tv v` by decide_tac >>
  `w2n w + off < s.vs_alloca_next` by
    (drule_all expr_val_at_below_frontier >> simp[]) >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `off < dimword(:256) /\ w2n w + off < dimword(:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, LESS_MOD]
QED

Theorem membership_address_binop_step:
  (opc = MUL /\ f = word_mul \/ opc = ADD /\ f = word_add) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out (f a b) s)
Proof
  strip_tac >> gvs[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def]
QED

(* Raw instruction positioning allows this boundary to serve a loop body,
   whose compiler state is no longer the current open compilation block. *)
Theorem membership_address_binop_path:
  (opc = MUL /\ f = word_mul \/ opc = ADD /\ f = word_add) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    G' = step_prov PG G (mk_inst id opc [left;right] [out])
           (update_var out (f a b) s) /\
    (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out (f a b) s)` by
    (irule membership_address_binop_step >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [left;right] [out]) s` by
    (Cases_on `opc = MUL` >-
       (irule typed_copy_loop_test_check >>
        gvs[update_var_def] >> metis_tac[]) >>
     irule ptr_inst_ok_copy_len_binop >> gvs[update_var_def]) >>
  `~is_terminator (mk_inst id opc [left;right] [out]).inst_opcode /\
    (mk_inst id opc [left;right] [out]).inst_opcode <> INVOKE` by
    (gvs[mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  `step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out (f a b) s) tn = tn with t_var := tn.t_var |+ (out,{})` by
    (Cases_on `opc = MUL` >-
       gvs[typed_copy_loop_arith_ghost, update_var_def, mk_inst_def,
           ptrDisciplineTheory.out_taint_def] >>
     gvs[scalar_add_taint, update_var_def]) >>
  qexists_tac `step_prov PG G (mk_inst id opc [left;right] [out])
    (update_var out (f a b) s)` >>
  simp[scalar_step_old_prov] >>
  gvs[mk_inst_def] >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> simp[update_var_def, cj 1 gas_path_ptr_rules]
QED

Theorem membership_frame_scalar_update:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. not_fresh_at sa x ==> x <> dst) /\
  (!x. x <> dst ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (tn' with t_var := tn.t_var) = tn ==>
  membership_loop_frame sa G0 tn0 s0 G' tn'
    (update_var dst w s with vs_inst_idx := pc)
Proof
  strip_tac >> fs[membership_loop_frame_def, taint_component_equality] >>
  reverse conj_tac
  >- (qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
      simp[update_var_def]) >>
  rpt strip_tac >> `x <> dst` by metis_tac[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[lookup_var_def]
QED

Theorem membership_registers_scalar_update:
  membership_loop_registers sa i r G tn s /\
  dst <> "%" ++ toString (sa.cs_next_var+1) /\
  dst <> "%" ++ toString sa.cs_next_var /\
  (!x. x <> dst ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  membership_loop_registers sa i r G' tn'
    (update_var dst w s with vs_inst_idx := pc)
Proof
  strip_tac >> irule membership_loop_registers_untouched >>
  goal_assum (drule_at Any) >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem membership_address_binop_framed_path:
  (opc = MUL /\ f = word_mul \/ opc = ADD /\ f = word_add) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [left;right] [out]) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  out <> "%" ++ toString (sa.cs_next_var+1) /\
  out <> "%" ++ toString sa.cs_next_var ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    tn' = (tn with t_var := tn.t_var |+ (out,{})) /\
    G' = step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out (f a b) s)
Proof
  strip_tac >>
  drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_path >>
  simp[] >> disch_then drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  (conj_tac
   >- (irule membership_frame_scalar_update >>
       conj_tac >- metis_tac[] >> qexistsl_tac [`G`, `tn`] >>
       simp[op_taint_def, FLOOKUP_UPDATE]) >>
   irule membership_registers_scalar_update >>
   gvs[] >> qexistsl_tac [`G`, `tn`] >>
   simp[op_taint_def, FLOOKUP_UPDATE])
QED

Theorem membership_compiled_product_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME
      (mk_inst (sa.cs_next_id+6) MUL
        [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)]
        ["%" ++ toString (sa.cs_next_var+3)])
Proof
  strip_tac >> gvs[SRULE [] bodyPtrBopInLoopLayoutTheory.membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> simp[get_instruction_def]
QED

Theorem membership_product_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load is_ctor imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ dst = "%" ++ toString (sa.cs_next_var+3) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (n2w (stride*i)) s with vs_inst_idx := 1) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_compiled_product_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+6) MUL
      [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)]
      ["%" ++ toString (sa.cs_next_var+3)])` by simp[] >>
  `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+3))` by
    simp[compileEnvTheory.not_fresh_at_def] >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+1))) s = SOME (n2w i) /\
   op_taint tn (Var ("%" ++ toString (sa.cs_next_var+1))) = {}` by
    fs[membership_loop_registers_def, eval_operand_def] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[GSYM word_mul_n2w, WORD_MULT_COMM] >>
  goal_assum (drule_at Any) >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
    update_var_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem membership_compiled_runtime_address_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ delta = (if 0 < skip then 1 else 0) ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    (0 < skip ==> get_instruction bb 1 = SOME
      (mk_inst (sa.cs_next_id+7) ADD
        [Lit (n2w skip);Var ("%" ++ toString (sa.cs_next_var+3))]
        ["%" ++ toString (sa.cs_next_var+4)])) /\
    get_instruction bb (1+delta) = SOME
      (mk_inst (sa.cs_next_id+7+delta) ADD
        [arr;Var ("%" ++ toString (sa.cs_next_var+3+delta))]
        ["%" ++ toString (sa.cs_next_var+4+delta)]) /\
    get_instruction bb (2+delta) = SOME
      (mk_inst (sa.cs_next_id+8+delta)
        (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
          LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)
        [Var ("%" ++ toString (sa.cs_next_var+4+delta))]
        ["%" ++ toString (sa.cs_next_var+5+delta)])
Proof
  strip_tac >> gvs[SRULE [] bodyPtrBopInLoopLayoutTheory.membership_loop_layout] >>
  fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >> Cases_on `loc` >> simp[get_instruction_def]
QED

Theorem membership_runtime_offset_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 1 /\
  lookup_var ("%" ++ toString (sa.cs_next_var+3)) s = SOME (n2w (stride*i)) /\
  FLOOKUP G ("%" ++ toString (sa.cs_next_var+3)) = NONE /\
  op_taint tn (Var ("%" ++ toString (sa.cs_next_var+3))) = {} /\
  delta = (if 0 < skip then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+3+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 1+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (n2w (skip+stride*i)) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> Cases_on `0 < skip`
  >- (drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
      `get_instruction bb s.vs_inst_idx = SOME
        (mk_inst (sa.cs_next_id+7) ADD
          [Lit (n2w skip);Var ("%" ++ toString (sa.cs_next_var+3))]
          ["%" ++ toString (sa.cs_next_var+4)])` by simp[] >>
      `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+4))` by
        simp[compileEnvTheory.not_fresh_at_def] >>
      drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
      disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
      simp[eval_operand_def, op_taint_def] >> disch_then drule_all >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      goal_assum (drule_at Any) >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w,
        MULT_COMM, op_taint_def] >>
      simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
        op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  `skip = 0` by decide_tac >>
  qexistsl_tac [`G`, `tn`, `s`] >>
  gvs[cj 1 gas_path_ptr_rules]
QED

Theorem membership_runtime_address_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 1+delta /\
  off = "%" ++ toString (sa.cs_next_var+3+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+4+delta) /\
  lookup_var off s = SOME offset /\ FLOOKUP G off = NONE /\
  op_taint tn (Var off) = {} /\ eval_operand arr s = SOME bw /\
  op_taint tn arr = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (bw+offset) s with vs_inst_idx := 2+delta) /\
    FLOOKUP G' dst = op_prov G arr /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+7+delta) ADD
      [arr;Var ("%" ++ toString (sa.cs_next_var+3+delta))]
      ["%" ++ toString (sa.cs_next_var+4+delta)])` by gvs[] >>
  `~not_fresh_at sa ("%" ++ toString (sa.cs_next_var+4+delta))` by
    simp[compileEnvTheory.not_fresh_at_def] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_address_binop_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  gvs[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[ADD1] >> goal_assum (drule_at Any) >>
  Cases_on `op_prov G arr` >>
  gvs[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]
QED

Theorem membership_runtime_address_prefix:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ eval_operand arr s0 = SOME bw /\
  op_taint tn0 arr = {} /\ (!x. arr = Var x ==> not_fresh_at sa x) /\
  delta = (if 0 < skip then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+4+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 2+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (bw+n2w (skip+stride*i)) /\
    FLOOKUP G' dst = op_prov G0 arr /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all (SRULE [] (GEN_ALL membership_product_path)) >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G1 tn1 p` >>
  `~p.vs_halted /\ p.vs_inst_idx = 1 /\
   p.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
   lookup_var ("%" ++ toString (sa.cs_next_var+3)) p = SOME (n2w (stride*i))` by
    simp[Abbr `p`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  drule (SRULE [] (GEN_ALL membership_runtime_offset_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `q` strip_assume_tac)))) >>
  drule_all membership_loop_frame_operand >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G3 tn3 t` >>
  qexistsl_tac [`G3`, `tn3`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[update_var_def] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G1 tn1 p _ G2 tn2 _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G2 tn2 q _ G3 tn3 _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[]
QED

Theorem membership_positioned_mload_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  lookup_var src s = SOME w /\ ptr_covers G tn src s 32 /\
  mem_word_taint tn.t_mem (w2n w) = {} ==>
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (mload (w2n w) s) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
     OK (update_var out (mload (w2n w) s) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[exec_read1_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_mload >> simp[update_var_def]) >>
  `~is_terminator (mk_inst id MLOAD [Var src] [out]).inst_opcode /\
   (mk_inst id MLOAD [Var src] [out]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  `step_taint (mk_inst id MLOAD [Var src] [out]) s
     (update_var out (mload (w2n w) s) s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule readonly_load_taint >> simp[eval_operand_def, update_var_def]) >>
  qexists_tac `step_prov PG G (mk_inst id MLOAD [Var src] [out])
    (update_var out (mload (w2n w) s) s)` >>
  simp[bodyPtrBopInLoadOutputTheory.scalar_load_output_prov, scalar_step_old_prov] >>
  gvs[mk_inst_def] >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> simp[update_var_def, cj 1 gas_path_ptr_rules]
QED

Theorem membership_frame_memory:
  membership_loop_frame sa G0 tn0 s0 G tn s ==>
  s.vs_memory = s0.vs_memory /\ tn.t_mem = tn0.t_mem /\
  (!off. mload off s = mload off s0)
Proof
  simp[membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[mload_def]
QED

Theorem membership_frame_ptr_mem_ok:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ptr_mem_ok cx ty v op G0 tn0 s0 ==>
  ptr_mem_ok cx ty v op G tn s
Proof
  strip_tac >> drule_all membership_loop_frame_operand >> strip_tac >>
  drule membership_frame_memory >> strip_tac >>
  fs[bodyPtrDefsTheory.ptr_mem_ok_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  fs[op_prov_def] >> metis_tac[]
QED

Theorem membership_memory_load_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 2+delta /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  lookup_var src s = SOME w /\ ptr_covers G tn src s 32 /\
  mem_word_taint tn.t_mem (w2n w) = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (mload (w2n w) s) s with vs_inst_idx := 3+delta) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+8+delta) MLOAD [Var src] [dst])` by gvs[] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_mload_path >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  qexists_tac `tn with t_var := tn.t_var |+
    ("%" ++ toString (sa.cs_next_var+5+(if 0 < skip then 1 else 0)),{})` >>
  fs[ADD1, op_taint_def, FLOOKUP_UPDATE] >>
  reverse conj_tac
  >- (irule membership_registers_scalar_update >>
      simp[] >> qexistsl_tac [`G`, `tn`] >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  irule membership_frame_scalar_update >>
  conj_tac >- simp[compileEnvTheory.not_fresh_at_def] >>
  qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]
QED

(* Discharge all three MLOAD obligations from the original located post;
   only the generated address and the preserved loop frame concern t. *)
Theorem membership_memory_array_read:
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ value_has_type tv v /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\
      prefix = 32 /\ i < LENGTH vs /\ v = EL i vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\
      prefix = 0 /\ v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv))) /\
  i < cap /\ lookup_var basesrc s0 = SOME bw /\
  membership_loop_frame sa G0 tn0 s0 G tn t /\
  lookup_var dst t = SOME (bw + n2w (prefix+32*i)) /\
  FLOOKUP G dst = FLOOKUP G0 basesrc /\ op_taint tn (Var dst) = {} ==>
  ptr_covers G tn dst t 32 /\
  mem_word_taint tn.t_mem (w2n (bw + n2w (prefix+32*i))) = {} /\
  mload (w2n (bw + n2w (prefix+32*i))) t = typed_val_to_w256 tv v
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `((bd = Fixed cap /\ prefix = 0) \/
    (bd = Dynamic cap /\ prefix = 32))` by metis_tac[] >>
  `type_memory_size tv = 32` by metis_tac[word_type_sizes] >>
  `ptr_mem_ok cx aty (ArrayV av) (Var basesrc) G0 tn0 s0` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  `ptr_covers G tn dst t 32` by
    (metis_tac[membership_memory_array_child_covers]) >>
  `prefix+32*i < val_footprint (ArrayTV tv bd) (ArrayV av)` by
    (gvs[loweringPostsTheory.val_footprint_def,
         valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `w2n (bw+n2w (prefix+32*i)) = w2n bw + (prefix+32*i)` by
    (drule_all membership_memory_offset_nonwrap >> simp[]) >>
  `eval_operand (Var basesrc) s0 = SOME bw` by simp[eval_operand_def] >>
  `mem_word_taint tn0.t_mem (w2n bw + prefix + i * type_memory_size tv) = {} /\
   mload (w2n bw + prefix + i * type_memory_size tv) s0 = typed_val_to_w256 tv v` by
    (metis_tac[memory_array_typed_element_read]) >>
  drule membership_frame_memory >> strip_tac >>
  full_simp_tac bool_ss [ADD_ASSOC, ADD_CLAUSES, MULT_COMM] >> gvs[]
QED

Theorem membership_memory_array_element_prefix:
  compile_array_membership_loop needle (Var basesrc) len 32 prefix
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ not_fresh_at sa basesrc /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ value_has_type tv v /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\
      prefix = 32 /\ i < LENGTH vs /\ v = EL i vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\
      prefix = 0 /\ v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv))) /\
  i < cap /\ lookup_var basesrc s0 = SOME bw /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn0 (Var basesrc) = {}` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  `eval_operand (Var basesrc) s0 = SOME bw` by simp[eval_operand_def] >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  rule_assum_tac (SRULE [op_prov_def]) >>
  drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_memory_array_read)) >>
  disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_memory_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED

Theorem membership_memory_array_element_prefix_source:
  compile_array_membership_loop needle (Var basesrc) len 32 prefix
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  membership_loop_frame sa Gh tnh sh G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ not_fresh_at early basesrc /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ value_has_type tv v /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\
      prefix = 32 /\ i < LENGTH vs /\ v = EL i vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\
      prefix = 0 /\ v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv))) /\
  i < cap /\ lookup_var basesrc s0 = SOME bw /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa Gh tnh sh G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn0 (Var basesrc) = {}` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  `not_fresh_at sa basesrc` by metis_tac[] >>
  `eval_operand (Var basesrc) s0 = SOME bw` by simp[eval_operand_def] >>
  `eval_operand (Var basesrc) sh = SOME bw /\
   op_prov Gh (Var basesrc) = op_prov G0 (Var basesrc) /\
   op_taint tnh (Var basesrc) = {}` by
    (qpat_assum `membership_loop_frame early G0 tn0 s0 Gh tnh sh`
       (mp_then Any mp_tac membership_loop_frame_operand) >>
     disch_then (qspec_then `Var basesrc` mp_tac) >> simp[]) >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  `membership_loop_frame early G0 tn0 s0 G1 tn1 q` by
    metis_tac[membership_loop_frame_source] >>
  rule_assum_tac (SRULE [op_prov_def]) >>
  `FLOOKUP G1 ("%" ++ toString (sa.cs_next_var+4+delta)) = FLOOKUP G0 basesrc` by
    (gvs[] >> metis_tac[]) >>
  gnvs[] >>
  drule_at (Pat `membership_loop_frame early _ _ _ G1 tn1 q`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_memory_array_read)) >>
  disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_memory_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame sa Gh tnh sh G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa Gh tnh sh G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED
