(*
 * Fuel bound for the dynamic-array ABI decode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_decode_dyn_loop
 *)

Theory fragFuelLoopAbiDecDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousContext fragExec
  fragFuelLoopAbiDecDynSteps exprSimAbiGasBridge exprLoweringProps list sorting
  fnBlockBodyHelpers
  venomInst venomMemProps venomInstProps venomExecSemantics venomEffects venomState
Libs
  fragFuelLib

(* A successful one-input header instruction preserves byte memory.
   Memory-writing non-call opcodes have incompatible arity; DLOAD is a
   conservative effect annotation but its semantics is a read. *)
Theorem abi_dyn_single_input_memory[local]:
  !fuel ctx opc id op out s t.
    ~is_terminator opc /\ opc <> PHI /\ opc <> INVOKE /\
    step_inst fuel ctx (mk_inst id opc [op] [out]) s = OK t ==>
    t.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `is_alloca_op opc`
  >- (irule step_inst_alloca_preserves_memory >>
      qexistsl_tac [`ctx`, `fuel`, `mk_inst id opc [op] [out]`] >>
      simp[mk_inst_def]) >>
  Cases_on `Eff_MEMORY IN write_effects opc`
  >- (Cases_on `opc` >>
      gvs[write_effects_def, empty_effects_def, all_effects_def,
          is_terminator_def] >>
      gvs[step_inst_non_invoke, mk_inst_def] >>
      gvs[step_inst_base_opcode_eqs, exec_write2_def, exec_read1_def,
          AllCaseEqs(), update_var_def]) >>
  irule write_effects_sound_memory >>
  qexistsl_tac [`ctx`, `fuel`, `mk_inst id opc [op] [out]`] >>
  simp[mk_inst_def]
QED

(* Straight-line segment boundaries.  The exit sets name the loop's
   control-flow edges; no composition across the back edge is used here. *)
Theorem fuel_ok_decode_dyn_header[local]:
  !load_opc i_ptr base_op src_op exit_lbl body_lbl Wv E.
    ~is_terminator load_opc /\ load_opc <> PHI /\
    exit_lbl IN E /\ body_lbl IN E ==>
    fuel_ok Wv {} E
      (do i_op <- emit_op MLOAD [i_ptr];
          src_addr <- compile_abi_dec_addr base_op src_op;
          cnt_hdr <- emit_op load_opc [src_addr];
          cmp <- emit_op LT [i_op; cnt_hdr];
          done_op <- emit_op ISZERO [cmp];
          emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] []
       od)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_dec_addr_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_decode_dyn_body[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz
     i_ptr hdr_lbl Wv E.
    ~is_terminator load_opc /\ load_opc <> PHI /\ hdr_lbl IN E /\
    (!d s Wv E. fuel_ok Wv {} E
       (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    fuel_ok Wv {} E
      (do i_op2 <- emit_op MLOAD [i_ptr];
          src_data <- emit_op ADD [src_op; Lit 32w];
          src_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
          elem_src <- emit_op ADD [src_data; src_off];
          actual_src <-
            (if dec_info_needs_offset elem_info then
               compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src
                 src_data hi_op elem_abi_sz
             else return elem_src);
          dst_data <- emit_op ADD [dst; Lit 32w];
          dst_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
          elem_dst <- emit_op ADD [dst_data; dst_off];
          compile_abi_decode_to_buf elem_dst actual_src
            load_opc base_op hi_op elem_info;
          new_i <- emit_op ADD [i_op2; Lit 1w];
          emit_void MSTORE [i_ptr; new_i];
          emit_inst JMP [Label hdr_lbl] []
       od)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

(* Discarding control-flow destinations gives the structural compilation
   invariant without asserting termination of the back edge. *)
Theorem fuel_ok_decode_dyn_structure[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt.
    ~is_terminator load_opc /\ load_opc <> PHI /\
    (!d s Wv E. fuel_ok Wv {} E
       (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    !Wv. fuel_ok Wv {} UNIV
      (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
        elem_info elem_abi_sz elem_mem_sz i_ptr cnt)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_decode_to_buf_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp,
    fuel_ok_emit_inst_jnz] >>
  simp[is_terminator_def]
QED

Theorem fuel_decode_dyn_compile_decompose[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz
     i_ptr cnt st r st'.
    compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
      elem_info elem_abi_sz elem_mem_sz i_ptr cnt st = (r, st') ==>
    ?hdr body exit i_op src_addr cnt_hdr cmp done_op i_op2 src_data
     src_off elem_src actual_src dst_data dst_off elem_dst new_i
     old_hdr old_body old_exit
     s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16
     s17 s18 s19 s20 s21 s22 s23 s24 s25.
      fresh_label "dec_dyn_hdr" st = (hdr, s1) /\
      fresh_label "dec_dyn_body" s1 = (body, s2) /\
      fresh_label "dec_dyn_exit" s2 = (exit, s3) /\
      emit_inst JMP [Label hdr] [] s3 = ((), s4) /\
      new_block hdr s4 = (old_hdr, s5) /\
      emit_op MLOAD [i_ptr] s5 = (i_op, s6) /\
      compile_abi_dec_addr base_op src_op s6 = (src_addr, s7) /\
      emit_op load_opc [src_addr] s7 = (cnt_hdr, s8) /\
      emit_op LT [i_op; cnt_hdr] s8 = (cmp, s9) /\
      emit_op ISZERO [cmp] s9 = (done_op, s10) /\
      emit_inst JNZ [done_op; Label exit; Label body] [] s10 = ((), s11) /\
      new_block body s11 = (old_body, s12) /\
      emit_op MLOAD [i_ptr] s12 = (i_op2, s13) /\
      emit_op ADD [src_op; Lit 32w] s13 = (src_data, s14) /\
      emit_op MUL [i_op2; Lit (n2w elem_abi_sz)] s14 = (src_off, s15) /\
      emit_op ADD [src_data; src_off] s15 = (elem_src, s16) /\
      (if dec_info_needs_offset elem_info then
         compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src
           src_data hi_op elem_abi_sz
       else return elem_src) s16 = (actual_src, s17) /\
      emit_op ADD [dst; Lit 32w] s17 = (dst_data, s18) /\
      emit_op MUL [i_op2; Lit (n2w elem_mem_sz)] s18 = (dst_off, s19) /\
      emit_op ADD [dst_data; dst_off] s19 = (elem_dst, s20) /\
      compile_abi_decode_to_buf elem_dst actual_src load_opc base_op hi_op
        elem_info s20 = ((), s21) /\
      emit_op ADD [i_op2; Lit 1w] s21 = (new_i, s22) /\
      emit_void MSTORE [i_ptr; new_i] s22 = ((), s23) /\
      emit_inst JMP [Label hdr] [] s23 = ((), s24) /\
      new_block exit s24 = (old_exit, s25) /\
      r = () /\ st' = s25
Proof
  rpt gen_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >>
  strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED

(* Retain the actual successful instruction step when lifting an emitted
   fresh-output instruction to the block-fuel interface. *)
Theorem abi_dyn_emit_op_outcome[local]:
  !opc ops sa op sb G N ctx fn s.
    emit_op opc ops sa = (op, sb) /\ ~is_terminator opc /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
        t.vs_labels = s.vs_labels /\
        ?u. step_inst G ctx
              (mk_inst sa.cs_next_id opc ops
                [STRING #"%" (toString sa.cs_next_var)]) s = OK u /\
            t = u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc ops
       [STRING #"%" (toString sa.cs_next_var)]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  drule_then (qspecl_then [`s`, `bb`,
    `mk_inst sa.cs_next_id opc ops
      [STRING #"%" (toString sa.cs_next_var)]`] mp_tac)
    run_from_nonterm_stable >>
  simp[mk_inst_def] >>
  impl_tac >- gvs[at_point_def, mk_inst_def] >>
  strip_tac
  >- (simp[fuel_outcome_def] >> disj1_tac >> conj_tac
      >- gvs[at_point_def] >>
      `s1.vs_labels = s.vs_labels` by
        metis_tac[venomExecPropsTheory.step_inst_preserves_labels_always] >>
      gvs[vars_kept_def, lookup_var_def] >> rpt strip_tac >>
      first_x_assum irule >> metis_tac[var_below_fresh]) >>
  simp[fuel_outcome_def]
QED

Theorem abi_dyn_mload_outcome[local]:
  !ptr sa op sb G N ctx fn s p.
    emit_op MLOAD [ptr] sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s /\
    eval_operand ptr s = SOME p ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           eval_operand op t = SOME (mload (w2n p) s) /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels)
Proof
  rpt strip_tac >>
  `~is_terminator MLOAD` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_read1_def, eval_operands_def, eval_operand_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem abi_dyn_addr_outcome[local]:
  !base_op pos sa op sb G N ctx fn s.
    compile_abi_dec_addr base_op pos sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels)
Proof
  rpt strip_tac >>
  Cases_on `base_op = Lit 0w`
  >- (gvs[compile_abi_dec_addr_def, comp_return_def] >>
      irule fuel_outcome_refl >> simp[]) >>
  `emit_op ADD [base_op; pos] sa = (op, sb)` by
    gvs[compile_abi_dec_addr_def] >>
  `~is_terminator ADD` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure2_def, update_var_def, AllCaseEqs()]
QED

Theorem abi_dyn_header_load_outcome[local]:
  !opc arg sa op sb G N ctx fn s.
    emit_op opc [arg] sa = (op, sb) /\
    ~is_terminator opc /\ opc <> PHI /\ opc <> INVOKE /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels)
Proof
  rpt strip_tac >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all abi_dyn_single_input_memory >> simp[]
QED

Theorem abi_dyn_header_middle_outcome[local]:
  !base_op pos opc sa arg sm bound sb G N ctx fn s.
    compile_abi_dec_addr base_op pos sa = (arg, sm) /\
    emit_op opc [arg] sm = (bound, sb) /\
    ~is_terminator opc /\ opc <> PHI /\ opc <> INVOKE /\
    N <= sa.cs_next_var /\ N <= sm.cs_next_var /\
    callees_stable G ctx fn /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels)
Proof
  rpt strip_tac >>
  drule_all abi_dyn_addr_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. at_point sb t /\ vars_kept N {} s t /\
          t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels`, `0`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule_all abi_dyn_header_load_outcome >> strip_tac >>
      irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[] >>
      metis_tac[vars_kept_trans]) >>
  simp[]
QED

(* An undefined loop-counter address is already a fixed error outcome,
   not a runtime-validity premise for the loop theorem. *)
Theorem abi_dyn_mload_missing[local]:
  !ptr sa op sb G N ctx fn s.
    emit_op MLOAD [ptr] sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s /\
    eval_operand ptr s = NONE ==>
    fuel_outcome G ctx fn s 0 (\t. F)
Proof
  rpt strip_tac >>
  `~is_terminator MLOAD` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_read1_def, eval_operands_def]
QED

Theorem abi_dyn_lt_outcome[local]:
  !a b sa op sb G N ctx fn s w.
    emit_op LT [a; b] sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s /\
    eval_operand a s = SOME w ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
           ?v. eval_operand b s = SOME v /\
               eval_operand op t = SOME (bool_to_word (w2n w < w2n v)))
Proof
  rpt strip_tac >>
  `~is_terminator LT` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem abi_dyn_iszero_outcome[local]:
  !a sa op sb G N ctx fn s w.
    emit_op ISZERO [a] sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s /\
    eval_operand a s = SOME w ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
           t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
           eval_operand op t = SOME (bool_to_word (w = 0w)))
Proof
  rpt strip_tac >>
  `~is_terminator ISZERO` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure1_def, eval_operands_def, eval_operand_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem abi_dyn_header_tail_outcome[local]:
  !a b sa cmp sm done_op sn sb exit body_lbl G N ctx fn s w.
    emit_op LT [a; b] sa = (cmp, sm) /\
    emit_op ISZERO [cmp] sm = (done_op, sn) /\
    emit_inst JNZ [done_op; Label exit; Label body_lbl] [] sn = ((), sb) /\
    N <= sa.cs_next_var /\ N <= sm.cs_next_var /\
    callees_stable G ctx fn /\ no_phi_fn fn /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
    fn_has_code sn sb fn /\ at_point sa s /\
    eval_operand a s = SOME w ==>
    ?j. j <= 1 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N {} s t /\ t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
           t.vs_inst_idx = 0 /\
           (t.vs_current_bb = exit \/
            (t.vs_current_bb = body_lbl /\ w2n w < 2 ** 256 - 1)))
Proof
  rpt strip_tac >>
  drule_all abi_dyn_lt_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. vars_kept N {} s t /\ t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
           t.vs_inst_idx = 0 /\
           (t.vs_current_bb = exit \/
            (t.vs_current_bb = body_lbl /\ w2n w < 2 ** 256 - 1))`, `1`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      drule_all abi_dyn_iszero_outcome >> strip_tac >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then
        [`\t. vars_kept N {} s t /\ t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
               t.vs_inst_idx = 0 /\
               (t.vs_current_bb = exit \/
                (t.vs_current_bb = body_lbl /\ w2n w < 2 ** 256 - 1))`, `1`] mp_tac) >>
      impl_tac
      >- (simp[] >> rpt strip_tac >>
          `sb.cs_current_bb = sn.cs_current_bb /\
           sb.cs_current_insts = sn.cs_current_insts ++
             [mk_inst sn.cs_next_id JNZ
               [done_op; Label exit; Label body_lbl] []]` by
            gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
                comp_return_def, fresh_id_def, emit_def] >>
          drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
          first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
          qexists_tac `1` >> simp[] >>
          irule fuel_outcome_jump >> simp[] >>
          qexistsl_tac [`bb`, `mk_inst sn.cs_next_id JNZ
            [done_op; Label exit; Label body_lbl] []`,
            `if w2n w < w2n v then body_lbl else exit`] >>
          simp[mk_inst_def, is_terminator_def] >>
          conj_tac
          >- (drule venomExecPropsTheory.step_jnz_behavior >>
              disch_then (qspecl_then [`exit`, `body_lbl`, `sn.cs_next_id`] mp_tac) >>
              Cases_on `w2n w < w2n v` >> simp[bool_to_word_def]) >>
          `vars_kept N {} s t'` by metis_tac[vars_kept_trans] >>
          `w2n v < 2 ** 256` by
            (mp_tac (Q.ISPEC `v:bytes32` wordsTheory.w2n_lt) >>
             simp[wordsTheory.dimword_def]) >>
          Cases_on `w2n w < w2n v` >>
          gvs[at_point_def, jump_to_def, vars_kept_def, lookup_var_def,
              mk_inst_def]) >>
      simp[]) >>
  simp[]
QED

Theorem abi_dyn_eval_operand_kept[local]:
  !N ptr_op s t.
    vars_kept N {} s t /\ t.vs_labels = s.vs_labels /\
    (!x. ptr_op = Var x ==> var_below N x) ==>
    eval_operand ptr_op t = eval_operand ptr_op s
Proof
  rpt strip_tac >> Cases_on `ptr_op` >>
  gvs[eval_operand_def, vars_kept_def] >> metis_tac[]
QED

Theorem abi_dyn_header_outcome[local]:
  !ptr base_op pos opc sa a s6 arg s7 bound s8 cmp s9 done_op s10 sb
     exit body_lbl N.
    emit_op MLOAD [ptr] sa = (a, s6) /\
    compile_abi_dec_addr base_op pos s6 = (arg, s7) /\
    emit_op opc [arg] s7 = (bound, s8) /\
    emit_op LT [a; bound] s8 = (cmp, s9) /\
    emit_op ISZERO [cmp] s9 = (done_op, s10) /\
    emit_inst JNZ [done_op; Label exit; Label body_lbl] [] s10 = ((), sb) /\
    ~is_terminator opc /\ opc <> PHI /\ opc <> INVOKE /\
    N <= sa.cs_next_var /\
    s6.cs_next_var <= s7.cs_next_var /\
    s6.cs_next_var <= s8.cs_next_var /\
    s6.cs_next_var <= s9.cs_next_var /\
    (!x. ptr = Var x ==> var_below N x) ==>
    ?Kh. !G ctx fn s p.
      callees_stable G ctx fn /\ no_phi_fn fn /\
      fn_has_code sa s6 fn /\ fn_has_code s6 s7 fn /\
      fn_has_code s7 s8 fn /\ fn_has_code s8 s9 fn /\
      fn_has_code s9 s10 fn /\ fn_has_code s10 sb fn /\
      at_point sa s /\ eval_operand ptr s = SOME p ==>
      ?j. j <= Kh /\ fuel_outcome G ctx fn s j
        (\t. vars_kept N {} s t /\ eval_operand ptr t = SOME p /\
             t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
             t.vs_inst_idx = 0 /\
             (t.vs_current_bb = exit \/
              (t.vs_current_bb = body_lbl /\
               w2n (mload (w2n p) s) < 2 ** 256 - 1)))
Proof
  rpt gen_tac >> strip_tac >> qexists_tac `1` >> rpt strip_tac >>
  `N <= s6.cs_next_var /\
   a = Var (STRING #"%" (toString sa.cs_next_var)) /\
   var_below s6.cs_next_var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def, var_below_def] >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s _ Q` >>
  drule_all abi_dyn_mload_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Q`, `1`] mp_tac) >> impl_tac
  >- (simp[] >> rpt strip_tac >>
      `fuel_outcome G ctx fn t 0
         (\u. at_point s8 u /\ vars_kept s6.cs_next_var {} t u /\
              u.vs_memory = t.vs_memory /\ u.vs_labels = t.vs_labels)` by
        (irule abi_dyn_header_middle_outcome >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then [`Q`, `1`] mp_tac) >> impl_tac
      >- (simp[] >> rpt strip_tac >>
          `eval_operand a t' = SOME (mload (w2n p) s)` by
            (gvs[vars_kept_def, eval_operand_def] >> metis_tac[]) >>
          drule_all abi_dyn_header_tail_outcome >> strip_tac >>
          qexists_tac `j` >> simp[] >>
          irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
          simp[Abbr `Q`] >> qx_gen_tac `u` >> strip_tac >>
          `vars_kept s6.cs_next_var {} t u` by
            metis_tac[vars_kept_trans] >>
          `vars_kept N {} t u` by
            (gvs[vars_kept_def, var_below_def] >>
             metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
          `vars_kept N {} s u` by metis_tac[vars_kept_trans] >>
          simp[] >>
          drule_all abi_dyn_eval_operand_kept >> simp[]) >>
      simp[]) >>
  simp[]
QED

Theorem fuel_ok_decode_dyn_body_middle[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_op2.
    ~is_terminator load_opc /\ load_opc <> PHI /\
    (!d s Wv E. fuel_ok Wv {} E
       (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    fuel_ok {} {} {}
      (do src_data <- emit_op ADD [src_op; Lit 32w];
          src_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
          elem_src <- emit_op ADD [src_data; src_off];
          actual_src <-
            (if dec_info_needs_offset elem_info then
               compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src
                 src_data hi_op elem_abi_sz
             else return elem_src);
          dst_data <- emit_op ADD [dst; Lit 32w];
          dst_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
          elem_dst <- emit_op ADD [dst_data; dst_off];
          compile_abi_decode_to_buf elem_dst actual_src
            load_opc base_op hi_op elem_info
       od)
Proof
  rpt strip_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp,
    fuel_ok_emit_inst_jnz] >> simp[is_terminator_def]
QED

Theorem abi_dyn_code_if[local]:
  !P b m n. code_action P m /\ code_action P n ==>
    code_action P (if b then m else n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem abi_dyn_code_copy_case[local]:
  !P opc m n p.
    code_action P m /\ code_action P n /\ code_action P p ==>
    code_action P (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  Cases_on `opc` >> simp[]
QED

Theorem abi_dyn_decode_code[local]:
  (!dst src lop base hi info.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI /\ (lop <> DJMP ==> opc <> DJMP))
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI /\ (lop <> DJMP ==> opc <> DJMP))
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI /\ (lop <> DJMP ==> opc <> DJMP))
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss [code_action_bind, code_action_ignore_bind, code_action_return,
    code_action_emit_op, code_action_emit_void, code_action_emit_inst,
    code_action_fresh_label, code_action_new_block, code_action_alloc_buffer]
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume abi_dyn_decode_code[word]:
  Cases_on `base' = Lit 0w` >> simp[] >>
  irule code_action_bind >> simp[code_action_emit_op, code_action_return] >>
  gen_tac >> irule code_action_bind >> simp[code_action_emit_op] >>
  gen_tac >> Cases_on `clamp_info` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >>
  rpt IF_CASES_TAC >>
  simp[code_action_bind, code_action_ignore_bind, code_action_emit_op,
    code_action_emit_void, code_action_return]
QED

Resume abi_dyn_decode_code[bytes]:
  rpt (FIRST [
    CHANGED_TAC (ASM_SIMP_TAC std_ss
      [code_action_return, code_action_emit_op, code_action_emit_void]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule abi_dyn_code_if, irule abi_dyn_code_copy_case,
    irule code_action_emit_op, irule code_action_emit_void,
    gen_tac, conj_tac]) >> simp[] >>
  Cases_on `lop` >> simp[code_action_emit_void]
QED
Resume abi_dyn_decode_code[array]:
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info` >>
  rpt (FIRST [
    CHANGED_TAC (ASM_SIMP_TAC std_ss
      [LET_THM, code_action_return, code_action_alloc_buffer]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule abi_dyn_code_if,
    irule code_action_emit_op, irule code_action_emit_void,
    gen_tac, conj_tac]) >> simp[]
  >- (Cases_on `lop` >> simp[code_action_emit_void]) >>
  gvs[] >> irule code_action_alloc_buffer >> simp[]
QED
Resume abi_dyn_decode_code[complex]:
  Cases_on `hi = Lit 0w` >> gvs[LET_THM] >>
  rpt (FIRST [
    CHANGED_TAC (ASM_SIMP_TAC std_ss [code_action_return]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule code_action_emit_op, irule code_action_emit_void,
    gen_tac, conj_tac]) >> gvs[]
QED
Resume abi_dyn_decode_code[cons]:
  gvs[LET_THM] >>
  rpt (FIRST [
    CHANGED_TAC (ASM_SIMP_TAC std_ss [code_action_return]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule abi_dyn_code_if,
    irule code_action_emit_op, irule code_action_emit_void,
    gen_tac, conj_tac]) >> simp[]
QED
Resume abi_dyn_decode_code[loop]:
  gvs[LET_THM] >>
  rpt (FIRST [
    CHANGED_TAC (ASM_SIMP_TAC std_ss [code_action_return,
      code_action_fresh_label, code_action_new_block]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule abi_dyn_code_if,
    irule code_action_emit_op, irule code_action_emit_void,
    irule code_action_emit_inst,
    gen_tac, conj_tac]) >> simp[]
QED
Finalise abi_dyn_decode_code

(* Quotation-only instruction and action interfaces. *)
val dyn_F = ``\P a b. entry_shape a b /\ EVERY P (frag_code a b)``;
val dyn_O = ``\N i. EVERY (\x. ~var_below N x) i.inst_outputs``;
val dyn_fresh = ``\m. !N a r b. N <= a.cs_next_var /\ m a = (r,b) ==>
  (^dyn_F) ((^dyn_O) N) a b /\ a.cs_next_var <= b.cs_next_var``;
val dyn_fresh_op = inst [alpha |-> ``:operand``] dyn_fresh;
val dyn_fresh_unit = inst [alpha |-> ``:unit``] dyn_fresh;
val dyn_fresh_label = inst [alpha |-> ``:string``] dyn_fresh;
val dyn_fresh_buffer = inst [alpha |-> ``:buffer``] dyn_fresh;

Theorem abi_dyn_fixed_compose[local]:
  !P a b c. (^dyn_F) P a b /\ (^dyn_F) P b c ==> (^dyn_F) P a c
Proof
  simp_tac std_ss [] >> rpt strip_tac
  >- metis_tac[entry_shape_trans] >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >> simp[EVERY_APPEND]
QED

Theorem abi_dyn_fresh_bind[local]:
  !m f. (^dyn_fresh) m /\ (!x. (^(inst [alpha |-> beta] dyn_fresh)) (f x)) ==>
    (^(inst [alpha |-> beta] dyn_fresh)) (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  first_x_assum (qspecl_then [`N`, `a`, `q`, `r'`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `q` mp_tac) >>
  disch_then (qspecl_then [`N`, `r'`, `r`, `b`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  conj_tac >- (irule (SRULE [] abi_dyn_fixed_compose) >>
    qexists_tac `r'` >> simp[]) >> decide_tac
QED

Theorem abi_dyn_fresh_ignore_bind[local]:
  !m n. (^dyn_fresh) m /\ (^(inst [alpha |-> beta] dyn_fresh)) n ==>
    (^(inst [alpha |-> beta] dyn_fresh)) (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_fresh_bind) >> simp[] >> metis_tac[]
QED

Theorem abi_dyn_fresh_return[local]:
  !v. (^dyn_fresh) (comp_return v)
Proof
  simp[comp_return_def, entry_shape_refl, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem abi_dyn_fresh_emit_op[local]:
  !opc ops. (^dyn_fresh_op) (emit_op opc ops)
Proof
  simp_tac std_ss [emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       DROP_APPEND, mk_inst_def, var_below_fresh] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops
    [STRING #"%" (toString a.cs_next_var)]]` >> simp[]
QED

Theorem abi_dyn_fresh_emit_inst[local]:
  !opc ops. (^dyn_fresh_unit) (emit_inst opc ops [])
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       DROP_APPEND, mk_inst_def] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops []]` >> simp[]
QED

Theorem abi_dyn_fresh_emit_void[local]:
  !opc ops. (^dyn_fresh_unit) (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  metis_tac[BETA_RULE abi_dyn_fresh_emit_inst]
QED

Theorem abi_dyn_fresh_label[local]:
  !suffix. (^dyn_fresh_label) (fresh_label suffix)
Proof
  simp[fresh_label_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem abi_dyn_fresh_block[local]:
  !l. (^dyn_fresh_label) (new_block l)
Proof
  simp[new_block_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def] >>
  rpt strip_tac >> disj2_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]
QED

Theorem abi_dyn_fresh_alloc[local]:
  !size. (^dyn_fresh_buffer) (compile_alloc_buffer size)
Proof
  gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  ho_match_mp_tac (BETA_RULE abi_dyn_fresh_bind) >>
  conj_tac >- (MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_emit_op)) >>
  gen_tac >> MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_return)
QED

Theorem abi_dyn_fresh_if[local]:
  !b m n. (^dyn_fresh) m /\ (^dyn_fresh) n ==>
    (^dyn_fresh) (if b then m else n)
Proof
  Cases_on `b` >> simp[] >> metis_tac[]
QED

Theorem abi_dyn_fresh_copy_case[local]:
  !opc m n p. (^dyn_fresh) m /\ (^dyn_fresh) n /\ (^dyn_fresh) p ==>
    (^dyn_fresh) (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  Cases_on `opc` >> simp[] >> metis_tac[]
QED


Theorem abi_dyn_decode_fresh[local]:
  (!dst src lop base hi info.
    (^dyn_fresh_unit) (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    (^dyn_fresh_unit) (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    (^dyn_fresh_unit) (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^dyn_fresh_unit` >>
  qabbrev_tac `FrO = ^dyn_fresh_op` >>
  qabbrev_tac `B = ^dyn_fresh_buffer` >>
  qabbrev_tac `L = ^dyn_fresh_label` >>
  `(!m f. FrO m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. FrO (f x)) ==> FrO (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. B (f x)) ==> B (comp_bind m f)) /\
   (!m f. B m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. L m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. U m /\ (!x. U (f x)) ==> U (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_bind)) >>
  `(!m n. U m /\ U n ==> U (comp_ignore_bind m n)) /\
   (!m n. U m /\ FrO n ==> FrO (comp_ignore_bind m n)) /\
   (!m n. L m /\ U n ==> U (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_ignore_bind)) >>
  `(!opc ops. FrO (emit_op opc ops)) /\
   (!opc ops. U (emit_void opc ops)) /\
   (!opc ops. U (emit_inst opc ops [])) /\
   (!l. L (fresh_label l)) /\ (!l. L (new_block l)) /\
   (!sz. B (compile_alloc_buffer sz)) /\
   (!v. U (comp_return v)) /\ (!v. FrO (comp_return v)) /\
   (!v. B (comp_return v)) /\ (!v. L (comp_return v))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_fresh_emit_op, abi_dyn_fresh_emit_void, abi_dyn_fresh_emit_inst,
           abi_dyn_fresh_label, abi_dyn_fresh_block, abi_dyn_fresh_alloc,
           abi_dyn_fresh_return])) >>
  `!opc m n p. U m /\ U n /\ U p ==>
    U (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (Cases_on `opc` >> simp[]) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss []
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume abi_dyn_decode_fresh[word]:
  Cases_on `base' = Lit 0w` >> ASM_SIMP_TAC std_ss [] >>
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> rpt IF_CASES_TAC >>
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac])
QED

Resume abi_dyn_decode_fresh[bytes]:
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac])
QED
Resume abi_dyn_decode_fresh[array]:
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac]) >>
  gvs[] >> metis_tac[]
QED
Resume abi_dyn_decode_fresh[complex]:
  gvs[] >> rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac]) >> gvs[]
QED
Resume abi_dyn_decode_fresh[cons]:
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac])
QED
Resume abi_dyn_decode_fresh[loop]:
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    first_assum irule, IF_CASES_TAC, gen_tac, conj_tac])
QED
Finalise abi_dyn_decode_fresh

Theorem abi_dyn_body_middle_fresh[local]:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_op2.
    (^dyn_fresh_unit)
      (do src_data <- emit_op ADD [src_op; Lit 32w];
          src_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
          elem_src <- emit_op ADD [src_data; src_off];
          actual_src <-
            (if dec_info_needs_offset elem_info then
               compile_abi_decode_dyn_elem_ptr load_opc base_op elem_src
                 src_data hi_op elem_abi_sz
             else return elem_src);
          dst_data <- emit_op ADD [dst; Lit 32w];
          dst_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
          elem_dst <- emit_op ADD [dst_data; dst_off];
          compile_abi_decode_to_buf elem_dst actual_src
            load_opc base_op hi_op elem_info
       od)
Proof
  rpt gen_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_fresh)),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_emit_op),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_emit_void),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_fresh_return),
    CHANGED_TAC (simp_tac std_ss [LET_THM]),
    ho_match_mp_tac (BETA_RULE abi_dyn_fresh_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_fresh_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac])
QED

(* Literal branch targets and the blocks available in a completed fragment. *)
val dyn_J = ``\T i.
  (i.inst_opcode = JMP ==> ?l. i.inst_operands = [Label l] /\ l IN T) /\
  (i.inst_opcode = JNZ ==> ?v l r.
    i.inst_operands = [v; Label l; Label r] /\ l IN T /\ r IN T)``;
val dyn_B = ``\a b. {l | (?bb. MEM bb (emitted_blocks a b) /\ l = bb.bb_label) \/
                            l = b.cs_current_bb}``;

Theorem abi_dyn_emitted_compose[local]:
  !a b c. cs_extends a b /\ cs_extends b c ==>
    emitted_blocks a c = emitted_blocks b c ++ emitted_blocks a b
Proof
  simp_tac std_ss [cs_extends_def] >> rpt strip_tac >>
  `emitted_blocks a b = new` by (irule emitted_blocks_append >> simp[]) >>
  `emitted_blocks b c = new'` by (irule emitted_blocks_append >> simp[]) >>
  simp[] >> irule emitted_blocks_append >> simp[APPEND_ASSOC]
QED

Theorem abi_dyn_current_available[local]:
  !a b. cs_extends a b ==> a.cs_current_bb IN (^dyn_B) a b
Proof
  rpt strip_tac >> gvs[cs_extends_def] >>
  `emitted_blocks a b = new` by (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >> gvs[] >>
  simp[] >> disj1_tac >> qexists_tac `LAST (emitted_blocks a b)` >> simp[rich_listTheory.LAST_MEM]
QED

Theorem abi_dyn_available_compose[local]:
  !a b c. cs_extends a b /\ cs_extends b c ==>
    (^dyn_B) a b SUBSET (^dyn_B) a c /\
    (^dyn_B) b c SUBSET (^dyn_B) a c
Proof
  rpt strip_tac >> drule_all abi_dyn_emitted_compose >> strip_tac >>
  drule abi_dyn_current_available >>
  ASM_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, pred_setTheory.IN_GSPEC_IFF, MEM_APPEND] >>
  metis_tac[]
QED

Theorem abi_dyn_targets_mono[local]:
  !S T i. S SUBSET T /\ (^dyn_J) S i ==> (^dyn_J) T i
Proof
  simp_tac std_ss [pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_dyn_closed_compose[local]:
  !T a b c.
    (^dyn_F) ((^dyn_J) (T UNION (^dyn_B) a b)) a b /\
    (^dyn_F) ((^dyn_J) (T UNION (^dyn_B) b c)) b c ==>
    (^dyn_F) ((^dyn_J) (T UNION (^dyn_B) a c)) a c
Proof
  simp_tac std_ss [] >> rpt strip_tac
  >- metis_tac[entry_shape_trans] >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  drule_all abi_dyn_available_compose >> strip_tac >>
  `T' UNION (^dyn_B) a b SUBSET T' UNION (^dyn_B) a c /\
   T' UNION (^dyn_B) b c SUBSET T' UNION (^dyn_B) a c`
    by (fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >> simp_tac std_ss [EVERY_APPEND] >>
  conj_tac
  >- (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
      gen_tac >> strip_tac >> simp_tac std_ss [] >>
      irule (BETA_RULE abi_dyn_targets_mono) >>
      metis_tac[]) >>
  irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  gen_tac >> strip_tac >> simp_tac std_ss [] >>
      irule (BETA_RULE abi_dyn_targets_mono) >>
      metis_tac[]
QED

val dyn_closed = ``\T m. !a r b. m a = (r,b) ==>
  (^dyn_F) ((^dyn_J) (T UNION (^dyn_B) a b)) a b``;

Theorem abi_dyn_branchless_closed[local]:
  !m. code_action (\opc. opc <> JMP /\ opc <> JNZ) m ==>
    !T. (^dyn_closed) T m
Proof
  simp_tac std_ss [code_action_def, code_step_def] >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  simp[] >> irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_dyn_closed_bind[local]:
  !T m f. (^dyn_closed) T m /\
    (!x. (^(inst [alpha |-> beta] dyn_closed)) T (f x)) ==>
    (^(inst [alpha |-> beta] dyn_closed)) T (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule (SRULE [] (BETA_RULE abi_dyn_closed_compose)) >>
  qexists_tac `r'` >> simp[]
QED

Theorem abi_dyn_closed_ignore_bind[local]:
  !T m n. (^dyn_closed) T m /\
    (^(inst [alpha |-> beta] dyn_closed)) T n ==>
    (^(inst [alpha |-> beta] dyn_closed)) T (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >> simp[]
QED

Theorem abi_dyn_closed_return[local]:
  !T v. (^dyn_closed) T (comp_return v)
Proof
  rpt gen_tac >> qspec_then `comp_return v` mp_tac abi_dyn_branchless_closed >>
  simp[code_action_return]
QED

Theorem abi_dyn_closed_emit_op[local]:
  !T opc ops. opc <> JMP /\ opc <> JNZ ==>
    (^(inst [alpha |-> ``:operand``] dyn_closed)) T (emit_op opc ops)
Proof
  ntac 3 gen_tac >> strip_tac >>
  qspec_then `emit_op opc ops` mp_tac abi_dyn_branchless_closed >>
  simp[code_action_emit_op]
QED

Theorem abi_dyn_closed_emit_inst[local]:
  !T opc ops outs. (^dyn_J) T (mk_inst 0 opc ops outs) ==>
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T (emit_inst opc ops outs)
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, frag_code_def, emitted_blocks_def, emitted_insts_def,
       DROP_APPEND, mk_inst_def] >>
  metis_tac[]
QED

Theorem abi_dyn_closed_emit_void[local]:
  !T opc ops. (^dyn_J) T (mk_inst 0 opc ops []) ==>
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  metis_tac[BETA_RULE abi_dyn_closed_emit_inst]
QED

Theorem abi_dyn_closed_label[local]:
  !T suffix. (^(inst [alpha |-> ``:string``] dyn_closed)) T (fresh_label suffix)
Proof
  ntac 2 gen_tac >> qspec_then `fresh_label suffix` mp_tac abi_dyn_branchless_closed >>
  simp[code_action_fresh_label]
QED

Theorem abi_dyn_closed_block[local]:
  !T l. (^(inst [alpha |-> ``:string``] dyn_closed)) T (new_block l)
Proof
  ntac 2 gen_tac >> qspec_then `new_block l` mp_tac abi_dyn_branchless_closed >>
  simp[code_action_new_block]
QED

Theorem abi_dyn_closed_alloc[local]:
  !T size. (^(inst [alpha |-> ``:buffer``] dyn_closed)) T (compile_alloc_buffer size)
Proof
  qx_gen_tac `targets` >> qx_gen_tac `sz` >>
  qspec_then `compile_alloc_buffer sz` mp_tac abi_dyn_branchless_closed >>
  simp[code_action_alloc_buffer]
QED

Theorem abi_dyn_targets_discharge[local]:
  !T U a b. (^dyn_F) ((^dyn_J) ((T UNION U) UNION (^dyn_B) a b)) a b /\
    U SUBSET (^dyn_B) a b ==>
    (^dyn_F) ((^dyn_J) (T UNION (^dyn_B) a b)) a b
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `(T' UNION U) UNION (^dyn_B) a b = T' UNION (^dyn_B) a b`
    by (BETA_TAC >> ASM_SET_TAC[]) >>
  pop_assum (fn th => rule_assum_tac (PURE_REWRITE_RULE [BETA_RULE th])) >> simp[]
QED

Theorem abi_dyn_switch_shape[local]:
  !l a r b. new_block l a = (r,b) ==>
    entry_shape a b /\ b.cs_current_bb = l
Proof
  simp[new_block_def, entry_shape_def] >> rpt strip_tac >>
  disj2_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]
QED

Theorem abi_dyn_marked_available[local]:
  !a b c. entry_shape a b /\ entry_shape b c ==>
    b.cs_current_bb IN (^dyn_B) a c
Proof
  rpt strip_tac >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  drule_all abi_dyn_available_compose >>
  drule_all abi_dyn_current_available >>
  simp_tac std_ss [pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

val dyn_skel = ``\hdr body exit (p:compile_state -> unit # compile_state)
    (h:compile_state -> unit # compile_state) (q:compile_state -> unit # compile_state).
  do p; new_block hdr; h; new_block body; q; new_block exit; return () od``;

Theorem abi_dyn_skeleton_closed[local]:
  !T hdr body exit p h q.
    (^(inst [alpha |-> ``:unit``] dyn_closed)) (T UNION {hdr;body;exit}) p /\
    (^(inst [alpha |-> ``:unit``] dyn_closed)) (T UNION {hdr;body;exit}) h /\
    (^(inst [alpha |-> ``:unit``] dyn_closed)) (T UNION {hdr;body;exit}) q ==>
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T ((^dyn_skel) hdr body exit p h q)
Proof
  map_every qx_gen_tac [`targets`, `lh`, `lb`, `le`, `p`, `h`, `q`] >> strip_tac >>
  `(^(inst [alpha |-> ``:unit``] dyn_closed)) (targets UNION {lh;lb;le}) ((^dyn_skel) lh lb le p h q)` by
    (rule_assum_tac BETA_RULE >> simp_tac std_ss [] >> rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
      ho_match_mp_tac (BETA_RULE abi_dyn_closed_ignore_bind),
      MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_block),
      MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return), conj_tac])) >>
  simp_tac std_ss [] >> rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_targets_discharge) >>
  qexists_tac `{lh;lb;le}` >> conj_tac
  >- gvs[] >>
  suspend "available"
QED

Resume abi_dyn_skeleton_closed[available]:
  qpat_x_assum `do _ od a = _` mp_tac >>
  simp_tac std_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rule_assum_tac BETA_RULE >>
  rpt (first_x_assum drule >> strip_tac) >>
  imp_res_tac abi_dyn_switch_shape >>
  qpat_x_assum `!a b. _` kall_tac >>
  rpt (qpat_x_assum `EVERY _ _` kall_tac) >>
  rpt conj_tac >> metis_tac[SRULE [] (BETA_RULE abi_dyn_marked_available), entry_shape_trans]
QED
Finalise abi_dyn_skeleton_closed

val dyn_loop_header = ``\ip base src lop.
  do i <- emit_op MLOAD [ip];
     addr <- compile_abi_dec_addr base src;
     cnt <- emit_op lop [addr];
     cmp <- emit_op LT [i;cnt];
     done_op <- emit_op ISZERO [cmp];
     return done_op od``;
val dyn_loop_body = ``\dst src lop base hi info asz msz ip.
  do i <- emit_op MLOAD [ip];
     data <- emit_op ADD [src; Lit 32w];
     off <- emit_op MUL [i; Lit (n2w asz)];
     elem_src <- emit_op ADD [data; off];
     actual_src <- (if dec_info_needs_offset info then
       compile_abi_decode_dyn_elem_ptr lop base elem_src data hi asz
       else return elem_src);
     dst_data <- emit_op ADD [dst; Lit 32w];
     dst_off <- emit_op MUL [i; Lit (n2w msz)];
     elem_dst <- emit_op ADD [dst_data; dst_off];
     compile_abi_decode_to_buf elem_dst actual_src lop base hi info;
     new_i <- emit_op ADD [i; Lit 1w];
     emit_void MSTORE [ip; new_i] od``;

Theorem abi_dyn_loop_skeleton[local]:
  !dst src lop base hi info asz msz ip cnt.
  compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt =
  do lh <- fresh_label "dec_dyn_hdr";
     lb <- fresh_label "dec_dyn_body";
     le <- fresh_label "dec_dyn_exit";
     (^dyn_skel) lh lb le (emit_inst JMP [Label lh] [])
       (do done_op <- (^dyn_loop_header) ip base src lop;
           emit_inst JNZ [done_op; Label le; Label lb] [] od)
       (do (^dyn_loop_body) dst src lop base hi info asz msz ip;
           emit_inst JMP [Label lh] [] od) od
Proof
  simp_tac std_ss [Once compile_abi_decode_to_buf_def, LET_THM,
    comp_ignore_bind_def, compileEnvTheory.comp_bind_assoc,
    comp_bind_return]
QED

Theorem abi_dyn_loop_closed[local]:
  !dst src lop base hi info asz msz ip cnt.
    lop <> JMP /\ lop <> JNZ /\
    (!T d s. (^(inst [alpha |-> ``:unit``] dyn_closed)) T (compile_abi_decode_to_buf d s lop base hi info)) ==>
    !T. (^(inst [alpha |-> ``:unit``] dyn_closed)) T
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp_tac std_ss [abi_dyn_loop_skeleton] >>
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
  conj_tac >- (MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label)) >> gen_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
  conj_tac >- (MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label)) >> gen_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
  conj_tac >- (MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label)) >> gen_tac >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_skeleton_closed) >>
  rpt conj_tac
  >- (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_inst) >> simp[mk_inst_def])
  >- suspend "header"
  >> suspend "body"
QED

Resume abi_dyn_loop_closed[header]:
  simp_tac std_ss [compile_abi_dec_addr_def] >>
  rpt (FIRST [CHANGED_TAC BETA_TAC,
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op) >> simp[]),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_inst) >> simp[mk_inst_def]),
    MATCH_MP_TAC (BETA_RULE abi_dyn_closed_bind), conj_tac, gen_tac,
    IF_CASES_TAC])
QED
Resume abi_dyn_loop_closed[body]:
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def] >>
  rpt (FIRST [CHANGED_TAC BETA_TAC,
    first_assum (MATCH_ACCEPT_TAC o BETA_RULE),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op) >> simp[]),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_inst) >> simp[mk_inst_def]),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_void) >> simp[mk_inst_def]),
    MATCH_MP_TAC (BETA_RULE abi_dyn_closed_bind),
    MATCH_MP_TAC (BETA_RULE abi_dyn_closed_ignore_bind),
    conj_tac, gen_tac, IF_CASES_TAC])
QED
Finalise abi_dyn_loop_closed

(* Typed structural dispatch: the output predicate and bound-action type
   distinguish all composition rules before any rule is applied. *)
fun dyn_certificate_tac g = ASSUM_LIST (fn ths =>
  let
    fun body t =
      if boolSyntax.is_forall t then body (#2 (boolSyntax.dest_forall t))
      else if boolSyntax.is_imp t then body (#2 (boolSyntax.dest_imp t))
      else t
    fun key t =
      let val (pred,args) = strip_comb (body t)
          val (h,acts) = strip_comb (List.last args)
          val name = fst (dest_const h)
          val input = if name = "monad_bind" orelse name = "comp_bind"
                         orelse name = "comp_ignore_bind"
                      then type_to_string (type_of (hd acts)) else ""
      in (fst (dest_var pred), name, input) end
    val rules = List.mapPartial (fn th =>
      SOME (key (concl th), th) handle HOL_ERR _ => NONE | Empty => NONE) ths
    fun walk g =
      (if boolSyntax.is_forall (#2 g) then (gen_tac >> walk) g
      else if boolSyntax.is_conj (#2 g) then (conj_tac >> walk) g
      else if boolSyntax.is_neg (#2 g) then simp[] g
      else if pred_setSyntax.is_in (#2 g) then simp[] g
      else
        let val k = key (#2 g) handle HOL_ERR e =>
              (print "Cannot key certificate: "; print_term (#2 g); raise HOL_ERR e)
            val matching = map #2 (List.filter (fn (k',_) => k' = k) rules)
            val _ = if null matching then
              (print "No typed certificate rule: "; print_term (#2 g)) else ()
            fun apply g = FIRST (map MATCH_ACCEPT_TAC matching @ map MATCH_MP_TAC matching) g
              handle HOL_ERR e => (print ("Typed rule failed (" ^ Int.toString (length matching) ^ "): ");
                                   print_term (#2 g); raise HOL_ERR e)
        in if #2 k = "LET" then (pure_rewrite_tac [LET_THM] >> BETA_TAC >> walk) g
           else (apply >> BETA_TAC >> walk) g end)
  in walk end) g;

Theorem abi_dyn_closed_if[local]:
  !T p m n. (^dyn_closed) T m /\ (^dyn_closed) T n ==>
    (^dyn_closed) T (if p then m else n)
Proof
  Cases_on `p` >> simp[]
QED

Theorem abi_dyn_closed_copy_case[local]:
  !T opc m n p. (^dyn_closed) T m /\ (^dyn_closed) T n /\ (^dyn_closed) T p ==>
    (^dyn_closed) T (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `opc` >> pure_rewrite_tac[opcode_case_def] >>
  metis_tac[]
QED

Theorem abi_dyn_decode_closed[local]:
  (!dst src lop base hi info.
    lop <> JMP /\ lop <> JNZ ==> !T.
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    lop <> JMP /\ lop <> JNZ ==> !T.
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    lop <> JMP /\ lop <> JNZ ==> !T.
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^(inst [alpha |-> ``:unit``] dyn_closed)` >>
  qabbrev_tac `FrO = ^(inst [alpha |-> ``:operand``] dyn_closed)` >>
  qabbrev_tac `B = ^(inst [alpha |-> ``:buffer``] dyn_closed)` >>
  qabbrev_tac `L = ^(inst [alpha |-> ``:string``] dyn_closed)` >>
  `(!T m f. FrO T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. FrO T (f x)) ==> FrO T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. B T (f x)) ==> B T (comp_bind m f)) /\
   (!T m f. B T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. L T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. U T m /\ (!x. U T (f x)) ==> U T (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_bind)) >>
  `(!T m n. U T m /\ U T n ==> U T (comp_ignore_bind m n)) /\
   (!T m n. U T m /\ FrO T n ==> FrO T (comp_ignore_bind m n)) /\
   (!T m n. L T m /\ U T n ==> U T (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_ignore_bind)) >>
  `(!T opc ops. opc <> JMP /\ opc <> JNZ ==> FrO T (emit_op opc ops)) /\
   (!T opc ops. opc <> JMP /\ opc <> JNZ ==> U T (emit_void opc ops)) /\
   (!T l. L T (fresh_label l)) /\ (!T l. L T (new_block l)) /\
   (!T sz. B T (compile_alloc_buffer sz)) /\
   (!T v. U T (comp_return v)) /\ (!T v. FrO T (comp_return v)) /\
   (!T v. B T (comp_return v)) /\ (!T v. L T (comp_return v))`
    by (rpt conj_tac >>
        simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_closed_label, abi_dyn_closed_block,
           abi_dyn_closed_alloc, abi_dyn_closed_return] @
          [ntac 3 gen_tac >> strip_tac >>
           FIRST [MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op),
                  MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_void)] >>
           simp[mk_inst_def]])) >>
  `(!T p m n. U T m /\ U T n ==> U T (if p then m else n)) /\
   (!T p m n. FrO T m /\ FrO T n ==> FrO T (if p then m else n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_if)) >>
  `!T opc m n p. U T m /\ U T n /\ U T p ==>
    U T (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_copy_case)) >>
  `!dst src lop base hi info asz msz ip cnt.
    lop <> JMP /\ lop <> JNZ /\
    (!T d s. U T (compile_abi_decode_to_buf d s lop base hi info)) ==>
    !T. U T (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_loop_closed)) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss []
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume abi_dyn_decode_closed[word]:
  qpat_assum `!T m f. FrO T m /\ (!x. U T (f x)) ==> U T (monad_bind m f)` MATCH_MP_TAC >>
  conj_tac
  >- (qpat_assum `!T p m n. FrO T m /\ FrO T n ==> FrO T (if p then m else n)` MATCH_MP_TAC >>
      conj_tac
      >- (qpat_assum `!T v. FrO T (comp_return v)` MATCH_ACCEPT_TAC) >>
      qpat_assum `!T opc ops. opc <> JMP /\ opc <> JNZ ==> FrO T (emit_op opc ops)` MATCH_MP_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  qpat_assum `!T m f. FrO T m /\ (!x. U T (f x)) ==> U T (monad_bind m f)` MATCH_MP_TAC >>
  conj_tac
  >- (qpat_assum `!T opc ops. opc <> JMP /\ opc <> JNZ ==> FrO T (emit_op opc ops)` MATCH_MP_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  qpat_assum `!T m n. U T m /\ U T n ==> U T (comp_ignore_bind m n)` MATCH_MP_TAC >>
  reverse conj_tac
  >- (qpat_assum `!T opc ops. opc <> JMP /\ opc <> JNZ ==> U T (emit_void opc ops)` MATCH_MP_TAC >> simp[]) >>
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> simp[]
QED
Resume abi_dyn_decode_closed[bytes]:
  dyn_certificate_tac
QED
Resume abi_dyn_decode_closed[array]:
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info`
  >- (ASM_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` mp_tac >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_closed[complex]:
  Cases_on `hi = Lit 0w` >>
  FULL_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_closed[cons]:
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_closed[loop]:
  `U T' (compile_abi_decode_dyn_loop dst src lop base' hi info asz msz ip cnt)`
    suffices_by (simp_tac std_ss [Once compile_abi_decode_to_buf_def,
      compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
      compile_abi_decode_dyn_elem_ptr_def]) >>
  qpat_x_assum `!is_dyn_elem dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >> dyn_certificate_tac
QED
Finalise abi_dyn_decode_closed

(* Label provenance, with previously allocated labels carried ambiently. *)
val dyn_I = ``\lo hi. {l | ?suffix k. lo <= k /\ k < hi /\
  l = fresh_label_output suffix k}``;
val dyn_span = ``\A a b. entry_shape a b /\
  a.cs_next_label <= b.cs_next_label /\
  (^dyn_B) a b SUBSET ({a.cs_current_bb} UNION A UNION
    (^dyn_I) a.cs_next_label b.cs_next_label)``;
val dyn_prov = ``\A m. !a r b. m a = (r,b) ==> (^dyn_span) A a b``;

Theorem abi_dyn_interval_mono[local]:
  !lo hi lo' hi'. lo' <= lo /\ hi <= hi' ==>
    (^dyn_I) lo hi SUBSET (^dyn_I) lo' hi'
Proof
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  qexistsl_tac [`suffix`, `k`] >> simp[]
QED

Theorem abi_dyn_available_cover[local]:
  !a b c. entry_shape a b /\ entry_shape b c ==>
    (^dyn_B) a c SUBSET ((^dyn_B) a b UNION (^dyn_B) b c)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  drule_all abi_dyn_emitted_compose >> strip_tac >>
  simp[pred_setTheory.SUBSET_DEF, MEM_APPEND] >> metis_tac[]
QED

Theorem abi_dyn_span_compose[local]:
  !A a b c. (^dyn_span) A a b /\ (^dyn_span) A b c ==>
    (^dyn_span) A a c
Proof
  simp_tac std_ss [] >> rpt gen_tac >> strip_tac >>
  `entry_shape a c` by metis_tac[entry_shape_trans] >>
  `a.cs_next_label <= c.cs_next_label` by decide_tac >>
  `(^dyn_B) a c SUBSET ((^dyn_B) a b UNION (^dyn_B) b c)`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_available_cover) >> simp[]) >>
  `(^dyn_I) a.cs_next_label b.cs_next_label SUBSET
     (^dyn_I) a.cs_next_label c.cs_next_label`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_interval_mono) >> simp[]) >>
  `(^dyn_I) b.cs_next_label c.cs_next_label SUBSET
     (^dyn_I) a.cs_next_label c.cs_next_label`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_interval_mono) >> simp[]) >>
  `b.cs_current_bb IN (^dyn_B) a b` by simp[] >>
  RULE_ASSUM_TAC BETA_RULE >>
  qmatch_asmsub_abbrev_tac `xx SUBSET ({a.cs_current_bb} UNION A UNION ii)` >>
  qmatch_asmsub_abbrev_tac `yy SUBSET ({b.cs_current_bb} UNION A UNION jj)` >>
  qmatch_goalsub_abbrev_tac `zz SUBSET ({a.cs_current_bb} UNION A UNION kk)` >>
  simp_tac std_ss [] >>
  qpat_x_assum `Abbrev (xx = _)` kall_tac >>
  qpat_x_assum `Abbrev (yy = _)` kall_tac >>
  qpat_x_assum `Abbrev (zz = _)` kall_tac >>
  qpat_x_assum `Abbrev (ii = _)` kall_tac >>
  qpat_x_assum `Abbrev (jj = _)` kall_tac >>
  qpat_x_assum `Abbrev (kk = _)` kall_tac >>
  ASM_SET_TAC []
QED

Theorem abi_dyn_prov_bind[local]:
  !A m f. (^dyn_prov) A m /\
    (!x. (^(inst [alpha |-> beta] dyn_prov)) A (f x)) ==>
    (^(inst [alpha |-> beta] dyn_prov)) A (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule (SRULE [] (BETA_RULE abi_dyn_span_compose)) >>
  qexists_tac `r'` >> simp[]
QED

Theorem abi_dyn_prov_ignore_bind[local]:
  !A m n. (^dyn_prov) A m /\
    (^(inst [alpha |-> beta] dyn_prov)) A n ==>
    (^(inst [alpha |-> beta] dyn_prov)) A (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_prov_bind) >> simp[]
QED

Theorem abi_dyn_prov_return[local]:
  !A v. (^dyn_prov) A (comp_return v)
Proof
  simp[comp_return_def, entry_shape_refl, emitted_blocks_def]
QED

Theorem abi_dyn_prov_emit_op[local]:
  !A opc ops. (^(inst [alpha |-> ``:operand``] dyn_prov)) A (emit_op opc ops)
Proof
  simp_tac std_ss [emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, emitted_blocks_def] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops
    [STRING #"%" (toString a.cs_next_var)]]` >> simp[]
QED

Theorem abi_dyn_prov_emit_inst[local]:
  !A opc ops outs. (^(inst [alpha |-> ``:unit``] dyn_prov)) A (emit_inst opc ops outs)
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[entry_shape_def, emitted_blocks_def] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops outs]` >> simp[]
QED

Theorem abi_dyn_prov_emit_void[local]:
  !A opc ops. (^(inst [alpha |-> ``:unit``] dyn_prov)) A (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_emit_inst)
QED

Theorem abi_dyn_prov_block[local]:
  !A l. l IN A ==>
    (^(inst [alpha |-> ``:string``] dyn_prov)) A (new_block l)
Proof
  simp[new_block_def, entry_shape_def, emitted_blocks_def] >>
  rpt strip_tac >> ASM_SET_TAC []
QED

Theorem abi_dyn_prov_fresh_label_bind[local]:
  !A suffix f. (!l. (^dyn_prov) (A UNION {l}) (f l)) ==>
    (^dyn_prov) A (comp_bind (fresh_label suffix) f)
Proof
  simp_tac std_ss [comp_bind_def, fresh_label_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[] >>
  `entry_shape a b` by fs[entry_shape_def] >>
  `a.cs_next_label <= b.cs_next_label` by decide_tac >>
  `(^dyn_I) (a.cs_next_label + 1) b.cs_next_label SUBSET
     (^dyn_I) a.cs_next_label b.cs_next_label`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_interval_mono) >> simp[]) >>
  fs[emitted_blocks_def] >>
  qmatch_asmsub_abbrev_tac `xx SUBSET ({a.cs_current_bb} UNION _ UNION ii)` >>
  qmatch_goalsub_abbrev_tac `xx SUBSET ({a.cs_current_bb} UNION A UNION jj)` >>
  `fresh_label_output suffix a.cs_next_label IN jj`
    by (simp[Abbr `jj`] >> qexistsl_tac [`suffix`, `a.cs_next_label`] >> simp[]) >>
  qpat_x_assum `Abbrev (xx = _)` kall_tac >>
  qpat_x_assum `Abbrev (ii = _)` kall_tac >>
  qpat_x_assum `Abbrev (jj = _)` kall_tac >> ASM_SET_TAC []
QED

Theorem abi_dyn_prov_alloc[local]:
  !A size. (^(inst [alpha |-> ``:buffer``] dyn_prov)) A (compile_alloc_buffer size)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_prov_bind) >> conj_tac
  >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_emit_op) >>
  gen_tac >> BETA_TAC >> MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_return)
QED

Theorem abi_dyn_prov_if[local]:
  !A p m n. (^dyn_prov) A m /\ (^dyn_prov) A n ==>
    (^dyn_prov) A (if p then m else n)
Proof
  Cases_on `p` >> simp[]
QED

Theorem abi_dyn_prov_copy_case[local]:
  !A opc m n p. (^dyn_prov) A m /\ (^dyn_prov) A n /\ (^dyn_prov) A p ==>
    (^dyn_prov) A (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `opc` >> pure_rewrite_tac[opcode_case_def] >> metis_tac[]
QED

Theorem abi_dyn_decode_provenance[local]:
  (!dst src lop base hi info. !A.
    (^(inst [alpha |-> ``:unit``] dyn_prov)) A
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo. !A.
    (^(inst [alpha |-> ``:unit``] dyn_prov)) A
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt. !A.
    (^(inst [alpha |-> ``:unit``] dyn_prov)) A
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^(inst [alpha |-> ``:unit``] dyn_prov)` >>
  qabbrev_tac `FrO = ^(inst [alpha |-> ``:operand``] dyn_prov)` >>
  qabbrev_tac `B = ^(inst [alpha |-> ``:buffer``] dyn_prov)` >>
  qabbrev_tac `L = ^(inst [alpha |-> ``:string``] dyn_prov)` >>
  `(!T m f. FrO T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. FrO T (f x)) ==> FrO T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. B T (f x)) ==> B T (comp_bind m f)) /\
   (!T m f. B T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. U T m /\ (!x. U T (f x)) ==> U T (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_bind)) >>
  `(!T suffix f. (!l. U (T UNION {l}) (f l)) ==>
      U T (comp_bind (fresh_label suffix) f))`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_fresh_label_bind)) >>
  `(!T m n. U T m /\ U T n ==> U T (comp_ignore_bind m n)) /\
   (!T m n. U T m /\ FrO T n ==> FrO T (comp_ignore_bind m n)) /\
   (!T m n. L T m /\ U T n ==> U T (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_ignore_bind)) >>
  `(!T opc ops. FrO T (emit_op opc ops)) /\
   (!T opc ops. U T (emit_void opc ops)) /\
   (!T opc ops. U T (emit_inst opc ops [])) /\
   (!T l. l IN T ==> L T (new_block l)) /\
   (!T sz. B T (compile_alloc_buffer sz)) /\
   (!T v. U T (comp_return v)) /\ (!T v. FrO T (comp_return v)) /\
   (!T v. B T (comp_return v)) /\ (!T v. L T (comp_return v))`
    by (rpt conj_tac >>
        simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_prov_emit_op, abi_dyn_prov_emit_void, abi_dyn_prov_emit_inst,
           abi_dyn_prov_block, abi_dyn_prov_alloc, abi_dyn_prov_return])) >>
  `(!T p m n. U T m /\ U T n ==> U T (if p then m else n)) /\
   (!T p m n. FrO T m /\ FrO T n ==> FrO T (if p then m else n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_if)) >>
  `!T opc m n p. U T m /\ U T n /\ U T p ==>
    U T (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_copy_case)) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss []
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume abi_dyn_decode_provenance[word]:
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> simp[] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_provenance[bytes]:
  dyn_certificate_tac
QED
Resume abi_dyn_decode_provenance[array]:
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info`
  >- (ASM_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` mp_tac >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_provenance[complex]:
  Cases_on `hi = Lit 0w` >>
  FULL_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_provenance[cons]:
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_provenance[loop]:
  qpat_x_assum `!is_dyn_elem dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >> dyn_certificate_tac
QED
Finalise abi_dyn_decode_provenance

(* Fresh branch targets, carried ambiently until their allocating bind. *)
val dyn_target_span = ``\A a b. entry_shape a b /\
  a.cs_next_label <= b.cs_next_label /\
  EVERY ((^dyn_J) (A UNION (^dyn_I) a.cs_next_label b.cs_next_label))
    (frag_code a b)``;
val dyn_target = ``\A m. !a r b. m a = (r,b) ==>
  (^dyn_target_span) A a b``;

Theorem abi_dyn_target_compose[local]:
  !A a b c. (^dyn_target_span) A a b /\ (^dyn_target_span) A b c ==>
    (^dyn_target_span) A a c
Proof
  simp_tac std_ss [] >> rpt gen_tac >> strip_tac >>
  `entry_shape a c` by metis_tac[entry_shape_trans] >>
  `a.cs_next_label <= c.cs_next_label` by decide_tac >> ASM_SIMP_TAC std_ss [] >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  `(^dyn_I) a.cs_next_label b.cs_next_label SUBSET
    (^dyn_I) a.cs_next_label c.cs_next_label /\
   (^dyn_I) b.cs_next_label c.cs_next_label SUBSET
    (^dyn_I) a.cs_next_label c.cs_next_label`
    by (BETA_TAC >> conj_tac >> irule (BETA_RULE abi_dyn_interval_mono) >> simp[]) >>
  `A UNION (^dyn_I) a.cs_next_label b.cs_next_label SUBSET
     A UNION (^dyn_I) a.cs_next_label c.cs_next_label /\
   A UNION (^dyn_I) b.cs_next_label c.cs_next_label SUBSET
     A UNION (^dyn_I) a.cs_next_label c.cs_next_label`
    by ASM_SET_TAC[] >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >>
  simp_tac std_ss [EVERY_APPEND] >> conj_tac
  >- (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
      gen_tac >> strip_tac >> simp_tac std_ss [] >>
      irule (BETA_RULE abi_dyn_targets_mono) >>
      qexists_tac `A UNION (^dyn_I) a.cs_next_label b.cs_next_label` >>
      BETA_TAC >> rule_assum_tac BETA_RULE >> ASM_SIMP_TAC std_ss []) >>
  irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  gen_tac >> strip_tac >> simp_tac std_ss [] >>
  irule (BETA_RULE abi_dyn_targets_mono) >>
  qexists_tac `A UNION (^dyn_I) b.cs_next_label c.cs_next_label` >>
  BETA_TAC >> rule_assum_tac BETA_RULE >> ASM_SIMP_TAC std_ss []
QED

Theorem abi_dyn_target_bind[local]:
  !A m f. (^dyn_target) A m /\
    (!x. (^(inst [alpha |-> beta] dyn_target)) A (f x)) ==>
    (^(inst [alpha |-> beta] dyn_target)) A (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  irule (SRULE [] (BETA_RULE abi_dyn_target_compose)) >>
  qexists_tac `r'` >> simp[]
QED

Theorem abi_dyn_target_ignore_bind[local]:
  !A m n. (^dyn_target) A m /\
    (^(inst [alpha |-> beta] dyn_target)) A n ==>
    (^(inst [alpha |-> beta] dyn_target)) A (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_target_bind) >> simp[]
QED

Theorem abi_dyn_target_return[local]:
  !A v. (^dyn_target) A (comp_return v)
Proof
  simp[comp_return_def, entry_shape_refl, frag_code_def,
    emitted_insts_def, emitted_blocks_def]
QED

Theorem abi_dyn_target_emit_op[local]:
  !A opc ops. opc <> JMP /\ opc <> JNZ ==>
    (^(inst [alpha |-> ``:operand``] dyn_target)) A (emit_op opc ops)
Proof
  simp_tac std_ss [emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, frag_code_def, emitted_insts_def,
    emitted_blocks_def, mk_inst_def, DROP_APPEND]
QED

Theorem abi_dyn_target_emit_inst[local]:
  !A opc ops outs. (^dyn_J) A (mk_inst 0 opc ops outs) ==>
    (^(inst [alpha |-> ``:unit``] dyn_target)) A (emit_inst opc ops outs)
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, frag_code_def, emitted_insts_def,
    emitted_blocks_def, mk_inst_def, DROP_APPEND] >> metis_tac[]
QED

Theorem abi_dyn_target_emit_void[local]:
  !A opc ops. (^dyn_J) A (mk_inst 0 opc ops []) ==>
    (^(inst [alpha |-> ``:unit``] dyn_target)) A (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_emit_inst)
QED

Theorem abi_dyn_target_block[local]:
  !A l. (^(inst [alpha |-> ``:string``] dyn_target)) A (new_block l)
Proof
  simp[new_block_def, entry_shape_def, frag_code_def, emitted_insts_def,
    emitted_blocks_def] >> rpt strip_tac >>
  disj2_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]
QED

Theorem abi_dyn_target_fresh_label_bind[local]:
  !A suffix f. (!l. (^dyn_target) (A UNION {l}) (f l)) ==>
    (^dyn_target) A (comp_bind (fresh_label suffix) f)
Proof
  simp_tac std_ss [comp_bind_def, fresh_label_def, LET_THM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[Excl "IN_UNION", Excl "IN_INSERT"] >>
  `entry_shape a b` by fs[entry_shape_def] >>
  `a.cs_next_label <= b.cs_next_label` by decide_tac >>
  ASM_SIMP_TAC std_ss [] >>
  `A UNION {fresh_label_output suffix a.cs_next_label} UNION
      (^dyn_I) (a.cs_next_label + 1) b.cs_next_label SUBSET
    A UNION (^dyn_I) a.cs_next_label b.cs_next_label`
    by (`(^dyn_I) (a.cs_next_label + 1) b.cs_next_label SUBSET
           (^dyn_I) a.cs_next_label b.cs_next_label`
          by (BETA_TAC >> irule (BETA_RULE abi_dyn_interval_mono) >> simp[]) >>
        `fresh_label_output suffix a.cs_next_label IN
           (^dyn_I) a.cs_next_label b.cs_next_label`
          by (simp[] >> qexistsl_tac [`suffix`, `a.cs_next_label`] >> simp[]) >>
        ASM_SET_TAC[]) >>
  `frag_code (a with cs_next_label := a.cs_next_label + 1) b = frag_code a b`
    by simp[frag_code_def, emitted_insts_def, emitted_blocks_def] >>
  qpat_x_assum `frag_code _ _ = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  gen_tac >> strip_tac >> simp_tac std_ss [] >>
  irule (BETA_RULE abi_dyn_targets_mono) >>
  qexists_tac `A UNION {fresh_label_output suffix a.cs_next_label} UNION
      (^dyn_I) (a.cs_next_label + 1) b.cs_next_label` >>
  BETA_TAC >> rule_assum_tac BETA_RULE >> ASM_SIMP_TAC std_ss []
QED

Theorem abi_dyn_target_alloc[local]:
  !A size. (^(inst [alpha |-> ``:buffer``] dyn_target)) A (compile_alloc_buffer size)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_target_bind) >> conj_tac
  >- (MATCH_MP_TAC (BETA_RULE abi_dyn_target_emit_op) >> simp[]) >>
  gen_tac >> BETA_TAC >> MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_return)
QED

Theorem abi_dyn_target_if[local]:
  !A p m n. (^dyn_target) A m /\ (^dyn_target) A n ==>
    (^dyn_target) A (if p then m else n)
Proof
  Cases_on `p` >> simp[]
QED

Theorem abi_dyn_target_copy_case[local]:
  !A opc m n p. (^dyn_target) A m /\ (^dyn_target) A n /\ (^dyn_target) A p ==>
    (^dyn_target) A (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `opc` >> pure_rewrite_tac[opcode_case_def] >> metis_tac[]
QED

Theorem abi_dyn_decode_targets[local]:
  (!dst src lop base hi info. lop <> JMP /\ lop <> JNZ ==> !A.
    (^(inst [alpha |-> ``:unit``] dyn_target)) A
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo. lop <> JMP /\ lop <> JNZ ==> !A.
    (^(inst [alpha |-> ``:unit``] dyn_target)) A
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt. lop <> JMP /\ lop <> JNZ ==> !A.
    (^(inst [alpha |-> ``:unit``] dyn_target)) A
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^(inst [alpha |-> ``:unit``] dyn_target)` >>
  qabbrev_tac `FrO = ^(inst [alpha |-> ``:operand``] dyn_target)` >>
  qabbrev_tac `B = ^(inst [alpha |-> ``:buffer``] dyn_target)` >>
  qabbrev_tac `L = ^(inst [alpha |-> ``:string``] dyn_target)` >>
  `(!T m f. FrO T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. FrO T (f x)) ==> FrO T (comp_bind m f)) /\
   (!T m f. FrO T m /\ (!x. B T (f x)) ==> B T (comp_bind m f)) /\
   (!T m f. B T m /\ (!x. U T (f x)) ==> U T (comp_bind m f)) /\
   (!T m f. U T m /\ (!x. U T (f x)) ==> U T (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_bind)) >>
  `(!T suffix f. (!l. U (T UNION {l}) (f l)) ==>
      U T (comp_bind (fresh_label suffix) f))`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_fresh_label_bind)) >>
  `(!T m n. U T m /\ U T n ==> U T (comp_ignore_bind m n)) /\
   (!T m n. U T m /\ FrO T n ==> FrO T (comp_ignore_bind m n)) /\
   (!T m n. L T m /\ U T n ==> U T (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_ignore_bind)) >>
  `(!T opc ops. opc <> JMP /\ opc <> JNZ ==> FrO T (emit_op opc ops)) /\
   (!T opc ops. opc <> JMP /\ opc <> JNZ ==> U T (emit_void opc ops)) /\
   (!T l. l IN T ==> U T (emit_inst JMP [Label l] [])) /\
   (!T v l r. l IN T /\ r IN T ==> U T (emit_inst JNZ [v; Label l; Label r] [])) /\
   (!T l. L T (new_block l)) /\
   (!T sz. B T (compile_alloc_buffer sz)) /\
   (!T v. U T (comp_return v)) /\ (!T v. FrO T (comp_return v)) /\
   (!T v. B T (comp_return v)) /\ (!T v. L T (comp_return v))`
    by (rpt conj_tac >>
        simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_target_emit_op, abi_dyn_target_block,
           abi_dyn_target_alloc, abi_dyn_target_return] @
          [rpt gen_tac >> strip_tac >>
           FIRST [MATCH_MP_TAC (BETA_RULE abi_dyn_target_emit_void),
                  MATCH_MP_TAC (BETA_RULE abi_dyn_target_emit_inst)] >>
           simp[mk_inst_def]])) >>
  `(!T p m n. U T m /\ U T n ==> U T (if p then m else n)) /\
   (!T p m n. FrO T m /\ FrO T n ==> FrO T (if p then m else n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_if)) >>
  `!T opc m n p. U T m /\ U T n /\ U T p ==>
    U T (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_copy_case)) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss []
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume abi_dyn_decode_targets[word]:
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> simp[] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_targets[bytes]:
  dyn_certificate_tac
QED
Resume abi_dyn_decode_targets[array]:
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info`
  >- (ASM_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` mp_tac >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_targets[complex]:
  Cases_on `hi = Lit 0w` >>
  FULL_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_targets[cons]:
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_targets[loop]:
  qpat_x_assum `!is_dyn_elem dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >> dyn_certificate_tac
QED
Finalise abi_dyn_decode_targets

(* The concrete middle, as metalevel notation only. *)
val dyn_middle = ``\dst src lop base hi info asz msz i.
  do data <- emit_op ADD [src; Lit 32w];
     off <- emit_op MUL [i; Lit (n2w asz)];
     elem_src <- emit_op ADD [data; off];
     actual_src <- (if dec_info_needs_offset info then
       compile_abi_decode_dyn_elem_ptr lop base elem_src data hi asz
       else return elem_src);
     dst_data <- emit_op ADD [dst; Lit 32w];
     dst_off <- emit_op MUL [i; Lit (n2w msz)];
     elem_dst <- emit_op ADD [dst_data; dst_off];
     compile_abi_decode_to_buf elem_dst actual_src lop base hi info od``;

Theorem abi_dyn_middle_code[local]:
  !dst src lop base hi info asz msz i.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI /\ (lop <> DJMP ==> opc <> DJMP))
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [irule (CONJUNCT1 abi_dyn_decode_code),
    CHANGED_TAC (ASM_SIMP_TAC std_ss [code_action_emit_op,
      code_action_emit_void, code_action_return]),
    irule code_action_bind, irule code_action_ignore_bind,
    irule code_action_emit_op, irule code_action_emit_void,
    IF_CASES_TAC, gen_tac, conj_tac]) >> simp[]
QED

Theorem abi_dyn_middle_provenance[local]:
  !dst src lop base hi info asz msz i A.
    (^(inst [alpha |-> ``:unit``] dyn_prov)) A
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_provenance)),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_emit_op),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_emit_void),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_prov_return),
    ho_match_mp_tac (BETA_RULE abi_dyn_prov_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_prov_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac])
QED

Theorem abi_dyn_middle_targets[local]:
  !dst src lop base hi info asz msz i A.
    lop <> JMP /\ lop <> JNZ ==>
    (^(inst [alpha |-> ``:unit``] dyn_target)) A
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [(MATCH_MP_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_targets)) >> simp[]),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_target_return),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_target_emit_op) >> simp[]),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_target_emit_void) >> simp[mk_inst_def]),
    ho_match_mp_tac (BETA_RULE abi_dyn_target_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_target_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac]) >> simp[]
QED

Theorem abi_dyn_interval_excludes_old[local]:
  !lo hi suffix k. k < lo ==>
    fresh_label_output suffix k NOTIN (^dyn_I) lo hi
Proof
  simp[] >> rpt strip_tac >>
  drule emitHelperPropsTheory.fresh_label_output_inj >> simp[]
QED

Theorem abi_dyn_fresh_step_frame[local]:
  !N inst s t.
    EVERY (\x. ~var_below N x) inst.inst_outputs /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
    vars_kept N {} s t /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst 0 ARB inst s = OK t` by simp[step_inst_non_invoke] >>
  reverse conj_tac
  >- metis_tac[venomExecPropsTheory.step_inst_preserves_labels_always] >>
  simp[vars_kept_def] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[venomExecPropsTheory.step_terminator_preserves_vars] >>
  `~MEM x inst.inst_outputs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[step_preserves_non_output_vars]
QED

Theorem abi_dyn_middle_frame[local]:
  !dst src lop base hi info asz msz i sa sb N inst s t.
    ((^dyn_middle) dst src lop base hi info asz msz i) sa = ((),sb) /\
    N <= sa.cs_next_var /\ lop <> INVOKE /\ lop <> PHI /\
    MEM inst (frag_code sa sb) /\ step_inst_base inst s = OK t ==>
    vars_kept N {} s t /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE abi_dyn_body_middle_fresh) >> strip_tac >>
  drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >>
  strip_tac >> irule abi_dyn_fresh_step_frame >>
  qexists_tac `inst` >> gvs[EVERY_MEM] >> metis_tac[]
QED

(* Terminal layout: only a terminator/switch pair may close a block. *)
val dyn_T = ``\xs:instruction list. xs <> [] /\
  is_terminator (LAST xs).inst_opcode``;
val dyn_terminal_span = ``\a b. entry_shape a b /\
  EVERY (\bb. (^dyn_T) bb.bb_instructions) (emitted_blocks a b)``;
val dyn_terminal = ``\m. !a r b. m a = (r,b) ==> (^dyn_terminal_span) a b``;

Theorem abi_dyn_terminal_compose[local]:
  !a b c. (^dyn_terminal_span) a b /\ (^dyn_terminal_span) b c ==>
    (^dyn_terminal_span) a c
Proof
  simp_tac std_ss [] >> rpt gen_tac >> strip_tac >>
  `entry_shape a c` by metis_tac[entry_shape_trans] >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  drule_all abi_dyn_emitted_compose >> simp[EVERY_APPEND]
QED

Theorem abi_dyn_terminal_bind[local]:
  !m f. (^dyn_terminal) m /\
    (!x. (^(inst [alpha |-> beta] dyn_terminal)) (f x)) ==>
    (^(inst [alpha |-> beta] dyn_terminal)) (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  irule (BETA_RULE abi_dyn_terminal_compose) >> qexists_tac `r'` >> simp[]
QED

Theorem abi_dyn_terminal_ignore_bind[local]:
  !m n. (^dyn_terminal) m /\
    (^(inst [alpha |-> beta] dyn_terminal)) n ==>
    (^(inst [alpha |-> beta] dyn_terminal)) (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_terminal_bind) >> simp[]
QED

Theorem abi_dyn_terminal_return[local]:
  !v. (^dyn_terminal) (comp_return v)
Proof
  simp[comp_return_def, entry_shape_refl, emitted_blocks_def]
QED

Theorem abi_dyn_terminal_emit_op[local]:
  !opc ops. (^(inst [alpha |-> ``:operand``] dyn_terminal)) (emit_op opc ops)
Proof
  simp_tac std_ss [emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[entry_shape_def, emitted_blocks_def] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops
    [STRING #"%" (toString a.cs_next_var)]]` >> simp[]
QED

Theorem abi_dyn_terminal_emit_inst[local]:
  !opc ops outs. (^(inst [alpha |-> ``:unit``] dyn_terminal)) (emit_inst opc ops outs)
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[entry_shape_def, emitted_blocks_def] >>
  qexists_tac `[mk_inst a.cs_next_id opc ops outs]` >> simp[]
QED

Theorem abi_dyn_terminal_emit_void[local]:
  !opc ops. (^(inst [alpha |-> ``:unit``] dyn_terminal)) (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_emit_inst)
QED

Theorem abi_dyn_terminal_label[local]:
  !suffix. (^(inst [alpha |-> ``:string``] dyn_terminal)) (fresh_label suffix)
Proof
  simp[fresh_label_def, entry_shape_def, emitted_blocks_def]
QED

Theorem abi_dyn_terminal_alloc[local]:
  !size. (^(inst [alpha |-> ``:buffer``] dyn_terminal)) (compile_alloc_buffer size)
Proof
  gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_terminal_bind) >> conj_tac
  >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_emit_op) >>
  gen_tac >> BETA_TAC >> MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_return)
QED

Theorem abi_dyn_terminal_switch[local]:
  !opc ops outs l. is_terminator opc ==>
    (^(inst [alpha |-> ``:string``] dyn_terminal))
      (do emit_inst opc ops outs; new_block l od)
Proof
  simp_tac std_ss [emit_inst_def, comp_bind_def, comp_ignore_bind_def,
    fresh_id_def, emit_def, new_block_def] >>
  rpt strip_tac >> gvs[] >>
  simp[entry_shape_def, emitted_blocks_def, rich_listTheory.LAST_APPEND,
    mk_inst_def] >> disj2_tac >> qexistsl_tac [`[]`,
      `[mk_inst a.cs_next_id opc ops outs]`] >> simp[]
QED

Theorem abi_dyn_terminal_switch_cont[local]:
  !opc ops outs l n. is_terminator opc /\ (^dyn_terminal) n ==>
    (^dyn_terminal)
      (do emit_inst opc ops outs; new_block l; n od)
Proof
  rpt gen_tac >> strip_tac >>
  `do emit_inst opc ops outs; new_block l; n od =
   comp_ignore_bind (do emit_inst opc ops outs; new_block l od) n`
    by simp[comp_ignore_bind_def, comp_bind_assoc] >>
  pop_assum SUBST1_TAC >> BETA_TAC >> rule_assum_tac BETA_RULE >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_terminal_ignore_bind) >> simp[] >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_terminal_switch) >> simp[]
QED

Theorem abi_dyn_terminal_if[local]:
  !p m n. (^dyn_terminal) m /\ (^dyn_terminal) n ==>
    (^dyn_terminal) (if p then m else n)
Proof
  Cases_on `p` >> simp[]
QED

Theorem abi_dyn_terminal_copy_case[local]:
  !opc m n p. (^dyn_terminal) m /\ (^dyn_terminal) n /\ (^dyn_terminal) p ==>
    (^dyn_terminal) (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `opc` >> pure_rewrite_tac[opcode_case_def] >> metis_tac[]
QED

Theorem abi_dyn_decode_terminal[local]:
  (!dst src lop base hi info.
    (^(inst [alpha |-> ``:unit``] dyn_terminal))
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    (^(inst [alpha |-> ``:unit``] dyn_terminal))
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    (^(inst [alpha |-> ``:unit``] dyn_terminal))
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^(inst [alpha |-> ``:unit``] dyn_terminal)` >>
  qabbrev_tac `FrO = ^(inst [alpha |-> ``:operand``] dyn_terminal)` >>
  qabbrev_tac `B = ^(inst [alpha |-> ``:buffer``] dyn_terminal)` >>
  qabbrev_tac `L = ^(inst [alpha |-> ``:string``] dyn_terminal)` >>
  `(!m f. FrO m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. FrO (f x)) ==> FrO (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. B (f x)) ==> B (comp_bind m f)) /\
   (!m f. B m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. L m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. U m /\ (!x. U (f x)) ==> U (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_bind)) >>
  `(!m n. U m /\ U n ==> U (comp_ignore_bind m n)) /\
   (!m n. U m /\ FrO n ==> FrO (comp_ignore_bind m n)) /\
   (!m n. L m /\ U n ==> U (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_ignore_bind)) >>
  `(!opc ops. FrO (emit_op opc ops)) /\
   (!opc ops. U (emit_void opc ops)) /\
   (!l. L (fresh_label l)) /\ (!sz. B (compile_alloc_buffer sz)) /\
   (!v. U (comp_return v)) /\ (!v. FrO (comp_return v)) /\
   (!v. B (comp_return v)) /\ (!v. L (comp_return v))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_terminal_emit_op, abi_dyn_terminal_emit_void,
           abi_dyn_terminal_label, abi_dyn_terminal_alloc, abi_dyn_terminal_return])) >>
  `(!p m n. U m /\ U n ==> U (if p then m else n)) /\
   (!p m n. FrO m /\ FrO n ==> FrO (if p then m else n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_if)) >>
  `!opc m n p. U m /\ U n /\ U p ==>
    U (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_copy_case)) >>
  `(!ops outs l n. U n ==>
      U (do emit_inst JMP ops outs; new_block l; n od)) /\
   (!ops outs l n. U n ==>
      U (do emit_inst JNZ ops outs; new_block l; n od))`
    by (conj_tac >> rpt gen_tac >> strip_tac >>
        simp_tac std_ss [Abbr `U`] >>
        BETA_TAC >> rule_assum_tac BETA_RULE >>
        MATCH_MP_TAC (BETA_RULE abi_dyn_terminal_switch_cont) >> simp[is_terminator_def]) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def,
    compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, compile_abi_decode_range_check_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  ASM_SIMP_TAC std_ss []
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume abi_dyn_decode_terminal[word]:
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> simp[] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_terminal[bytes]:
  dyn_certificate_tac
QED
Resume abi_dyn_decode_terminal[array]:
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info`
  >- (ASM_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` mp_tac >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_terminal[complex]:
  Cases_on `hi = Lit 0w` >>
  FULL_SIMP_TAC std_ss [LET_THM] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_terminal[cons]:
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [LET_THM] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_terminal[loop]:
  qpat_x_assum `!is_dyn_elem dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >> dyn_certificate_tac
QED
Finalise abi_dyn_decode_terminal

Theorem abi_dyn_middle_terminal[local]:
  !dst src lop base hi info asz msz i.
    (^(inst [alpha |-> ``:unit``] dyn_terminal))
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_terminal)),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_return),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_emit_op),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_terminal_emit_void),
    ho_match_mp_tac (BETA_RULE abi_dyn_terminal_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_terminal_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac])
QED

(* Uniqueness concerns the new block span, never the incoming blocks. *)
val dyn_Old = ``\a. ?suffix k. a.cs_current_bb = fresh_label_output suffix k /\
  k < a.cs_next_label``;
val dyn_unique_span = ``\a b. ALL_DISTINCT
  (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b))``;

Theorem abi_dyn_span_old_labels[local]:
  !a b. (^dyn_span) {} a b /\ (^dyn_Old) a ==>
    !l. l IN (^dyn_B) a b ==>
      ?suffix k. l = fresh_label_output suffix k /\ k < b.cs_next_label
Proof
  simp_tac std_ss [] >> rpt gen_tac >> strip_tac >>
  fs[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  qpat_x_assum `!x. _` (qspec_then `l` mp_tac) >>
  impl_tac >- metis_tac[] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem abi_dyn_span_old[local]:
  !a b. (^dyn_span) {} a b /\ (^dyn_Old) a ==> (^dyn_Old) b
Proof
  rpt gen_tac >> strip_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
  qspecl_then [`a`, `b`] mp_tac (BETA_RULE abi_dyn_span_old_labels) >>
  simp[] >> disch_then (qspec_then `b.cs_current_bb` mp_tac) >> simp[]
QED

Theorem abi_dyn_unique_compose[local]:
  !a b c. (^dyn_span) {} a b /\ (^dyn_span) {} b c /\
    (^dyn_Old) a /\ (^dyn_unique_span) a b /\ (^dyn_unique_span) b c ==>
    (^dyn_unique_span) a c
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[entry_shape_extends] >>
  drule_all abi_dyn_emitted_compose >> strip_tac >>
  `!l. l IN (^dyn_B) a b ==>
     ?suffix k. l = fresh_label_output suffix k /\ k < b.cs_next_label`
    by (BETA_TAC >> MATCH_MP_TAC (BETA_RULE abi_dyn_span_old_labels) >> simp[]) >>
  `!l. MEM l (MAP (\bb. bb.bb_label) (emitted_blocks a b)) ==>
       l NOTIN (^dyn_B) b c`
    by (rpt strip_tac >>
        `l IN (^dyn_B) a b` by (simp[] >> gvs[MEM_MAP] >> metis_tac[]) >>
        first_x_assum drule >> strip_tac >>
        `l NOTIN (^dyn_I) b.cs_next_label c.cs_next_label`
          by (BETA_TAC >> metis_tac[BETA_RULE abi_dyn_interval_excludes_old]) >>
        gvs[ALL_DISTINCT, pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  simp_tac std_ss [] >> simp[MAP_APPEND, ALL_DISTINCT_APPEND, ALL_DISTINCT] >>
  gvs[ALL_DISTINCT] >> conj_tac
  >- (gvs[MEM_MAP] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> gvs[MEM_MAP] >> metis_tac[]
QED

val dyn_unique = ``\m. !a r b. (^dyn_Old) a /\ m a = (r,b) ==>
  (^dyn_span) {} a b /\ (^dyn_Old) b /\ (^dyn_unique_span) a b``;

Theorem abi_dyn_unique_bind[local]:
  !m f. (^dyn_unique) m /\ (!x. (^(inst [alpha |-> beta] dyn_unique)) (f x)) ==>
    (^(inst [alpha |-> beta] dyn_unique)) (comp_bind m f)
Proof
  simp_tac std_ss [comp_bind_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `m a` >> gvs[] >>
  qpat_x_assum `!a r b. _` (qspecl_then [`a`, `q`, `r'`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qpat_x_assum `!x a r b. _` (qspecl_then [`q`, `r'`, `r`, `b`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  conj_tac
  >- (qspecl_then [`{}`, `a`, `r'`, `b`] mp_tac
        (BETA_RULE abi_dyn_span_compose) >> gvs[]) >>
  conj_tac >- metis_tac[] >>
  qspecl_then [`a`, `r'`, `b`] mp_tac (BETA_RULE abi_dyn_unique_compose) >>
  gvs[ALL_DISTINCT] >> metis_tac[]
QED

Theorem abi_dyn_unique_ignore_bind[local]:
  !m n. (^dyn_unique) m /\ (^(inst [alpha |-> beta] dyn_unique)) n ==>
    (^(inst [alpha |-> beta] dyn_unique)) (comp_ignore_bind m n)
Proof
  simp_tac std_ss [comp_ignore_bind_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac (BETA_RULE abi_dyn_unique_bind) >> gvs[] >> metis_tac[]
QED

Theorem abi_dyn_unique_return[local]:
  !v. (^dyn_unique) (comp_return v)
Proof
  simp[comp_return_def, entry_shape_refl, emitted_blocks_def]
QED

Theorem abi_dyn_unique_emit_op[local]:
  !opc ops. (^(inst [alpha |-> ``:operand``] dyn_unique)) (emit_op opc ops)
Proof
  rpt gen_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `(^dyn_span) {} a b`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_prov_emit_op) >> metis_tac[]) >>
  `(^dyn_Old) b` by (BETA_TAC >> rule_assum_tac BETA_RULE >>
    metis_tac[BETA_RULE abi_dyn_span_old]) >> simp[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, emitted_blocks_def] >> metis_tac[]
QED

Theorem abi_dyn_unique_emit_inst[local]:
  !opc ops outs. (^(inst [alpha |-> ``:unit``] dyn_unique)) (emit_inst opc ops outs)
Proof
  rpt gen_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `(^dyn_span) {} a b`
    by (BETA_TAC >> irule (BETA_RULE abi_dyn_prov_emit_inst) >> metis_tac[]) >>
  `(^dyn_Old) b` by (BETA_TAC >> rule_assum_tac BETA_RULE >>
    metis_tac[BETA_RULE abi_dyn_span_old]) >> simp[] >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, emitted_blocks_def] >> metis_tac[]
QED

Theorem abi_dyn_unique_emit_void[local]:
  !opc ops. (^(inst [alpha |-> ``:unit``] dyn_unique)) (emit_void opc ops)
Proof
  simp_tac std_ss [emit_void_def, GSYM emit_inst_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_inst)
QED

Theorem abi_dyn_unique_label[local]:
  !suffix. (^(inst [alpha |-> ``:string``] dyn_unique)) (fresh_label suffix)
Proof
  simp[fresh_label_def, entry_shape_def, emitted_blocks_def] >>
  rpt strip_tac >> `k < a.cs_next_label + 1` by simp[] >> metis_tac[]
QED

Theorem abi_dyn_unique_alloc[local]:
  !sz. (^(inst [alpha |-> ``:buffer``] dyn_unique)) (compile_alloc_buffer sz)
Proof
  gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  MATCH_MP_TAC (BETA_RULE abi_dyn_unique_bind) >> conj_tac
  >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_op) >>
  gen_tac >> BETA_TAC >> MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_return)
QED

(* A reserved label is not a target of a later fresh span. *)
Theorem abi_dyn_unique_reserved_exclusion[local]:
  !a b l suffix k.
    (^dyn_span) {} a b /\ l = fresh_label_output suffix k /\
    k < a.cs_next_label /\ l <> a.cs_current_bb ==>
    l NOTIN (^dyn_B) a b
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >> BETA_TAC >>
  `l NOTIN (^dyn_I) a.cs_next_label b.cs_next_label`
    by (BETA_TAC >> metis_tac[BETA_RULE abi_dyn_interval_excludes_old]) >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED


(* Extract a loop layout through explicit prefixes, without exposing TAKE. *)
Theorem abi_dyn_unique_layout[local]:
  !a s4 s5 b xs bh be bt.
    s4.cs_blocks = bh :: be :: a.cs_blocks /\
    s5.cs_blocks = xs ++ s4.cs_blocks /\
    b.cs_blocks = bt :: s5.cs_blocks ==>
    emitted_blocks a b = bt :: (xs ++ [bh;be]) /\
    emitted_blocks s4 s5 = xs
Proof
  rpt gen_tac >> strip_tac >> conj_tac >>
  irule emitted_blocks_append >> simp[APPEND_ASSOC]
QED

Theorem abi_dyn_unique_skeleton[local]:
  !lh lb le p h q a b.
    (^dyn_Old) a /\ ALL_DISTINCT [a.cs_current_bb;lh;lb;le] /\
    (!l. MEM l [lh;lb;le] ==>
      ?suffix k. l = fresh_label_output suffix k /\ k < a.cs_next_label) /\
    (!s t. p s = ((),t) ==> t.cs_blocks = s.cs_blocks /\
      t.cs_current_bb = s.cs_current_bb /\ t.cs_next_label = s.cs_next_label) /\
    (!s t. h s = ((),t) ==> t.cs_blocks = s.cs_blocks /\
      t.cs_current_bb = s.cs_current_bb /\ t.cs_next_label = s.cs_next_label) /\
    (^(inst [alpha |-> ``:unit``] dyn_unique)) q /\ (^dyn_skel) lh lb le p h q a = ((),b) ==>
    (^dyn_unique_span) a b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(^dyn_skel) _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rename1 `q s4 = ((),s5)` >>
  rpt (qpat_x_assum `!s t. _` (drule_then strip_assume_tac)) >>
  imp_res_tac (cj 2 emitHelperPropsTheory.new_block_props) >>
  imp_res_tac (cj 7 emitHelperPropsTheory.new_block_props) >>
  `(^dyn_Old) s4` by (BETA_TAC >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `!a b. _ /\ q a = _ ==> _` (qspecl_then [`s4`,`s5`] mp_tac) >>
  (impl_tac >- (rule_assum_tac BETA_RULE >> simp[])) >> strip_tac >>
  `!l. MEM l [a.cs_current_bb;lh;le] ==> l NOTIN (^dyn_B) s4 s5`
    by (gen_tac >> disch_tac >> BETA_TAC >>
        gvs[] >> metis_tac[SRULE [] (BETA_RULE abi_dyn_unique_reserved_exclusion)]) >>
  imp_res_tac (cj 4 emitHelperPropsTheory.new_block_props) >>
  `?xs. s5.cs_blocks = xs ++ s4.cs_blocks`
    by (qpat_x_assum `entry_shape s4 s5` mp_tac >>
        simp[entry_shape_def] >> strip_tac
        >- (qexists_tac `[]` >> simp[]) >>
        qexists_tac `front ++ [<|bb_label := s4.cs_current_bb;
          bb_instructions := s4.cs_current_insts ++ tail|>]` >>
        simp[APPEND_ASSOC]) >>
  `emitted_blocks a b =
    <|bb_label := s5.cs_current_bb; bb_instructions := s5.cs_current_insts|> ::
      (xs ++ [<|bb_label := lh; bb_instructions := cs'³'.cs_current_insts|>;
              <|bb_label := a.cs_current_bb; bb_instructions := cs'.cs_current_insts|>]) /\
   emitted_blocks s4 s5 = xs`
    by (irule abi_dyn_unique_layout >> simp[]) >>
  gvs[MAP_APPEND, ALL_DISTINCT_APPEND, ALL_DISTINCT] >>
  qpat_x_assum `!l. _ ==> ( (!bb. _) /\ _)` mp_tac >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem abi_dyn_unique_entry_blocks[local]:
  !a a' b. a.cs_blocks = a'.cs_blocks ==>
    ((^dyn_unique_span) a b <=> (^dyn_unique_span) a' b)
Proof
  simp[emitted_blocks_def]
QED

Theorem abi_dyn_unique_loop[local]:
  !dst src lop base hi info asz msz ip cnt.
    (!d s. (^(inst [alpha |-> ``:unit``] dyn_unique))
      (compile_abi_decode_to_buf d s lop base hi info)) ==>
    (^(inst [alpha |-> ``:unit``] dyn_unique))
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt)
Proof
  rpt gen_tac >> strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `(^dyn_span) {} a b`
    by (BETA_TAC >> irule (BETA_RULE (cj 3 abi_dyn_decode_provenance)) >>
        metis_tac[]) >>
  `(^dyn_Old) b` by (BETA_TAC >> rule_assum_tac BETA_RULE >>
    metis_tac[BETA_RULE abi_dyn_span_old]) >>
  conj_tac >- (rule_assum_tac BETA_RULE >> simp[]) >>
  conj_tac >- (rule_assum_tac BETA_RULE >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_abi_decode_dyn_loop _ _ _ _ _ _ _ _ _ _ a = _` mp_tac >>
  pure_rewrite_tac [abi_dyn_loop_skeleton] >>
  simp_tac std_ss [fresh_label_def, comp_bind_def, LET_THM] >> strip_tac >>
  Cases_on `r` >> fs[] >>
  `(^dyn_unique_span) (a with cs_next_label := a.cs_next_label + 3) b`
    suffices_by (mp_tac (Q.SPECL [`a`, `a with cs_next_label := a.cs_next_label + 3`, `b`]
      (BETA_RULE abi_dyn_unique_entry_blocks)) >> simp_tac std_ss [] >> simp[]) >>
  BETA_TAC >> irule (BETA_RULE abi_dyn_unique_skeleton) >>
  (conj_tac >- (simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
    DECIDE ``n <= n + 3``])) >>
  goal_assum (drule_at Any) >>
  conj_tac
  >- (simp_tac std_ss [compile_abi_dec_addr_def] >>
      Cases_on `base' = Lit 0w` >>
      simp[emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac >- suspend "body" >>
  simp[ALL_DISTINCT] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[DECIDE ``n < n + 3 /\ n + 1 < n + 3 /\ n + 2 < n + 3``]) >>
  rpt conj_tac >> strip_tac >>
  drule emitHelperPropsTheory.fresh_label_output_inj >> simp[]
QED
Resume abi_dyn_unique_loop[body]:
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def] >>
  rpt (FIRST [CHANGED_TAC BETA_TAC,
    first_assum (MATCH_ACCEPT_TAC o BETA_RULE),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_return),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_op),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_inst),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_void),
    MATCH_MP_TAC (BETA_RULE abi_dyn_unique_bind),
    MATCH_MP_TAC (BETA_RULE abi_dyn_unique_ignore_bind),
    conj_tac, gen_tac, IF_CASES_TAC]) >>
  Cases_on `r` >> simp[ALL_DISTINCT] >> metis_tac[]
QED
Finalise abi_dyn_unique_loop

Theorem abi_dyn_unique_if[local]:
  !p m n. (^dyn_unique) m /\ (^dyn_unique) n ==>
    (^dyn_unique) (if p then m else n)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `p` >> simp[]
QED

Theorem abi_dyn_unique_copy_case[local]:
  !opc m n p. (^dyn_unique) m /\ (^dyn_unique) n /\ (^dyn_unique) p ==>
    (^dyn_unique) (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `P m` >>
  Cases_on `opc` >> pure_rewrite_tac[opcode_case_def] >> metis_tac[]
QED

Theorem abi_dyn_decode_unique[local]:
  (!dst src lop base hi info.
    (^(inst [alpha |-> ``:unit``] dyn_unique))
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    (^(inst [alpha |-> ``:unit``] dyn_unique))
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    (^(inst [alpha |-> ``:unit``] dyn_unique))
      (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt))
Proof
  qabbrev_tac `U = ^(inst [alpha |-> ``:unit``] dyn_unique)` >>
  qabbrev_tac `FrO = ^(inst [alpha |-> ``:operand``] dyn_unique)` >>
  qabbrev_tac `B = ^(inst [alpha |-> ``:buffer``] dyn_unique)` >>
  qabbrev_tac `L = ^(inst [alpha |-> ``:string``] dyn_unique)` >>
  `(!m f. FrO m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. FrO (f x)) ==> FrO (comp_bind m f)) /\
   (!m f. FrO m /\ (!x. B (f x)) ==> B (comp_bind m f)) /\
   (!m f. B m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. L m /\ (!x. U (f x)) ==> U (comp_bind m f)) /\
   (!m f. U m /\ (!x. U (f x)) ==> U (comp_bind m f))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_bind)) >>
  `(!m n. U m /\ U n ==> U (comp_ignore_bind m n)) /\
   (!m n. U m /\ FrO n ==> FrO (comp_ignore_bind m n)) /\
   (!m n. L m /\ U n ==> U (comp_ignore_bind m n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `L`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_ignore_bind)) >>
  `(!opc ops. FrO (emit_op opc ops)) /\
   (!opc ops. U (emit_void opc ops)) /\
   (!l. L (fresh_label l)) /\ (!sz. B (compile_alloc_buffer sz)) /\
   (!v. U (comp_return v)) /\ (!v. FrO (comp_return v)) /\
   (!v. B (comp_return v)) /\ (!v. L (comp_return v))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`, Abbr `B`, Abbr `L`] >>
        FIRST (map (MATCH_ACCEPT_TAC o BETA_RULE)
          [abi_dyn_unique_emit_op, abi_dyn_unique_emit_void,
           abi_dyn_unique_label, abi_dyn_unique_alloc, abi_dyn_unique_return])) >>
  `(!p m n. U m /\ U n ==> U (if p then m else n)) /\
   (!p m n. FrO m /\ FrO n ==> FrO (if p then m else n))`
    by (rpt conj_tac >> simp_tac std_ss [Abbr `U`, Abbr `FrO`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_if)) >>
  `!opc m n p. U m /\ U n /\ U p ==>
    U (case opc of CALLDATALOAD => m | DLOAD => n | _ => p)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_copy_case)) >>
  `!dst src lop base hi info asz msz ip cnt.
    (!d s. U (compile_abi_decode_to_buf d s lop base hi info)) ==>
    U (compile_abi_decode_dyn_loop dst src lop base hi info asz msz ip cnt)`
    by (simp_tac std_ss [Abbr `U`] >>
        MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_loop)) >>
  qpat_x_assum `Abbrev (U = _)` kall_tac >>
  qpat_x_assum `Abbrev (FrO = _)` kall_tac >>
  qpat_x_assum `Abbrev (B = _)` kall_tac >>
  qpat_x_assum `Abbrev (L = _)` kall_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED
Resume abi_dyn_decode_unique[word]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_static_def] >>
  Cases_on `clamp_info` >>
  simp_tac std_ss [compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >> simp[] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[bytes]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[array]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def,
    compile_abi_decode_range_check_def, compile_abi_decode_static_def,
    compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info`
  >- (ASM_SIMP_TAC std_ss [LET_THM, compile_abi_dec_addr_def] >> dyn_certificate_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` mp_tac >>
  ASM_SIMP_TAC std_ss [LET_THM, compile_abi_dec_addr_def] >> disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[complex]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def] >>
  Cases_on `hi = Lit 0w` >>
  FULL_SIMP_TAC std_ss [LET_THM, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[nil]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def] >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[cons]:
  simp_tac std_ss [Once compile_abi_decode_to_buf_def] >>
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [LET_THM, compile_abi_dec_addr_def,
    compile_abi_decode_static_def, compile_getelemptr_abi_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_decode_range_check_def] >>
  disch_tac >> dyn_certificate_tac
QED
Resume abi_dyn_decode_unique[loop]:
  qpat_x_assum `!is_dyn_elem dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  ASM_SIMP_TAC std_ss [] >> disch_tac >> dyn_certificate_tac
QED
Finalise abi_dyn_decode_unique

Theorem abi_dyn_middle_unique[local]:
  !dst src lop base hi info asz msz i.
    (^(inst [alpha |-> ``:unit``] dyn_unique))
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_unique)),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_return),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_op),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_unique_emit_void),
    ho_match_mp_tac (BETA_RULE abi_dyn_unique_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_unique_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac])
QED

Theorem abi_dyn_middle_final_exclusion[local]:
  !dst src lop base hi info asz msz i sa sb.
    (^dyn_Old) sa /\
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) ==>
    !bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE abi_dyn_middle_unique) >>
  simp[ALL_DISTINCT, MEM_MAP] >> metis_tac[]
QED

(* Bounded emitted-code region.  Upper bounds rule out spurious off-cut
   states past the last instruction of either sort of block. *)
val dyn_R = ``\sa sb s.
  (s.vs_current_bb = sa.cs_current_bb ==>
     LENGTH sa.cs_current_insts <= s.vs_inst_idx) /\
  ((s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx <= LENGTH sb.cs_current_insts) \/
   (?bb. MEM bb (emitted_blocks sa sb) /\
     bb.bb_label = s.vs_current_bb /\
     s.vs_inst_idx < LENGTH bb.bb_instructions))``;

Theorem abi_dyn_lookup_filter[local]:
  !blocks lbl bb keep.
    lookup_block lbl blocks = SOME bb /\ keep bb ==>
    lookup_block lbl (FILTER keep blocks) = SOME bb
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  Cases_on `keep h` >> gvs[FIND_thm, lookup_block_def]
QED

Theorem abi_dyn_observer_has_code[local]:
  !sa sb fn id. fn_has_code sa sb fn /\
    (!bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb) ==>
    fn_has_code sa sb (frag_observer sa sb fn id)
Proof
  rpt gen_tac >> strip_tac >> rw[fn_has_code_def]
  >- (rename1 `MEM emitted (emitted_blocks sa sb)` >>
      `emitted.bb_label <> sb.cs_current_bb` by metis_tac[] >>
      simp[frag_observer_def, lookup_block_def, FIND_thm] >>
      rewrite_tac[GSYM lookup_block_def] >>
      irule abi_dyn_lookup_filter >> gvs[fn_has_code_def]) >>
  qexists_tac `<|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` >>
  simp[frag_observer_cut_lookup, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem abi_dyn_region_lookup[local]:
  !sa sb fn s. fn_has_code sa sb fn /\ (^dyn_R) sa sb s /\
    ~at_point sb s ==>
    ?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rpt gen_tac >> simp_tac std_ss [fn_has_code_def, at_point_def] >>
  strip_tac
  >- (qexistsl_tac [`bb`, `EL s.vs_inst_idx sb.cs_current_insts`] >>
      gvs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  rename1 `MEM emitted (emitted_blocks sa sb)` >>
  qexistsl_tac [`emitted`, `EL s.vs_inst_idx emitted.bb_instructions`] >>
  gvs[get_instruction_def] >> metis_tac[]
QED

Theorem abi_dyn_region_agreement[local]:
  !sa sb fn obs s. fn_has_code sa sb fn /\ fn_has_code sa sb obs /\
    (^dyn_R) sa sb s /\ ~at_point sb s ==>
    ?bb ob inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block s.vs_current_bb obs.fn_blocks = SOME ob /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction ob s.vs_inst_idx = SOME inst
Proof
  rpt gen_tac >> simp_tac std_ss [fn_has_code_def, at_point_def] >>
  strip_tac
  >- (qexistsl_tac [`bb`, `bb'`, `EL s.vs_inst_idx sb.cs_current_insts`] >>
      gvs[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  rename1 `MEM emitted (emitted_blocks sa sb)` >>
  qexistsl_tac [`emitted`, `emitted`, `EL s.vs_inst_idx emitted.bb_instructions`] >>
  gvs[get_instruction_def] >> metis_tac[]
QED

Theorem abi_dyn_region_code[local]:
  !sa sb fn s bb inst. cs_extends sa sb /\ fn_has_code sa sb fn /\
    (^dyn_R) sa sb s /\ ~at_point sb s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==>
    MEM inst (frag_code sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  `!block n. get_instruction block s.vs_inst_idx = SOME inst /\
       n <= s.vs_inst_idx ==> MEM inst (DROP n block.bb_instructions)` by
    (simp[get_instruction_def] >> rpt strip_tac >> gvs[] >>
     simp[MEM_EL] >> qexists_tac `s.vs_inst_idx - n` >> simp[EL_DROP]) >>
  qpat_x_assum `(^dyn_R) sa sb s` mp_tac >>
  simp_tac std_ss [] >> strip_tac
  >- (`s.vs_inst_idx < LENGTH sb.cs_current_insts` by gvs[at_point_def] >>
      `inst = EL s.vs_inst_idx sb.cs_current_insts` by
        gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND,
            get_instruction_def, EL_APPEND_EQN] >>
      Cases_on `emitted_blocks sa sb = []`
      >- (drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
          `LENGTH sa.cs_current_insts <= s.vs_inst_idx` by metis_tac[] >>
          simp[frag_code_def, emitted_insts_def] >>
          simp[MEM_EL] >> qexists_tac `s.vs_inst_idx - LENGTH sa.cs_current_insts` >>
          simp[EL_DROP]) >>
      simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj2_tac >> simp[MEM_EL] >> metis_tac[]) >>
  rename1 `MEM emitted (emitted_blocks sa sb)` >>
  `bb = emitted` by (gvs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >> gvs[] >>
  `emitted_blocks sa sb <> []` by (strip_tac >> gvs[]) >>
  Cases_on `bb = LAST (emitted_blocks sa sb)`
  >- (drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
      simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj1_tac >>
      first_x_assum irule >> gvs[]) >>
  `MEM bb (FRONT (emitted_blocks sa sb))` by
    metis_tac[listTheory.APPEND_FRONT_LAST, MEM_APPEND, MEM] >>
  simp[frag_code_def, NULL_EQ, MEM_APPEND] >> disj1_tac >> disj2_tac >>
  `MEM inst bb.bb_instructions` by metis_tac[DROP_0, arithmeticTheory.ZERO_LESS_EQ] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem abi_dyn_region_step[local]:
  !sa sb fn s bb inst t.
    fn_has_code sa sb fn /\ (^dyn_R) sa sb s /\ ~at_point sb s /\
    EVERY (\b. (^dyn_T) b.bb_instructions) (emitted_blocks sa sb) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t ==>
    (^dyn_R) sa sb (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  qpat_x_assum `(^dyn_R) sa sb s` mp_tac >>
  simp_tac std_ss [] >> strip_tac
  >- (simp_tac std_ss [venom_state_component_equality, venom_state_accfupds,
        venom_state_accessors] >> conj_tac >- (strip_tac >> gvs[] >> decide_tac) >>
      disj1_tac >> gvs[at_point_def]) >>
  rename1 `MEM emitted (emitted_blocks sa sb)` >>
  `bb = emitted` by (gvs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >>
  gvs[] >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[get_instruction_def] >>
     `s.vs_inst_idx <> LENGTH bb.bb_instructions - 1` by
       (strip_tac >> gvs[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]) >> decide_tac) >>
  simp_tac std_ss [venom_state_accfupds, venom_state_accessors] >>
  conj_tac >- (strip_tac >> gvs[] >> decide_tac) >>
  disj2_tac >> qexists_tac `bb` >> simp[]
QED

Theorem abi_dyn_literal_jump_target[local]:
  !T inst s t. (^dyn_J) T inst /\
    MEM inst.inst_opcode [JMP; JNZ] /\ step_inst_base inst s = OK t ==>
    t.vs_current_bb IN T
Proof
  rpt gen_tac >> simp_tac std_ss [] >> strip_tac >>
  gvs[] >> gvs[step_inst_base_opcode_eqs,
    AllCaseEqs(), jump_to_def] >> metis_tac[]
QED

Theorem abi_dyn_middle_off_cut[local]:
  !dst src lop base hi info asz msz i sa sb fn id s.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    lop <> INVOKE /\ lop <> PHI /\ (^dyn_Old) sa /\
    fn_has_code sa sb fn /\ (^dyn_R) sa sb s /\ ~at_point sb s ==>
    ?bb ob inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME ob /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction ob s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> INVOKE
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  qpat_x_assum `?suffix k. _` strip_assume_tac >>
  `fn_has_code sa sb (frag_observer sa sb fn id)` by
    (irule abi_dyn_observer_has_code >> simp[] >>
     metis_tac[BETA_RULE abi_dyn_middle_final_exclusion]) >>
  drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >>
  strip_tac >>
  `?bb ob inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME ob /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction ob s.vs_inst_idx = SOME inst` by
    metis_tac[BETA_RULE abi_dyn_region_agreement] >>
  `MEM inst (frag_code sa sb)` by
    metis_tac[BETA_RULE abi_dyn_region_code, entry_shape_extends] >>
  qexistsl_tac [`bb`, `ob`, `inst`] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_dyn_middle_closed[local]:
  !dst src lop base hi info asz msz i T.
    lop <> JMP /\ lop <> JNZ ==>
    (^(inst [alpha |-> ``:unit``] dyn_closed)) T
      ((^dyn_middle) dst src lop base hi info asz msz i)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [(MATCH_MP_TAC (BETA_RULE (CONJUNCT1 abi_dyn_decode_closed)) >> simp[]),
    MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op) >> simp[]),
    (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_void) >> simp[mk_inst_def]),
    ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind),
    ho_match_mp_tac (BETA_RULE abi_dyn_closed_ignore_bind),
    IF_CASES_TAC, gen_tac, conj_tac]) >> simp[]
QED

Theorem abi_dyn_middle_jump_target[local]:
  !dst src lop base hi info asz msz i sa sb inst s t.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    lop <> JMP /\ lop <> JNZ /\ (^dyn_Old) sa /\
    MEM inst (frag_code sa sb) /\ MEM inst.inst_opcode [JMP; JNZ] /\
    step_inst_base inst s = OK t ==>
    t.vs_current_bb IN (^dyn_B) sa sb /\
    t.vs_current_bb <> sa.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  `EVERY ((^dyn_J) ((^dyn_B) sa sb)) (frag_code sa sb)` by
    (drule_all (BETA_RULE abi_dyn_middle_closed) >>
     disch_then (qspec_then `{}` mp_tac) >> simp[]) >>
  `EVERY ((^dyn_J) ((^dyn_I) sa.cs_next_label sb.cs_next_label))
     (frag_code sa sb)` by
    (drule_all (BETA_RULE abi_dyn_middle_targets) >>
     disch_then (qspec_then `{}` mp_tac) >> simp[]) >>
  `t.vs_current_bb IN (^dyn_B) sa sb /\
   t.vs_current_bb IN (^dyn_I) sa.cs_next_label sb.cs_next_label` by
    (conj_tac >> irule abi_dyn_literal_jump_target >>
     qexistsl_tac [`inst`, `s`] >>
     asm_simp_tac std_ss [] >>
     rule_assum_tac (BETA_RULE o REWRITE_RULE [EVERY_MEM]) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `?suffix k. _` strip_assume_tac >>
  metis_tac[BETA_RULE abi_dyn_interval_excludes_old]
QED

Theorem abi_dyn_middle_terminator_target[local]:
  !dst src lop base hi info asz msz i sa sb inst s t.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    ~is_terminator lop /\ lop <> INVOKE /\ lop <> PHI /\ (^dyn_Old) sa /\
    MEM inst (frag_code sa sb) /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t ==>
    t.vs_current_bb IN (^dyn_B) sa sb /\
    t.vs_current_bb <> sa.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  `lop <> DJMP /\ lop <> JMP /\ lop <> JNZ` by metis_tac[is_terminator_def] >>
  drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >>
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DJMP` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ARB inst s = OK t` by simp[step_inst_non_invoke] >>
  `MEM inst.inst_opcode [JMP; JNZ]` by
    metis_tac[fnBlockBodyHelpersTheory.step_ok_terminator_jump, MEM] >>
  metis_tac[BETA_RULE abi_dyn_middle_jump_target]
QED

Theorem abi_dyn_region_jump[local]:
  !sa sb fn t. fn_has_code sa sb fn /\
    EVERY (\b. (^dyn_T) b.bb_instructions) (emitted_blocks sa sb) /\
    t.vs_current_bb IN (^dyn_B) sa sb /\
    t.vs_current_bb <> sa.cs_current_bb ==>
    (?tb. lookup_block t.vs_current_bb fn.fn_blocks = SOME tb) /\
    (^dyn_R) sa sb (t with vs_inst_idx := 0)
Proof
  rpt gen_tac >> simp_tac std_ss [] >> strip_tac >>
  `?tb. lookup_block t.vs_current_bb fn.fn_blocks = SOME tb` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  simp_tac std_ss [venom_state_accfupds, venom_state_accessors] >>
  conj_tac >- simp[] >>
  gvs[EVERY_MEM] >> metis_tac[listTheory.LENGTH_NIL, arithmeticTheory.NOT_ZERO_LT_ZERO]
QED

Theorem abi_dyn_region_target_phi[local]:
  !sa sb fn id lbl.
    fn_has_code sa sb fn /\ no_phi_fn fn /\
    (lbl = sb.cs_current_bb ==>
      EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts) /\
    lbl IN (^dyn_B) sa sb ==>
    ?tb tob. lookup_block lbl fn.fn_blocks = SOME tb /\
      lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME tob /\
      phi_prefix_length tb.bb_instructions = 0 /\
      phi_prefix_length tob.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  `?tb. lookup_block lbl fn.fn_blocks = SOME tb` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `phi_prefix_length tb.bb_instructions = 0` by
    (drule venomExecProofsTheory.lookup_block_MEM >>
     gvs[no_phi_fn_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `lbl = sb.cs_current_bb`
  >- (gvs[] >>
      qexists_tac `<|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` >>
      simp[frag_observer_cut_lookup] >>
      Cases_on `sb.cs_current_insts` >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  `lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME tb` by
    (simp[frag_observer_def, lookup_block_def, FIND_thm] >>
     rewrite_tac[GSYM lookup_block_def] >> irule abi_dyn_lookup_filter >>
     simp[] >> gvs[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]) >>
  metis_tac[]
QED

Theorem abi_dyn_middle_jump[local]:
  !dst src lop base hi info asz msz i sa sb fn id s inst t.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    ~is_terminator lop /\ lop <> INVOKE /\ lop <> PHI /\ (^dyn_Old) sa /\
    fn_has_code sa sb fn /\ no_phi_fn fn /\
    MEM inst (frag_code sa sb) /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK t ==>
    ?tb tob. lookup_block t.vs_current_bb fn.fn_blocks = SOME tb /\
      lookup_block t.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME tob /\
      phi_prefix_length tb.bb_instructions = 0 /\
      phi_prefix_length tob.bb_instructions = 0 /\
      (^dyn_R) sa sb (t with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE abi_dyn_middle_terminator_target) >> strip_tac >>
  drule_all (BETA_RULE abi_dyn_middle_terminal) >> strip_tac >>
  `(^dyn_R) sa sb (t with vs_inst_idx := 0)` by
    metis_tac[BETA_RULE abi_dyn_region_jump] >>
  Cases_on `sb.cs_current_bb = sa.cs_current_bb`
  >- (`t.vs_current_bb <> sb.cs_current_bb` by metis_tac[] >>
      metis_tac[BETA_RULE abi_dyn_region_target_phi]) >>
  `emitted_blocks sa sb <> []` by
    (strip_tac >> drule entry_shape_extends >> strip_tac >>
     drule frag_extends_emitted_shape >> gvs[]) >>
  drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
    (gvs[frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  metis_tac[BETA_RULE abi_dyn_region_target_phi]
QED

Theorem abi_dyn_region_entry_prefix[local]:
  !sa sm sb s. entry_shape sm sb /\ sm.cs_blocks = sa.cs_blocks /\
    sm.cs_current_bb = sa.cs_current_bb /\
    LENGTH sa.cs_current_insts < LENGTH sm.cs_current_insts /\ at_point sa s ==>
    (^dyn_R) sa sb s
Proof
  rpt gen_tac >> strip_tac >>
  gvs[entry_shape_def, at_point_def, emitted_blocks_def] >>
  simp_tac std_ss [] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[listTheory.TAKE_APPEND2] >>
  disj2_tac >> qexists_tac `<|bb_label := sa.cs_current_bb;
    bb_instructions := sm.cs_current_insts ++ tail|>` >> simp[]
QED
Theorem abi_dyn_middle_entry[local]:
  !dst src lop base hi info asz msz i sa sb s.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    lop <> INVOKE /\ lop <> PHI /\ at_point sa s ==>
    (^dyn_R) sa sb s
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  qpat_x_assum `comp_bind _ _ sa = _` mp_tac >>
  simp_tac std_ss [Once comp_bind_def] >>
  Cases_on `emit_op ADD [src; Lit 32w] sa` >>
  rename1 `emit_op ADD [src; Lit 32w] sa = (data,sm)` >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `tail sm = ((),sb)` >> strip_tac >>
  `code_action (\opc. opc <> INVOKE /\ opc <> PHI /\
      (lop <> DJMP ==> opc <> DJMP)) tail` by
    (unabbrev_all_tac >>
     simp_tac std_ss [compile_abi_decode_dyn_elem_ptr_def,
       compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
     rpt (FIRST [irule (CONJUNCT1 abi_dyn_decode_code),
       CHANGED_TAC (ASM_SIMP_TAC std_ss [code_action_emit_op,
         code_action_emit_void, code_action_return]),
       irule code_action_bind, irule code_action_ignore_bind,
       irule code_action_emit_op, irule code_action_emit_void,
       IF_CASES_TAC, gen_tac, conj_tac]) >> simp[]) >>
  `entry_shape sm sb` by metis_tac[code_action_def, code_step_def] >>
  irule (BETA_RULE abi_dyn_region_entry_prefix) >> simp[] >> qexists_tac `sm` >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, emit_inst_def, fresh_id_def, emit_def]
QED


Theorem abi_dyn_region_cut_instruction[local]:
  !sa sb fn id s. at_point sb s ==>
    ?bb. lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])
Proof
  simp[at_point_def] >> rpt strip_tac >>
  irule_at Any frag_observer_cut_instruction >> simp[frag_observer_cut_lookup]
QED

Theorem abi_dyn_region_end[local]:
  !sa sb s. cs_extends sa sb /\
    (!bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb) /\
    at_point sb s ==> (^dyn_R) sa sb s
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [] >>
  reverse conj_tac >- gvs[at_point_def] >>
  strip_tac >> drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks sa sb = []`
  >- (simp[] >> strip_tac >> gvs[at_point_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  simp[] >> strip_tac >>
  `MEM (LAST (emitted_blocks sa sb)) (emitted_blocks sa sb)`
    by simp[rich_listTheory.MEM_LAST_NOT_NIL] >> gvs[at_point_def] >> metis_tac[]
QED

(* Quantitative cutoff diagnostic interface (implementation belongs to the
   subsequent transfer component).

   For an original fn and an exit-STOP observer obs, compare identical entry
   states in a region containing cut.  Require: both lookups succeed in the
   region; off-cut instructions agree and are non-INVOKE; successful ordinary
   successors and nonhalted jump targets stay in the region; jump-target
   instruction prefixes agree and are PHI-free.  No restriction is needed on
   instructions outside the region, GAS, ctx, or the initial halted flag.

   The finite-budget induction should prove, for every n, this trichotomy:
   (1) a real common prefix reaches cut at t with j <= n entered jumps,
       run_from (f+j) ctx fn s = run_from f ctx fn t for every f, and
       run_from n ctx0 obs s = Halt (halt_state
         (t with vs_returndata := [])); or
   (2) a genuine terminal result is common and fixed for both runs from n on;
   (3) both runs at n equal Error "out of fuel".
   Frame facts in (1) come from the actual common prefix, not fuel_outcome.

   Induct lexicographically on n and the remaining instructions of the current
   block.  At cut use j=0.  Nonterminators preserve n and decrease the latter
   measure.  An OK terminator with halted output gives (2), even when its
   position is cut; it is not an execution of the inserted STOP.  Otherwise
   n=0 gives (3), and SUC n enters the common PHI-free target and uses the
   outer IH, adding one to j.  Other instruction results give (2).  Initial
   halted states therefore need no separate semantic assumption.

   Apply fuel_outcome in ctx0 at G=0.  STOP makes either of its alternatives
   imply observer stability from some k<=K.  Apply the trichotomy at k:
   (1) gives the desired bounded prefix; (2) transfers stability.  In (3),
   observer stability fixes its result to Error "out of fuel".  For each f>=k,
   apply the trichotomy again.  Its case (1) contradicts this Error via Halt;
   its other cases equate the original result with the observer result.
   Thus the original also stays fixed from k on.  Exhaustion need not be
   mistaken for termination.  The overhead is zero for run_from: only
   entered jumps are counted; the initial partial block costs no fuel. *)
(* Metalevel notation only: no new logical constants. *)
val abi_dyn_cut_hyp = ``\R C Q (ctx:venom_context) fn (ctx0:venom_context) obs.
  (!s. R s /\ Q s /\ C s ==>
    ?bb id. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])) /\
  (!s. R s /\ Q s /\ ~C s ==>
    ?bb ob inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      lookup_block s.vs_current_bb obs.fn_blocks = SOME ob /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      get_instruction ob s.vs_inst_idx = SOME inst /\
      inst.inst_opcode <> INVOKE) /\
  (!s bb inst t. R s /\ Q s /\ ~C s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst_base inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
    R (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    Q (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!s bb inst t. R s /\ Q s /\ ~C s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst_base inst s = OK t /\ is_terminator inst.inst_opcode /\
    ~t.vs_halted ==>
    ?tb tob. lookup_block t.vs_current_bb fn.fn_blocks = SOME tb /\
      lookup_block t.vs_current_bb obs.fn_blocks = SOME tob /\
      phi_prefix_length tb.bb_instructions = 0 /\
      phi_prefix_length tob.bb_instructions = 0 /\
      R (t with vs_inst_idx := 0) /\ Q (t with vs_inst_idx := 0))``;

Theorem abi_dyn_middle_cut_hyp[local]:
  !dst src lop base hi info asz msz i sa sb N s0 ctx fn ctx0 id.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    ~is_terminator lop /\ lop <> INVOKE /\ lop <> PHI /\ (^dyn_Old) sa /\
    N <= sa.cs_next_var /\ fn_has_code sa sb fn /\ no_phi_fn fn ==>
    (^abi_dyn_cut_hyp) ((^dyn_R) sa sb) (at_point sb)
      (\s. vars_kept N {} s0 s /\ s.vs_labels = s0.vs_labels)
      ctx fn ctx0 (frag_observer sa sb fn id)
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE abi_dyn_middle_terminal) >> strip_tac >>
  drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >> strip_tac >>
  simp_tac std_ss [] >> conj_tac
  >- metis_tac[abi_dyn_region_cut_instruction] >>
  conj_tac
  >- metis_tac[BETA_RULE abi_dyn_middle_off_cut] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM inst (frag_code sa sb)` by
        metis_tac[BETA_RULE abi_dyn_region_code, entry_shape_extends] >>
      `inst.inst_opcode <> INVOKE` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      `vars_kept N {} s t /\ t.vs_labels = s.vs_labels` by
        metis_tac[BETA_RULE abi_dyn_middle_frame] >>
      `(^dyn_R) sa sb (t with vs_inst_idx := SUC s.vs_inst_idx)` by
        (irule abi_dyn_region_step >> simp[] >> metis_tac[]) >>
      `vars_kept N {} s0 t` by metis_tac[vars_kept_trans] >>
      gvs[vars_kept_def, lookup_var_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `MEM inst (frag_code sa sb)` by
    metis_tac[BETA_RULE abi_dyn_region_code, entry_shape_extends] >>
  `vars_kept N {} s t /\ t.vs_labels = s.vs_labels` by
    metis_tac[BETA_RULE abi_dyn_middle_frame] >>
  drule_all (BETA_RULE abi_dyn_middle_jump) >>
  disch_then (qspec_then `id` mp_tac) >> strip_tac >>
  qexistsl_tac [`tb`, `tob`] >> simp[] >>
  `vars_kept N {} s0 t` by metis_tac[vars_kept_trans] >>
  gvs[vars_kept_def, lookup_var_def] >> metis_tac[]
QED

Theorem abi_dyn_middle_region_interface[local]:
  !dst src lop base hi info asz msz i sa sb N s0 ctx fn ctx0 id.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    ~is_terminator lop /\ lop <> INVOKE /\ lop <> PHI /\ (^dyn_Old) sa /\
    N <= sa.cs_next_var /\ fn_has_code sa sb fn /\ no_phi_fn fn ==>
    (!s. at_point sa s ==> (^dyn_R) sa sb s) /\
    (!s. at_point sb s ==> (^dyn_R) sa sb s) /\
    fn_has_code sa sb (frag_observer sa sb fn id) /\
    (^abi_dyn_cut_hyp) ((^dyn_R) sa sb) (at_point sb)
      (\s. vars_kept N {} s0 s /\ s.vs_labels = s0.vs_labels)
      ctx fn ctx0 (frag_observer sa sb fn id)
Proof
  rpt gen_tac >> strip_tac >> rule_assum_tac BETA_RULE >>
  `!bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb`
    by metis_tac[BETA_RULE abi_dyn_middle_final_exclusion] >>
  `cs_extends sa sb` by
    (drule_all (SRULE [code_action_def, code_step_def] abi_dyn_middle_code) >>
     metis_tac[entry_shape_extends]) >>
  conj_tac >- metis_tac[BETA_RULE abi_dyn_middle_entry] >>
  conj_tac >- metis_tac[BETA_RULE abi_dyn_region_end] >>
  conj_tac >- metis_tac[abi_dyn_observer_has_code] >>
  irule abi_dyn_middle_cut_hyp >> simp_tac std_ss [] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_assum `comp_bind _ _ sa = _` (irule_at Any) >> simp[]
QED

val abi_dyn_cut_result = ``\C Q ctx fn ctx0 obs n s.
  (?j t. j <= n /\ C t /\ Q t /\
    (!f. run_from (f+j) ctx fn s = run_from f ctx fn t) /\
    run_from n ctx0 obs s = Halt (halt_state (t with vs_returndata := []))) \/
  (?r. !f. n <= f ==> run_from f ctx fn s = r /\
                        run_from f ctx0 obs s = r) \/
  (run_from n ctx fn s = Error "out of fuel" /\
   run_from n ctx0 obs s = Error "out of fuel")``;

Theorem abi_dyn_cutoff_trichotomy[local]:
  !R C Q ctx fn ctx0 obs.
    ^abi_dyn_cut_hyp R C Q ctx fn ctx0 obs ==>
    !n s. R s /\ Q s ==> ^abi_dyn_cut_result C Q ctx fn ctx0 obs n s
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> completeInduct_on `n` >>
  gen_tac >> measureInduct_on
    `(\s. case lookup_block s.vs_current_bb fn.fn_blocks of
       NONE => 0 | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) s` >>
  rpt strip_tac >> rename1 `R ss` >> Cases_on `C ss`
  >- (disj1_tac >> qexistsl_tac [`0`, `ss`] >> simp[] >>
      qpat_x_assum `!s. R s /\ Q s /\ C s ==> _` drule_all >>
      strip_tac >> irule fragExecTheory.run_from_halt >>
      goal_assum (drule_at Any) >>
      simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  qpat_x_assum `!s. R s /\ Q s /\ ~C s ==> _` drule_all >>
  strip_tac >> Cases_on `step_inst_base inst ss`
  >- suspend "ok" >>
  disj2_tac >> disj1_tac >> qexists_tac `run_from n ctx fn ss` >>
  rpt strip_tac >>
  `!fuel ctxt. run_from fuel ctxt fn ss = step_inst_base inst ss` by
    (irule abi_dyn_run_from_exit >> simp[] >> metis_tac[exec_result_distinct]) >>
  `!fuel ctxt. run_from fuel ctxt obs ss = step_inst_base inst ss` by
    (irule abi_dyn_run_from_exit >> simp[] >> metis_tac[exec_result_distinct]) >>
  simp[]
QED

Resume abi_dyn_cutoff_trichotomy[ok]:
  rename1 `step_inst_base inst ss = OK next` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "term" >>
  `!fuel. run_from fuel ctx fn ss =
      run_from fuel ctx fn (next with vs_inst_idx := SUC ss.vs_inst_idx)` by
    (gen_tac >> irule fragExecTheory.run_from_step >> simp[]) >>
  `!fuel. run_from fuel ctx0 obs ss =
      run_from fuel ctx0 obs (next with vs_inst_idx := SUC ss.vs_inst_idx)` by
    (gen_tac >> irule fragExecTheory.run_from_step >> simp[]) >>
  qpat_x_assum `!s bb inst t. _ ==> R (t with vs_inst_idx := _) /\ _` drule_all >>
  strip_tac >>
  `next.vs_current_bb = ss.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `ss.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then
    `next with vs_inst_idx := SUC ss.vs_inst_idx` mp_tac) >>
  simp[]
QED

Resume abi_dyn_cutoff_trichotomy[term]:
  Cases_on `next.vs_halted`
  >- (disj2_tac >> disj1_tac >> qexists_tac `Halt next` >>
      rpt strip_tac >> metis_tac[abi_dyn_run_from_term]) >>
  qpat_x_assum `!s bb inst t. _ ==> ?tb tob. _` drule_all >>
  strip_tac >>
  Cases_on `n`
  >- (disj2_tac >> disj2_tac >> conj_tac >>
      irule abi_dyn_run_from_term_zero >> simp[]) >>
  rename1 `SUC k` >>
  `!fuel. run_from (SUC fuel) ctx fn ss =
      run_from fuel ctx fn (next with vs_inst_idx := 0)` by
    (gen_tac >> irule abi_dyn_run_from_term_enter >> simp[]) >>
  `!fuel. run_from (SUC fuel) ctx0 obs ss =
      run_from fuel ctx0 obs (next with vs_inst_idx := 0)` by
    (gen_tac >> irule abi_dyn_run_from_term_enter >> simp[]) >>
  qpat_x_assum `!y. _ < _ ==> _` kall_tac >>
  qpat_x_assum `!m. m < _ ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> disch_then (qspec_then `next with vs_inst_idx := 0` mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`SUC j`, `t`] >> simp[arithmeticTheory.ADD_CLAUSES])
  >- (disj2_tac >> disj1_tac >> qexists_tac `r` >>
      gen_tac >> strip_tac >> Cases_on `f` >> gvs[]) >>
  disj2_tac >> disj2_tac >> simp[]
QED

Finalise abi_dyn_cutoff_trichotomy

Theorem abi_dyn_cutoff_stable[local]:
  !R C Q ctx fn ctx0 obs k s.
    ^abi_dyn_cut_hyp R C Q ctx fn ctx0 obs /\ R s /\ Q s /\
    (!f. k <= f ==> run_from f ctx0 obs s = run_from k ctx0 obs s) ==>
    (?j t. j <= k /\ C t /\ Q t /\
       (!f. run_from (f+j) ctx fn s = run_from f ctx fn t)) \/
    (!f. k <= f ==> run_from f ctx fn s = run_from k ctx fn s)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_dyn_cutoff_trichotomy >>
  disch_then (fn th => qspec_then `k` mp_tac th >> assume_tac th) >>
  disch_then (qspec_then `s` mp_tac) >>
  (impl_tac >- simp[]) >> BETA_TAC >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`j`, `t`] >> simp[]) 
  >- (disj2_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  disj2_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!n s. _` (qspec_then `f` mp_tac) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> BETA_TAC >>
  strip_tac >> metis_tac[exec_result_distinct, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem abi_dyn_empty_context_stable[local]:
  !ctx fn G. callees_stable G (ctx with ctx_functions := []) fn
Proof
  simp[callees_stable_def, venomInstTheory.lookup_function_def,
       listTheory.FIND_thm]
QED

Theorem abi_dyn_non_invoke_context[local]:
  !f g ctx ctx' inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst f ctx inst s = step_inst g ctx' inst s
Proof
  simp[venomExecSemanticsTheory.step_inst_non_invoke]
QED

(* Cutoff diagnostic: a continuation witness becomes a state observation,
   but the fixed-result alternative remains a distinct obligation. *)
Theorem abi_dyn_cutoff_observation[local]:
  !G ctx fn s j P bb id.
    (!t. P t ==>
       lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] [])) /\
    fuel_outcome G ctx fn s j P ==>
    (?t. P t /\ run_from (G+j) ctx fn s =
       Halt (halt_state (t with vs_returndata := []))) \/
    (!f. G <= f ==> run_from (f+j) ctx fn s = run_from (G+j) ctx fn s)
Proof
  rpt gen_tac >> strip_tac >> gvs[fuel_outcome_def] >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  qpat_x_assum `!f. G <= f ==> _` (qspec_then `G` mp_tac) >>
  simp[] >> strip_tac >> asm_rewrite_tac[] >>
  irule fragExecTheory.run_from_halt >>
  qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def]
QED

Theorem abi_dyn_observer_no_phi[local]:
  !sa sb fn id. fn_has_code sa sb fn /\ no_phi_fn fn ==>
    no_phi_fn (frag_observer sa sb fn id)
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    IS_PREFIX bb.bb_instructions sb.cs_current_insts` by gvs[fn_has_code_def] >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (drule venomExecProofsTheory.lookup_block_MEM >>
     gvs[no_phi_fn_def, EVERY_MEM] >> metis_tac[]) >>
  simp[frag_observer_def, no_phi_fn_def] >> conj_tac
  >- (gvs[rich_listTheory.IS_PREFIX_APPEND] >>
      Cases_on `sb.cs_current_insts` >>
      gvs[phi_prefix_length_def, mk_inst_def, AllCaseEqs()]) >>
  gvs[no_phi_fn_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem abi_dyn_observer_outcome_stable[local]:
  !sa sb fn id ctx s j P.
    (!t. P t ==> at_point sb t) /\
    fuel_outcome 0 ctx (frag_observer sa sb fn id) s j P ==>
    !f. j <= f ==> run_from f ctx (frag_observer sa sb fn id) s =
      run_from j ctx (frag_observer sa sb fn id) s
Proof
  rpt gen_tac >> strip_tac >> gvs[fuel_outcome_def]
  >- (`!f. run_from f ctx (frag_observer sa sb fn id) t =
          Halt (halt_state (t with vs_returndata := []))` by
        (gen_tac >> `at_point sb t` by metis_tac[] >>
         gvs[at_point_def] >> irule fragExecTheory.run_from_halt >>
         qexistsl_tac [`<|bb_label := sb.cs_current_bb;
           bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
           `mk_inst id STOP [] []`] >>
         simp[frag_observer_cut_lookup, step_inst_base_opcode_eqs, mk_inst_def] >>
         simp[get_instruction_def, EL_APPEND_EQN]) >>
      rpt strip_tac >>
      `f = (f-j)+j` by simp[] >>
      qpat_assum `!f. _ = run_from f _ _ t` (qspec_then `f-j` mp_tac) >>
      qpat_x_assum `!f. _ = run_from f _ _ t` (qspec_then `0` mp_tac) >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!f. _` (qspec_then `f-j` mp_tac) >> simp[]
QED

(* Primitive footprint probe for the structural middle certificate. *)
Theorem abi_dyn_middle_framed_bound[local]:
  !dst src lop base hi info asz msz i sa sb.
    (^dyn_middle) dst src lop base hi info asz msz i sa = ((),sb) /\
    ~is_terminator lop /\ lop <> PHI /\ lop <> INVOKE /\ (^dyn_Old) sa /\
    (!d s Wv E. fuel_ok Wv {} E
      (compile_abi_decode_to_buf d s lop base hi info)) ==>
    ?K. !G N ctx fn s.
      N <= sa.cs_next_var /\ no_phi_fn fn /\ fn_has_code sa sb fn /\ at_point sa s ==>
      ?j. j <= K /\ fuel_outcome G ctx fn s j
        (\t. at_point sb t /\ vars_kept N {} s t /\ t.vs_labels = s.vs_labels)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `(^dyn_middle) dst src lop bop hi info asz msz i sa = ((),sb)` >>
  `fuel_ok {} {} {} ((^dyn_middle) dst src lop bop hi info asz msz i)` by
    (BETA_TAC >> irule fuel_ok_decode_dyn_body_middle >> simp[]) >>
  qpat_x_assum `fuel_ok _ _ _ _` (mp_tac o REWRITE_RULE [fuel_ok_def]) >>
  disch_then drule >> strip_tac >> qexists_tac `Kb` >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa sb (frag_observer sa sb fn 0)` by
    (irule abi_dyn_observer_has_code >> simp[] >>
     metis_tac[BETA_RULE abi_dyn_middle_final_exclusion]) >>
  `no_phi_fn (frag_observer sa sb fn 0)` by metis_tac[abi_dyn_observer_no_phi] >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` (mp_tac o REWRITE_RULE [frag_fuel_def]) >>
  disch_then (qspecl_then [`0`, `N`, `ctx with ctx_functions := []`,
    `frag_observer sa sb fn 0`, `s`] mp_tac) >>
  simp[abi_dyn_empty_context_stable] >> strip_tac >>
  `!f. j <= f ==> run_from f (ctx with ctx_functions := [])
      (frag_observer sa sb fn 0) s =
      run_from j (ctx with ctx_functions := []) (frag_observer sa sb fn 0) s` by
    (drule_at Any abi_dyn_observer_outcome_stable >> simp[]) >>
  `(^abi_dyn_cut_hyp) ((^dyn_R) sa sb) (at_point sb)
      (\t. vars_kept N {} s t /\ t.vs_labels = s.vs_labels)
      ctx fn (ctx with ctx_functions := []) (frag_observer sa sb fn 0)` by
    (irule abi_dyn_middle_cut_hyp >> rule_assum_tac BETA_RULE >>
     simp_tac std_ss [] >> qpat_assum `comp_bind _ _ sa = _` (irule_at Any) >> simp[]) >>
  `(^dyn_R) sa sb s` by
    (irule abi_dyn_middle_entry >> rule_assum_tac BETA_RULE >>
     simp_tac std_ss [] >> qpat_assum `comp_bind _ _ sa = _` (irule_at Any) >> simp[]) >>
  `vars_kept N {} s s /\ s.vs_labels = s.vs_labels` by simp[vars_kept_def] >>
  drule abi_dyn_cutoff_stable >>
  disch_then (qspecl_then [`j`, `s`] mp_tac) >>
  simp_tac std_ss [] >>
  (impl_tac >- (rule_assum_tac BETA_RULE >> simp[])) >> strip_tac
  >- (qexists_tac `j'` >> simp[fuel_outcome_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexists_tac `j` >> simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
  `j <= f+j /\ j <= G+j` by simp[] >> metis_tac[]
QED

Theorem abi_dyn_add_one_outcome[local]:
  !a sa op sb G N ctx fn s w.
    emit_op ADD [a; Lit 1w] sa = (op, sb) /\
    N <= sa.cs_next_var /\ callees_stable G ctx fn /\
    fn_has_code sa sb fn /\ at_point sa s /\ eval_operand a s = SOME w ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
        t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
        eval_operand op t = SOME (w + 1w))
Proof
  rpt strip_tac >>
  `~is_terminator ADD` by simp[is_terminator_def] >>
  drule_all abi_dyn_emit_op_outcome >> strip_tac >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  `op = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem abi_dyn_mstore_outcome[local]:
  !ptr value sa sb G N ctx fn s p w.
    emit_void MSTORE [ptr; value] sa = ((), sb) /\
    callees_stable G ctx fn /\ fn_has_code sa sb fn /\ at_point sa s /\
    eval_operand ptr s = SOME p /\ eval_operand value s = SOME w ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept N {} s t /\
        t.vs_labels = s.vs_labels /\ mload (w2n p) t = w)
Proof
  rpt strip_tac >> rename1 `emit_void MSTORE [ptr_op; value] sa = ((), sb)` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [ptr_op; value] []]` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  drule_then (qspecl_then [`s`, `bb`,
    `mk_inst sa.cs_next_id MSTORE [ptr_op; value] []`] mp_tac)
    run_from_nonterm_stable >>
  simp[mk_inst_def, is_terminator_def] >>
  (impl_tac >- gvs[at_point_def, mk_inst_def]) >> strip_tac
  >- (simp[fuel_outcome_def] >> disj1_tac >>
      qexists_tac `s1 with vs_inst_idx := SUC s.vs_inst_idx` >> simp[] >>
      gvs[at_point_def, vars_kept_def, step_inst_non_invoke,
          mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def,
          eval_operands_def, lookup_var_def] >>
      `mload (w2n p) (mstore (w2n p) w s with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)) =
       mload (w2n p) (mstore (w2n p) w s)` by simp[mload_def] >>
      conj_tac >- simp[mstore_def] >>
      simp[venomMemPropsTheory.mload_mstore_same]) >>
  simp[fuel_outcome_def]
QED

Theorem abi_dyn_jmp_outcome[local]:
  !sa sb hdr G N ctx fn s.
    emit_inst JMP [Label hdr] [] sa = ((),sb) /\
    no_phi_fn fn /\ fn_has_code sa sb fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 1
      (\t. vars_kept N {} s t /\ t.vs_memory = s.vs_memory /\
        t.vs_labels = s.vs_labels /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0)
Proof
  rpt strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id JMP [Label hdr] []]` by
    gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `mk_inst sa.cs_next_id JMP [Label hdr] []`, `hdr`] >>
  simp[mk_inst_def, is_terminator_def] >> conj_tac
  >- (simp[step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def, jump_to_def]) >>
  gvs[jump_to_def, vars_kept_def, lookup_var_def, at_point_def, mk_inst_def]
QED

Theorem abi_dyn_body_suffix_outcome[local]:
  !a ptr_op sa new_i sm sn sb hdr G N ctx fn s p w.
    emit_op ADD [a; Lit 1w] sa = (new_i,sm) /\
    emit_void MSTORE [ptr_op; new_i] sm = ((),sn) /\
    emit_inst JMP [Label hdr] [] sn = ((),sb) /\
    N <= sa.cs_next_var /\ (!x. ptr_op = Var x ==> var_below N x) /\
    callees_stable G ctx fn /\ no_phi_fn fn /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn /\
    at_point sa s /\ eval_operand ptr_op s = SOME p /\ eval_operand a s = SOME w ==>
    ?j. j <= 1 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N {} s t /\ t.vs_labels = s.vs_labels /\
        eval_operand ptr_op t = SOME p /\ mload (w2n p) t = w + 1w /\
        t.vs_current_bb = hdr /\ t.vs_inst_idx = 0)
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s _ Q` >>
  drule_all abi_dyn_add_one_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Q`, `1`] mp_tac) >> impl_tac
  >- (simp[] >> rpt strip_tac >>
      `eval_operand ptr_op t = SOME p` by
        (drule_all abi_dyn_eval_operand_kept >> simp[]) >>
      `fuel_outcome G ctx fn t 0
        (\u. at_point sn u /\ vars_kept N {} t u /\
          u.vs_labels = t.vs_labels /\ mload (w2n p) u = w + 1w)` by
        (irule abi_dyn_mstore_outcome >>
         qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >> simp[]) >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then [`Q`, `1`] mp_tac) >> impl_tac
      >- (simp[] >> rpt strip_tac >>
          `fuel_outcome G ctx fn t' 1
            (\u. vars_kept N {} t' u /\ u.vs_memory = t'.vs_memory /\
              u.vs_labels = t'.vs_labels /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0)` by
            (irule abi_dyn_jmp_outcome >>
             qpat_assum `emit_inst JMP _ _ _ = _` (irule_at Any) >> simp[]) >>
          qexists_tac `1` >> simp[] >>
          irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
          simp[Abbr `Q`] >> qx_gen_tac `u` >> strip_tac >>
          `vars_kept N {} s u` by metis_tac[vars_kept_trans] >>
          `eval_operand ptr_op u = SOME p` by
            (drule_all abi_dyn_eval_operand_kept >> simp[]) >>
          gvs[mload_def]) >> simp[]) >> simp[]
QED

Theorem abi_dyn_body_outcome[local]:
  !dst src lop bop hi info asz msz ptr_op sa saved sm sn new_i sp sq sb hdr N.
    emit_op MLOAD [ptr_op] sa = (saved,sm) /\
    (^dyn_middle) dst src lop bop hi info asz msz saved sm = ((),sn) /\
    emit_op ADD [saved; Lit 1w] sn = (new_i,sp) /\
    emit_void MSTORE [ptr_op; new_i] sp = ((),sq) /\
    emit_inst JMP [Label hdr] [] sq = ((),sb) /\
    ~is_terminator lop /\ lop <> PHI /\ lop <> INVOKE /\ (^dyn_Old) sm /\
    (!d s Wv E. fuel_ok Wv {} E (compile_abi_decode_to_buf d s lop bop hi info)) /\
    N <= sa.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
    (!x. ptr_op = Var x ==> var_below N x) ==>
    ?Kbody. !G ctx fn s p.
      callees_stable G ctx fn /\ no_phi_fn fn /\
      fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
      fn_has_code sn sp fn /\ fn_has_code sp sq fn /\ fn_has_code sq sb fn /\
      at_point sa s /\ eval_operand ptr_op s = SOME p ==>
      ?j. j <= Kbody /\ fuel_outcome G ctx fn s j
        (\t. vars_kept N {} s t /\ t.vs_labels = s.vs_labels /\
          eval_operand ptr_op t = SOME p /\
          mload (w2n p) t = mload (w2n p) s + 1w /\
          t.vs_current_bb = hdr /\ t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> strip_tac >>
  rule_assum_tac BETA_RULE >>
  drule_all (BETA_RULE abi_dyn_middle_framed_bound) >>
  disch_then (qx_choose_then `Km` assume_tac) >>
  qexists_tac `Km+1` >> rpt gen_tac >> strip_tac >>
  `N <= sm.cs_next_var /\
   saved = Var (STRING #"%" (toString sa.cs_next_var)) /\
   var_below sm.cs_next_var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def, var_below_def] >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s _ Q` >>
  drule_all abi_dyn_mload_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Q`, `Km+1`] mp_tac) >> impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!G N ctx fn s. _`
        (qspecl_then [`G`, `sm.cs_next_var`, `ctx`, `fn`, `t`] mp_tac) >>
      simp[] >> strip_tac >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then [`Q`, `1`] mp_tac) >> impl_tac
      >- (simp[] >> rpt strip_tac >>
          `eval_operand saved t' = SOME (mload (w2n p) s)` by
            (gvs[vars_kept_def, eval_operand_def] >> metis_tac[]) >>
          `vars_kept N {} t t'` by
            (gvs[vars_kept_def, var_below_def] >>
             metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
          `vars_kept N {} s t'` by metis_tac[vars_kept_trans] >>
          `eval_operand ptr_op t' = SOME p` by
            (drule_all abi_dyn_eval_operand_kept >> simp[]) >>
          `N <= sn.cs_next_var` by decide_tac >>
          drule_all abi_dyn_body_suffix_outcome >> strip_tac >>
          qexists_tac `j'` >> simp[] >>
          irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
          simp[Abbr `Q`] >> rpt strip_tac >> metis_tac[vars_kept_trans]) >>
      simp[] >> strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac) >>
  simp[]
QED

Theorem abi_dyn_emit_op_footprint[local]:
  !opc ops st out st'.
    emit_op opc ops st = (out,st') ==>
    EVERY (\i. i.inst_opcode = opc /\
       EVERY (\x. ~var_below st.cs_next_var x) i.inst_outputs)
      (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
Proof
  rpt strip_tac >>
  drule exprLoweringPropsTheory.emitted_insts_emit_op_local >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >> strip_tac >>
  simp[listTheory.DROP_APPEND, mk_inst_def, var_below_def] >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_dyn_counter_rank[local]:
  !w:bytes32.
    (2 ** 256 - 1) - w2n w < 2 ** 256 /\
    (w2n w < 2 ** 256 - 1 ==>
     (2 ** 256 - 1) - w2n (w + 1w) < (2 ** 256 - 1) - w2n w)
Proof
  gen_tac >> conj_tac >- simp[] >>
  strip_tac >>
  `w2n (w + 1w) = w2n w + 1` by
    (gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
         wordsTheory.dimword_def, arithmeticTheory.LESS_MOD]) >>
  gvs[]
QED

Theorem abi_dyn_ranked_round[local]:
  !P (C:venom_state -> bytes32) hdr body_lbl exit Kh Kbody G ctx fn.
    (!s. P s /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
      ?j. j <= Kh /\ fuel_outcome G ctx fn s j
        (\t. P t /\ C t = C s /\ t.vs_inst_idx = 0 /\
          (t.vs_current_bb = exit \/
           (t.vs_current_bb = body_lbl /\ w2n (C s) < 2 ** 256 - 1)))) /\
    (!s. P s /\ s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 ==>
      ?j. j <= Kbody /\ fuel_outcome G ctx fn s j
        (\t. P t /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ C t = C s + 1w)) ==>
    let H = (\s. P s /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0);
        Q = (\s. P s /\ s.vs_current_bb = exit /\ s.vs_inst_idx = 0);
        mu = (\s. (2 ** 256 - 1) - w2n (C s))
    in (!s. H s ==> mu s < 2 ** 256) /\
       (!s. H s ==> ?j. j <= Kh + Kbody /\ fuel_outcome G ctx fn s j
         (\t. Q t \/ (H t /\ mu t < mu s)))
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn s _ Qr` >>
  qpat_x_assum `!s. P s /\ s.vs_current_bb = hdr /\ _ ==> _`
    (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Qr`, `Kbody`] mp_tac) >> impl_tac
  >- (simp[] >> rpt strip_tac
      >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> simp[Abbr `Qr`]) >>
      qpat_x_assum `!s. _` (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `j'` >> simp[] >>
      irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
      simp[Abbr `Qr`] >> rpt strip_tac >>
      disj2_tac >> qspec_then `C s` mp_tac abi_dyn_counter_rank >> simp[]) >>
  strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac
QED

(* The counter need not be disjoint from the element destination.  The
   final MSTORE overwrites any writes by the element decoder.  The bound
   is reloaded at every header and need not stay fixed. *)
Theorem fuel_okS_compile_abi_decode_dyn_loop:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt.
    ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE /\
    (!d s Wv E.
       fuel_ok Wv {} E
         (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    !Wv E.
      fuel_okS (\st. !x. i_ptr = Var x ==> var_below st.cs_next_var x)
        Wv {} E
        (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
           elem_info elem_abi_sz elem_mem_sz i_ptr cnt)
Proof
  cheat
QED
