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
    code_action (\opc. opc <> INVOKE /\ opc <> PHI)
      (compile_abi_decode_to_buf dst src lop base hi info)) /\
  (!dst src lop base hi elems ao vo.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI)
      (compile_abi_decode_complex_elems dst src lop base hi elems ao vo)) /\
  (!dst src lop base hi info asz msz ip cnt.
    lop <> INVOKE /\ lop <> PHI ==>
    code_action (\opc. opc <> INVOKE /\ opc <> PHI)
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

(* Primitive footprint probe for the structural middle certificate. *)
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
