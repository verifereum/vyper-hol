(*
 * Fuel bound for the dynamic-array ABI decode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_decode_dyn_loop
 *)

Theory fragFuelLoopAbiDecDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
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
