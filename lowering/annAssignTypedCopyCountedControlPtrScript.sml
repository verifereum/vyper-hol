(* Counted control paths for typed-copy loops.  Register-only jumps permit
   changes to prev_bb; the ambient state frame intentionally abstracts them. *)
Theory annAssignTypedCopyCountedControlPtr
Ancestors
  assignBasePtrStoragePath assignBasePtrStorageLayout bodyPtrBopInLoopSearch
  typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr typedMemoryCopy fragGasPathPtr
  bodyPtrDefs venomState venomExecSemantics venomInst words finite_map
  ptrDiscipline list arithmetic
Libs typedCopyLoopAmbientLib

Theorem annassign_loop_register_frame:
  !sa off len s p q a b lbl G tn.
    (!x. not_fresh_at sa x ==> x <> p /\ x <> q) ==>
    typed_copy_state_frame sa off len s
      (jump_to lbl (update_var q b (update_var p a s))) /\
    (!x. x <> p /\ x <> q ==>
      lookup_var x (jump_to lbl (update_var q b (update_var p a s))) =
        lookup_var x s /\
      FLOOKUP (DRESTRICT (DRESTRICT G (COMPL {p})) (COMPL {q})) x =
        FLOOKUP G x /\
      op_taint (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})) (Var x) =
        op_taint tn (Var x)) /\
    (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})).t_mem = tn.t_mem /\
    (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})).t_stor = tn.t_stor /\
    (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})).t_trans = tn.t_trans /\
    (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})).t_imm = tn.t_imm
Proof
  rpt strip_tac >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
       jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
       venom_state_component_equality]
QED

Theorem annassign_loop_test_exact_counted:
  !s fn bb id ctr lt done i n bodylbl exit tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id LT [Var ctr;Lit (n2w n)] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ISZERO [Var lt] [done]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JNZ [Var done;Label exit;Label bodylbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ i <= n /\ n < dimword (:256) /\
    op_taint tn (Var ctr) = {} /\ ALL_DISTINCT [ctr;lt;done] /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
      (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
      (OK (jump_to (if i<n then bodylbl else exit)
        (update_var done (bool_to_word (~(i<n)))
          (update_var lt (bool_to_word (i<n)) s))))
Proof
  rpt gen_tac >> strip_tac >>
  `ctr <> lt /\ ctr <> done` by gvs[ALL_DISTINCT] >>
  `step_inst_base (mk_inst id LT [Var ctr;Lit (n2w n)] [lt]) s =
    OK (update_var lt (bool_to_word (i<n)) s)` by
    (asm_simp_tac bool_ss [step_inst_base_opcode_eqs,
       mk_inst_def, instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD]) >>
  qabbrev_tac `s1 = update_var lt (bool_to_word (i<n)) s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule assign_base_storage_test_counted >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     gvs[op_taint_def]) >>
  qabbrev_tac `s2 = update_var done (bool_to_word (~(i<n))) s1
    with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {done})` >>
  qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2)` by
    (simp[Abbr `s2`, Abbr `g2`, Abbr `t2`] >>
     irule assign_base_storage_test_counted >>
     simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `ISZERO`, `[Var lt]`] >>
     gvs[Abbr `t1`, update_var_def, lookup_var_def,
         op_taint_def, FLOOKUP_UPDATE] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >>
     simp[exec_pure1_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     Cases_on `i<n` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t2
    (OK (jump_to (if ~(i<n) then exit else bodylbl) s2))` by
    (irule assign_base_storage_branch_counted >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+2`, `Var done`] >>
     simp[Abbr `t2`, eval_operand_def, ADD1,
          lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `i<n` >> simp[bool_to_word_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s (0+0+0) g2 t2
    (OK (jump_to (if ~(i<n) then exit else bodylbl) s2))` by
    (metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
  gvs[Abbr `g2`, Abbr `g1`, Abbr `t2`, Abbr `t1`,
      Abbr `s2`, Abbr `s1`, jump_to_def, update_var_def] >>
  Cases_on `i<n` >> gvs[]
QED

Theorem annassign_loop_address_exact_counted[local]:
  !s fn bb id ctr sr dr so doff sp dp i ss ds a b tn G ctx D PG
   s1 s2 u3 s3 u4 s4 g1 g2 g3 g4 tn1 tn2 tn3 tn4.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ADD [Var sr;Var so] [sp]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) /\
    lookup_var ctr s = SOME (n2w i) /\ lookup_var sr s = SOME a /\
    lookup_var dr s = SOME b /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var sr) = {} /\
    op_taint tn (Var dr) = {} /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    ~ctx_has_dalloca ctx /\
    s1 = (update_var so (n2w (i*ss)) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    s2 = (update_var doff (n2w (i*ds)) s1 with vs_inst_idx := SUC s1.vs_inst_idx) /\
    u3 = update_var sp (a+n2w (i*ss)) s2 /\
    s3 = (u3 with vs_inst_idx := SUC s2.vs_inst_idx) /\
    u4 = update_var dp (b+n2w (i*ds)) s3 /\
    s4 = (u4 with vs_inst_idx := SUC s3.vs_inst_idx) /\
    g1 = DRESTRICT G (COMPL {so}) /\
    g2 = DRESTRICT g1 (COMPL {doff}) /\
    tn1 = (tn with t_var := tn.t_var |+ (so,{})) /\
    tn2 = (tn1 with t_var := tn1.t_var |+ (doff,{})) /\
    g3 = step_prov PG g2 (mk_inst (id+2) ADD [Var sr;Var so] [sp]) u3 /\
    tn3 = step_taint (mk_inst (id+2) ADD [Var sr;Var so] [sp]) s2 u3 tn2 /\
    g4 = step_prov PG g3 (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) u4 /\
    tn4 = step_taint (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) s3 u4 tn3 ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 g4 tn4 (OK s4)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (asm_rewrite_tac [] >> rewrite_tac[GSYM word_mul_n2w] >>
     irule storageCopyBodyPtrTheory.storage_copy_mul_path_ptr >>
     simp[] >> qexistsl_tac [`id`, `Var ctr`, `Lit (n2w ss)`] >>
     gvs[eval_operand_def, op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)` by
    (asm_rewrite_tac [] >> rewrite_tac[GSYM word_mul_n2w] >>
     irule storageCopyBodyPtrTheory.storage_copy_mul_path_ptr >>
     simp[update_var_def] >>
     qexistsl_tac [`id+1`, `Var ctr`, `Lit (n2w ds)`] >>
     gvs[ALL_DISTINCT, eval_operand_def, op_taint_def, word_mul_n2w,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE, ADD1]) >>
  `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)` by
    (asm_rewrite_tac [] >> irule assign_base_copy_binop_counted >>
     gvs[ALL_DISTINCT, eval_operand_def, op_taint_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, ADD1] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx fn PG g3 tn3 s3 0 g4 tn4 (OK s4)` by
    (asm_rewrite_tac [] >> irule assign_base_copy_binop_counted >>
     gvs[ALL_DISTINCT, eval_operand_def, op_taint_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, ADD1,
         typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
     asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def,
       instruction_accessors, instruction_accfupds, combinTheory.K_THM,
       opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Theorem annassign_loop_address_counted:
  !ctx PG fn D bb sa ctr so doff sp dp sr dr id i ss ds a b S T G tn s.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ADD [Var sr;Var so] [sp]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    (!v. not_fresh_at sa v ==> ~MEM v [so;doff;sp;dp]) /\
    i*ss < S /\ i*ss+ss <= S /\ i*ds < T /\ i*ds+ds <= T /\
    w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) ==>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      typed_copy_state_frame sa 0 0 s sf /\
      sf.vs_current_bb = s.vs_current_bb /\
      sf.vs_inst_idx = s.vs_inst_idx+4 /\ ~sf.vs_halted /\
      lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
      lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
      ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
      sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
      tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. ~MEM p [so;doff;sp;dp] ==>
        lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
        op_taint tnf (Var p)=op_taint tn (Var p))
Proof
  typedCopyLoopAmbientLib.address_witnesses >>
  conj_tac >-
    (irule annassign_loop_address_exact_counted >>
     simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
          Abbr `g4`, Abbr `g3`, Abbr `g2`, Abbr `g1`,
          Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >>
     simp[mk_inst_def, instruction_component_equality] >>
     qexistsl_tac [`ds`, `i`, `ss`] >> simp[] >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >-
    (simp[typed_copy_state_frame_def, typed_copy_frame_def,
          Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> res_tac >> gvs[]) >>
  `s4.vs_current_bb = s.vs_current_bb /\
   s4.vs_inst_idx = s.vs_inst_idx+4 /\ ~s4.vs_halted` by
    simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
         update_var_def, ADD1] >>
  simp[] >>
  typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers
QED
