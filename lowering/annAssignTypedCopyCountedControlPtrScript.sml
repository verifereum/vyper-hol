(* Counted control paths for typed-copy loops.  Register-only jumps permit
   changes to prev_bb; the ambient state frame intentionally abstracts them. *)
Theory annAssignTypedCopyCountedControlPtr
Ancestors
  assignBasePtrStoragePath assignBasePtrStorageLayout bodyPtrBopInLoopSearch
  typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr typedMemoryCopy fragGasPathPtr
  bodyPtrDefs venomState venomExecSemantics venomInst words finite_map
  ptrDiscipline list arithmetic

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
