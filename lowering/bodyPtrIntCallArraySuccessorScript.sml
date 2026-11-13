(* Operational boundaries for a single non-fast array-loop iteration. *)
Theory bodyPtrIntCallArraySuccessor
Ancestors
  bodyPtrIntCallArrayLoop bodyPtrIntCallArrayInvariant
  typedArrayLoopCode typedArrayLoopHeader typedArrayLoopCounter abiStaticLoopCode
  abiStaticLoopBody
  ssaOperandFrame fragGasPathPtr ptrDiscipline venomState venomExecSemantics
  compileEnv finite_map pred_set list words

(* Enter the recursively compiled child, retaining the independent source
   and destination provenances.  The concrete state exposes only the six
   compiler-temporary updates, so all ambient fields remain framed. *)
Theorem intcall_array_child_entry_counted:
  !D ctx fn PG G tn s id vb cl bl el len n j dst src a b ds ss dp sp hbb bbb R.
  j < n /\ n < dimword (:256) /\
  (!i. 1 <= i /\ i <= 6 ==> compiler_var_name vb i NOTIN R) /\
  (!i. 1 <= i /\ i <= 4 ==> src <> Var (compiler_var_name vb i) /\
    dst <> Var (compiler_var_name vb i)) /\
  dst <> Var (compiler_var_name vb 5) /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME (n2w j) /\
  eval_operand len s = SOME (n2w n) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  op_prov G src = SOME sp /\ op_prov G dst = SOME dp /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cl /\ s.vs_inst_idx = 0 /\
  lookup_block cl fn.fn_blocks = SOME hbb /\
  hbb.bb_instructions = typed_array_loop_header id vb bl el len /\
  lookup_block bl fn.fn_blocks = SOME bbb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bbb.bb_instructions ==>
  ?u H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
    u = ((update_var (compiler_var_name vb 6) (n2w (b+j*ds))
      (update_var (compiler_var_name vb 5) (n2w (a+j*ss))
        (update_var (compiler_var_name vb 4) (n2w (j*ds))
          (update_var (compiler_var_name vb 3) (n2w (j*ss))
            (jump_to bl (typed_array_loop_header_state vb (n2w j) (n2w n) s))))))
      with vs_inst_idx := 4) /\
    ~u.vs_halted /\ u.vs_current_bb = bl /\ u.vs_inst_idx = 4 /\
    eval_operand (Var (compiler_var_name vb 5)) u = SOME (n2w (a+j*ss)) /\
    eval_operand (Var (compiler_var_name vb 6)) u = SOME (n2w (b+j*ds)) /\
    op_prov H (Var (compiler_var_name vb 5)) = SOME sp /\
    op_prov H (Var (compiler_var_name vb 6)) = SOME dp /\
    op_taint tf (Var (compiler_var_name vb 5)) = {} /\
    op_taint tf (Var (compiler_var_name vb 6)) = {} /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `protected = R UNION {compiler_var_name vb 0} UNION
    {x | src = Var x \/ dst = Var x}` >>
  `compiler_var_name vb 1 NOTIN protected /\ compiler_var_name vb 2 NOTIN protected` by
    (simp[Abbr `protected`] >> metis_tac[compiler_var_name_inj]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hbb` by simp[] >>
  drule_all intcall_typed_array_header_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `j < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ H tf (OK sh)` >>
  `eval_operand src sh = SOME (n2w a) /\ eval_operand dst sh = SOME (n2w b) /\
   eval_operand (Var (compiler_var_name vb 0)) sh = SOME (n2w j)` by
    (`src <> Var (compiler_var_name vb 1) /\ src <> Var (compiler_var_name vb 2) /\
      dst <> Var (compiler_var_name vb 1) /\ dst <> Var (compiler_var_name vb 2)` by
       metis_tac[DECIDE ``1 <= 1 /\ 1 <= 4 /\ 1 <= 2 /\ 2 <= 4``] >>
     simp[Abbr `sh`, typed_array_loop_header_state_def,
      eval_operand_jump_to_eq, eval_operand_update_var_avoids]) >>
  `op_prov H src = SOME sp /\ op_prov H dst = SOME dp /\
   op_taint tf src = {} /\ op_taint tf dst = {} /\
   op_prov H (Var (compiler_var_name vb 0)) = NONE /\
   op_taint tf (Var (compiler_var_name vb 0)) = {}` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[op_prov_def, op_taint_def, Abbr `protected`]) >>
  `~sh.vs_halted /\ sh.vs_inst_idx = 0 /\
   lookup_block sh.vs_current_bb fn.fn_blocks = SOME bbb` by
    simp[Abbr `sh`, jump_to_def, typed_array_loop_header_state_def, update_var_def] >>
  `compiler_var_name vb 3 NOTIN R /\ compiler_var_name vb 4 NOTIN R /\
   compiler_var_name vb 5 NOTIN R /\ compiler_var_name vb 6 NOTIN R /\
   src <> Var (compiler_var_name vb 3) /\ src <> Var (compiler_var_name vb 4) /\
   dst <> Var (compiler_var_name vb 3) /\ dst <> Var (compiler_var_name vb 4)` by
    (qpat_assum `!i. 1 <= i /\ i <= 6 ==> _` (fn th =>
       map_every (fn i => qspec_then i mp_tac th) [`3`, `4`, `5`, `6`]) >>
     qpat_assum `!i. 1 <= i /\ i <= 4 ==> _` (fn th =>
       map_every (fn i => qspec_then i mp_tac th) [`3`, `4`]) >> simp[]) >>
  drule_all intcall_typed_array_addresses_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H'`, `tf'`] >>
  gvs[Abbr `sh`, typed_array_loop_header_state_def, jump_to_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    word_mul_n2w, word_add_n2w, WORD_MULT_COMM] >>
  rpt strip_tac >>
  `!i. 1 <= i /\ i <= 6 ==> compiler_var_name vb i <> x` by
    metis_tac[] >>
  simp[] >> gvs[Abbr `protected`]
QED
