(* Operational boundaries for a single non-fast array-loop iteration. *)
Theory bodyPtrIntCallArraySuccessor
Ancestors
  bodyPtrIntCallArrayLoop bodyPtrIntCallArrayInvariant
  typedArrayLoopCode typedArrayLoopHeader typedArrayLoopCounter abiStaticLoopCode
  abiStaticLoopBody
  ssaOperandFrame fragGasPathPtr ptrDiscipline venomState venomExecSemantics
  compileEnv finite_map pred_set list words arithmetic
  context logValueFramePtr loweringStateRelDefs

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

(* Compose a child ending at its actual cursor with the counter suffix.
   The child frame protects the counter; the suffix need not be in the
   child's entry block. *)
Theorem intcall_array_child_backedge_counted:
  !D ctx fn PG G tn s H tm z id vb counter cl j bb R.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK z) /\
    compiler_var_name vb 0 NOTIN R /\ counter NOTIN R /\
    op_prov H (Var counter) = NONE /\ op_taint tm (Var counter) = {} /\
    eval_operand (Var counter) z = SOME (n2w j) /\
    ~ctx_has_dalloca ctx /\ ~z.vs_halted /\
    lookup_block z.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (typed_array_loop_counter id vb counter cl)
      (DROP z.vs_inst_idx bb.bb_instructions) /\
    (!x. x IN R ==> lookup_var x z = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x) ==>
    ?t K tf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK t) /\
      t = jump_to cl (typed_array_loop_counter_state vb counter (n2w j) z) /\
      ~t.vs_halted /\ t.vs_current_bb = cl /\ t.vs_inst_idx = 0 /\
      eval_operand (Var counter) t = SOME (n2w (j+1)) /\
      op_prov K (Var counter) = NONE /\ op_taint tf (Var counter) = {} /\
      t.vs_memory = z.vs_memory /\ tf.t_mem = tm.t_mem /\
      tf.t_stor = tm.t_stor /\ tf.t_trans = tm.t_trans /\ tf.t_imm = tm.t_imm /\
      (t with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
        vs_current_bb := z.vs_current_bb; vs_inst_idx := z.vs_inst_idx;
        vs_prev_bb := z.vs_prev_bb|>) = z /\
      (!x. x IN R ==> lookup_var x t = lookup_var x s /\
        FLOOKUP K x = FLOOKUP G x /\ FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_typed_array_counter_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H'`, `tf`] >>
  gvs[typed_array_loop_counter_state_def, jump_to_def, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w] >>
  rpt strip_tac >> `counter <> x /\ compiler_var_name vb 0 <> x` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

(* A hypothesis, not an admitted recursive store theorem. *)
val typed_array_child_callback = ``
  !D ctx fn PG ce tenv dt st sc ec vb vs stv dtv a b ss ds sp dp R.
  compile_store_memory_typed ce (Var (compiler_var_name vb 6)) dt
    (Var (compiler_var_name vb 5)) st sc = ((),ec) ==>
  !j s G tn.
    j < LENGTH vs /\ fn_has_code sc ec fn /\
    ~ctx_has_dalloca ctx /\ (!x. x IN R ==> not_fresh_at sc x) /\
    evaluate_type tenv st = SOME stv /\
    evaluate_type tenv dt = SOME dtv /\
    type_memory_bytes ce st = ss /\ type_memory_bytes ce dt = ds /\
    (!i. a+j*ss <= i /\ i < a+(j+1)*ss ==>
      ~(b+j*ds <= i /\ i < b+(j+1)*ds)) /\
    ~s.vs_halted /\
    s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand (Var (compiler_var_name vb 5)) s = SOME (n2w (a+j*ss)) /\
    eval_operand (Var (compiler_var_name vb 6)) s = SOME (n2w (b+j*ds)) /\
    op_prov G (Var (compiler_var_name vb 5)) = SOME sp /\
    op_prov G (Var (compiler_var_name vb 6)) = SOME dp /\
    op_taint tn (Var (compiler_var_name vb 5)) = {} /\
    op_taint tn (Var (compiler_var_name vb 6)) = {} /\
    FST sp <= a+j*ss /\ a+(j+1)*ss <= FST sp + SND sp /\
    FST dp <= b+j*ds /\ b+(j+1)*ds <= FST dp + SND dp /\
    a+(j+1)*ss < dimword (:256) /\ b+(j+1)*ds < dimword (:256) /\
    (?aid. FLOOKUP s.vs_allocas aid = SOME sp) /\
    (?aid. FLOOKUP s.vs_allocas aid = SOME dp) /\
    val_wf stv (EL j vs) /\ val_wf dtv (EL j vs) /\
    val_footprint stv (EL j vs) <= ss /\
    val_footprint dtv (EL j vs) <= ds /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (EL j vs) (a+j*ss) m) ==>
    ?z H tf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      ~z.vs_halted /\ z.vs_current_bb = ec.cs_current_bb /\
      z.vs_inst_idx = LENGTH ec.cs_current_insts /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory dtv (EL j vs) (b+j*ds) m) /\
      (!i. ~(b+j*ds <= i /\ i < b+(j+1)*ds) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      (!i. ~(b+j*ds <= i /\ i < b+(j+1)*ds) /\ i IN tf.t_mem ==>
        i IN tn.t_mem) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      tf.t_imm = tn.t_imm /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
        vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. x IN R ==>
        lookup_var x z = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\
        FLOOKUP tf.t_var x = FLOOKUP tn.t_var x)``;

Theorem intcall_typed_array_header_successor_counted:
  ^typed_array_child_callback ==>
  !D ctx fn PG ce tenv dt st sc ec id vb cl bl el len dst src ds ss
    vs stv dtv a b sp dp R j s G tn hbb bbb ebb.
  compile_store_memory_typed ce (Var (compiler_var_name vb 6)) dt
    (Var (compiler_var_name vb 5)) st sc = ((),ec) /\ fn_has_code sc ec fn /\
  j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cl /\ s.vs_inst_idx = 0 /\
  lookup_block cl fn.fn_blocks = SOME hbb /\
  hbb.bb_instructions = typed_array_loop_header id vb bl el len /\
  lookup_block bl fn.fn_blocks = SOME bbb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bbb.bb_instructions /\
  sc.cs_current_bb = bl /\
  sc.cs_current_insts = typed_array_loop_addresses id vb dst src ds ss /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME ebb /\
  isPREFIX (typed_array_loop_counter ec.cs_next_id ec.cs_next_var
    (compiler_var_name vb 0) cl) (DROP (LENGTH ec.cs_current_insts) ebb.bb_instructions) /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME (n2w j) /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  eval_operand len s = SOME (n2w (LENGTH vs)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  op_prov G src = SOME sp /\ op_prov G dst = SOME dp /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  type_memory_bytes ce st = ss /\ type_memory_bytes ce dt = ds /\
  (!k. k < LENGTH vs ==> val_wf stv (EL k vs) /\ val_footprint stv (EL k vs) <= ss /\
    val_wf dtv (EL k vs) /\ val_footprint dtv (EL k vs) <= ds) /\
  (!i. a <= i /\ i < a + LENGTH vs * ss ==> ~(b <= i /\ i < b + LENGTH vs * ds)) /\
  FST sp <= a /\ a + LENGTH vs * ss <= FST sp + SND sp /\
  FST dp <= b /\ b + LENGTH vs * ds <= FST dp + SND dp /\
  a + LENGTH vs * ss < dimword (:256) /\ b + LENGTH vs * ds < dimword (:256) /\
  (?aid. FLOOKUP s.vs_allocas aid = SOME sp) /\
  (?aid. FLOOKUP s.vs_allocas aid = SOME dp) /\
  (!k. k < j ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory dtv (EL k vs) (b+k*ds) m) /\
  (!k. j <= k /\ k < LENGTH vs ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv (EL k vs) (a+k*ss) m) /\
  (!i. i <= 6 ==> compiler_var_name vb i NOTIN
    (R UNION {x | len = Var x \/ src = Var x \/ dst = Var x})) /\
  (!x. x IN ((R UNION {x | len = Var x \/ src = Var x \/ dst = Var x}) UNION
    {compiler_var_name vb 0}) ==> not_fresh_at sc x) /\
  compiler_var_name ec.cs_next_var 0 NOTIN
    ((R UNION {x | len = Var x \/ src = Var x \/ dst = Var x}) UNION
      {compiler_var_name vb 0}) ==>
  ?t H tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = cl /\ t.vs_inst_idx = 0 /\
    eval_operand (Var (compiler_var_name vb 0)) t = SOME (n2w (j+1)) /\
    op_prov H (Var (compiler_var_name vb 0)) = NONE /\
    op_taint tf (Var (compiler_var_name vb 0)) = {} /\
    eval_operand len t = SOME (n2w (LENGTH vs)) /\
    op_prov H len = NONE /\ op_taint tf len = {} /\
    eval_operand src t = SOME (n2w a) /\ eval_operand dst t = SOME (n2w b) /\
    op_prov H src = SOME sp /\ op_prov H dst = SOME dp /\
    op_taint tf src = {} /\ op_taint tf dst = {} /\
    (!k. k < j+1 ==> !m. mem_agree_outside tf.t_mem t.vs_memory m ==>
      val_in_memory dtv (EL k vs) (b+k*ds) m) /\
    (!k. j+1 <= k /\ k < LENGTH vs ==> !m. mem_agree_outside tf.t_mem t.vs_memory m ==>
      val_in_memory stv (EL k vs) (a+k*ss) m) /\
    (?aid. FLOOKUP t.vs_allocas aid = SOME sp) /\
    (?aid. FLOOKUP t.vs_allocas aid = SOME dp) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. x IN R ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tf.t_var x = FLOOKUP tn.t_var x) /\
    (!i. ~(b <= i /\ i < b + LENGTH vs * ds) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. ~(b <= i /\ i < b + LENGTH vs * ds) /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `Q = R UNION {x | len = Var x \/ src = Var x \/ dst = Var x}` >>
  qabbrev_tac `P = Q UNION {compiler_var_name vb 0}` >>
  `!i. 1 <= i /\ i <= 6 ==> compiler_var_name vb i NOTIN Q` by
    gvs[Abbr `Q`] >>
  `!i. 1 <= i /\ i <= 4 ==> src <> Var (compiler_var_name vb i) /\
    dst <> Var (compiler_var_name vb i)` by
    (gen_tac >> strip_tac >>
     `compiler_var_name vb i NOTIN Q` by (first_x_assum irule >> decide_tac) >>
     gvs[Abbr `Q`] >> metis_tac[]) >>
  `dst <> Var (compiler_var_name vb 5)` by
    (`compiler_var_name vb 5 NOTIN Q` by (first_x_assum irule >> simp[]) >>
     gvs[Abbr `Q`] >> metis_tac[]) >>
  `!i. 1 <= i /\ i <= 6 ==> compiler_var_name vb i NOTIN P` by
    (simp[Abbr `P`] >> metis_tac[compiler_var_name_inj]) >>
  qpat_x_assum `!i. 1 <= i /\ i <= 6 ==> compiler_var_name vb i NOTIN Q` kall_tac >>
  drule_all intcall_array_child_entry_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `u.vs_allocas = s.vs_allocas /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s` by
    gvs[typed_array_loop_header_state_def, jump_to_def, update_var_def] >>
  `(j+1)*ss <= LENGTH vs * ss /\ (j+1)*ds <= LENGTH vs * ds` by
    (conj_tac >> irule LESS_MONO_MULT2 >> decide_tac) >>
  `FST sp <= a+j*ss /\ a+(j+1)*ss <= FST sp + SND sp /\
   FST dp <= b+j*ds /\ b+(j+1)*ds <= FST dp + SND dp /\
   a+(j+1)*ss < dimword (:256) /\ b+(j+1)*ds < dimword (:256)` by decide_tac >>
  `!i. a+j*ss <= i /\ i < a+(j+1)*ss ==>
    ~(b+j*ds <= i /\ i < b+(j+1)*ds)` by
    (rpt strip_tac >>
     `a <= i /\ i < a+LENGTH vs*ss /\ b <= i /\ i < b+LENGTH vs*ds` by decide_tac >>
     metis_tac[]) >>
  `u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts` by
    simp[typed_array_loop_addresses_def] >>
  `(?aid. FLOOKUP u.vs_allocas aid = SOME sp) /\
   (?aid. FLOOKUP u.vs_allocas aid = SOME dp)` by metis_tac[] >>
  `val_wf stv (EL j vs) /\ val_wf dtv (EL j vs) /\
   val_footprint stv (EL j vs) <= ss /\ val_footprint dtv (EL j vs) <= ds` by metis_tac[] >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
    val_in_memory stv (EL j vs) (a+j*ss) m` by simp[] >>
  qpat_x_assum `!D ctx fn PG ce tenv dt st sc ec vb vs stv dtv a b ss ds sp dp R. _` drule >>
  strip_tac >>
  `?z K tm.
      gas_path_ptr D 0 ctx fn PG H tf u 0 K tm (OK z) /\
      ~z.vs_halted /\ z.vs_current_bb = ec.cs_current_bb /\
      z.vs_inst_idx = LENGTH ec.cs_current_insts /\
      (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
        val_in_memory dtv (EL j vs) (b+j*ds) m) /\
      (!i. ~(b+j*ds <= i /\ i < b+(j+1)*ds) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory) /\
      (!i. ~(b+j*ds <= i /\ i < b+(j+1)*ds) /\ i IN tm.t_mem ==> i IN tf.t_mem) /\
      tm.t_stor = tf.t_stor /\ tm.t_trans = tf.t_trans /\ tm.t_imm = tf.t_imm /\
      (z with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. x IN P ==> lookup_var x z = lookup_var x u /\
        FLOOKUP K x = FLOOKUP H x /\ FLOOKUP tm.t_var x = FLOOKUP tf.t_var x)` by
    (qpat_x_assum `!D ctx fn PG tenv vs stv dtv a b ss ds sp dp R j s G tn. _` irule >>
     simp[] >> conj_tac
     >- metis_tac[] >>
     qexistsl_tac [`a`, `stv`, `tenv`] >>
     `a+j*ss < dimword (:256)` by decide_tac >>
     `ss*(j+1) = (j+1)*ss /\ ds*j = j*ds /\ ds*(j+1) = (j+1)*ds` by
       simp_tac std_ss [MULT_COMM] >>
     asm_simp_tac std_ss [] >> conj_tac >- metis_tac[] >>
     qpat_x_assum `!i. a+j*ss <= i /\ i < a+(j+1)*ss ==> _` mp_tac >>
     metis_tac[]) >>
  qpat_x_assum `!D ctx fn PG tenv vs stv dtv a b ss ds sp dp R j s G tn. _` kall_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tf u 0 Gchild tm (OK z)` >>
  `compiler_var_name ec.cs_next_var 0 NOTIN Q /\ compiler_var_name vb 0 NOTIN Q` by
    (gvs[Abbr `P`] >> metis_tac[]) >>
  `op_prov Gchild (Var (compiler_var_name vb 0)) = NONE /\
   op_taint tm (Var (compiler_var_name vb 0)) = {} /\
   eval_operand (Var (compiler_var_name vb 0)) z = SOME (n2w j)` by
    (gvs[op_prov_def, op_taint_def, eval_operand_def, Abbr `P`] >> metis_tac[]) >>
  `!x. x IN Q ==> lookup_var x z = lookup_var x u /\
    FLOOKUP Gchild x = FLOOKUP H x /\ FLOOKUP tm.t_var x = FLOOKUP tf.t_var x` by
    (gvs[Abbr `P`] >> metis_tac[]) >>
  `lookup_block z.vs_current_bb fn.fn_blocks = SOME ebb /\
   isPREFIX (typed_array_loop_counter ec.cs_next_id ec.cs_next_var
     (compiler_var_name vb 0) cl) (DROP z.vs_inst_idx ebb.bb_instructions)` by simp[] >>
  drule_all intcall_array_child_backedge_counted >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `(!k. k < j+1 ==> !m. mem_agree_outside tm.t_mem z.vs_memory m ==>
      val_in_memory dtv (EL k vs) (b+k*ds) m) /\
   (!k. j+1 <= k /\ k < LENGTH vs ==> !m. mem_agree_outside tm.t_mem z.vs_memory m ==>
      val_in_memory stv (EL k vs) (a+k*ss) m)` by
    (irule intcall_array_robust_step >>
     metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\
   (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s` by
    (qpat_x_assum `u = _` kall_tac >> qpat_x_assum `t = _` kall_tac >>
     gvs[venom_state_component_equality]) >>
  `!x. x IN Q ==> lookup_var x t = lookup_var x s /\
    FLOOKUP K' x = FLOOKUP G x /\ FLOOKUP tf'.t_var x = FLOOKUP tn.t_var x` by
    (gvs[Abbr `P`] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 K' tf' (OK t)` by metis_tac[] >>
  qpat_x_assum `t = _` kall_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> x IN Q) ==>
    eval_operand op t = eval_operand op s /\
    op_prov K' op = op_prov G op /\ op_taint tf' op = op_taint tn op` by
    (Cases >> simp[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  `eval_operand len t = SOME (n2w (LENGTH vs)) /\
   op_prov K' len = NONE /\ op_taint tf' len = {} /\
   eval_operand src t = SOME (n2w a) /\ eval_operand dst t = SOME (n2w b) /\
   op_prov K' src = SOME sp /\ op_prov K' dst = SOME dp /\
   op_taint tf' src = {} /\ op_taint tf' dst = {}` by
    (gvs[Abbr `Q`] >> metis_tac[]) >>
  qexistsl_tac [`t`, `K'`, `tf'`] >>
  asm_simp_tac std_ss [] >>
  conj_tac >- metis_tac[MULT_COMM] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (gvs[Abbr `Q`] >> metis_tac[]) >>
  `j+1 <= LENGTH vs` by decide_tac >>
  `(j+1)*ds <= LENGTH vs*ds` by simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `~(b+j*ds <= i /\ i < b+(j+1)*ds)` by decide_tac >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~(b+j*ds <= i /\ i < b+(j+1)*ds)` by decide_tac >>
      metis_tac[]) >>
  gvs[venom_state_component_equality]
QED
