(* The one-child interface below is a typed design quotation, not a
   theorem or an execution assumption registered in HOL.  It is the
   boundary to be consumed by the remaining-count induction. *)
Theory bodyPtrIntCallArrayTraversal
Ancestors
  bodyPtrIntCallArrayLoop bodyPtrIntCallArrayInvariant
  bodyPtrIntCallArraySuccessor bodyPtrIntCallArrayIteration
  typedArrayLoopStructure typedArrayLoopCode abiStaticLoopCode
  context logValueFramePtr loweringStateRelDefs venomState arithmetic

(* All seven parent temporaries predate the recursive child.  In particular
   its counter and derived pointers can be protected by the usual fresh
   write frame; arbitrary names cannot be protected without this premise. *)
Theorem intcall_array_child_parent_not_fresh:
  !cs cl bl el len dst src ds ss i.
    i < 7 ==>
    not_fresh_at (typed_array_loop_start cs cl bl el len dst src ds ss)
      (compiler_var_name cs.cs_next_var i)
Proof
  simp[not_fresh_at_def, typed_array_loop_start_def, compiler_var_name_def] >>
  rpt strip_tac >> gvs[]
QED

(* sc is typed_array_loop_start; ec is the actual recursively compiled
   child's endpoint, which need not be in sc's initial block.  The loop
   join will preserve counter, bound and both base operand variables by
   choosing R to include them.  No prefix or next-index invariant is
   demanded of this callback. *)
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

(* Premise-to-producer audit for the operational join (still provisional):
   - compile equation and sc/ec cursors: compile_copy_sarray_loop_result,
     typed_array_loop_start_def and typed_array_loop_finish_def.  The
     dynamic compiler branch still needs its concrete decomposition.
   - element pointer values/provenances/cleanliness:
     intcall_typed_array_addresses_counted, instantiated with protected
     counter, bound, base operands and the original old-variable set.
   - source robustness: unread family of the header invariant; val_wf and
     footprint bounds are its fixed per-element data.
   - allocation coverage and word bounds: fixed full-span witnesses plus
     j < LENGTH vs.  The caller staging join, not this quotation, must
     supply those full-span witnesses and physical-type compatibility.
   - destination robustness/exterior frame: the smaller-type store IH,
     not a whole-array execution assumption.  That producer is not yet
     proved; this callback is to be discharged in recursive closure.
   - ambient and old-variable outputs: must be included in that smaller
     store IH.  Its exact input frame/freshness premises must be aligned
     before using this draft; arbitrary R is not automatically preserved.
   - next robust families: intcall_array_robust_step, not part of the child
     callback.  Header/address/counter control leave memory unchanged.
   No theorem claiming the callback or the full loop is registered here.
*)

(* Fixed code and physical-layout inputs, independent of the header index. *)
val array_loop_static = ``
  compile_store_memory_typed ce (Var (compiler_var_name vb 6)) dt
    (Var (compiler_var_name vb 5)) st sc = ((),ec) /\ fn_has_code sc ec fn /\
  LENGTH vs < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  lookup_block cl fn.fn_blocks = SOME hbb /\
  hbb.bb_instructions = typed_array_loop_header id vb bl el len /\
  lookup_block bl fn.fn_blocks = SOME bbb /\
  isPREFIX (typed_array_loop_addresses id vb dst src ds ss) bbb.bb_instructions /\
  sc.cs_current_bb = bl /\
  sc.cs_current_insts = typed_array_loop_addresses id vb dst src ds ss /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME ebb /\
  isPREFIX (typed_array_loop_counter ec.cs_next_id ec.cs_next_var
    (compiler_var_name vb 0) cl) (DROP (LENGTH ec.cs_current_insts) ebb.bb_instructions) /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  type_memory_bytes ce st = ss /\ type_memory_bytes ce dt = ds /\
  (!i. i < LENGTH vs ==> val_wf stv (EL i vs) /\ val_footprint stv (EL i vs) <= ss /\
    val_wf dtv (EL i vs) /\ val_footprint dtv (EL i vs) <= ds) /\
  (!i. a <= i /\ i < a + LENGTH vs * ss ==> ~(b <= i /\ i < b + LENGTH vs * ds)) /\
  FST sp <= a /\ a + LENGTH vs * ss <= FST sp + SND sp /\
  FST dp <= b /\ b + LENGTH vs * ds <= FST dp + SND dp /\
  a + LENGTH vs * ss < dimword (:256) /\ b + LENGTH vs * ds < dimword (:256) /\
  (!i. i <= 6 ==> compiler_var_name vb i NOTIN
    (R UNION {x | len = Var x \/ src = Var x \/ dst = Var x})) /\
  (!x. x IN ((R UNION {x | len = Var x \/ src = Var x \/ dst = Var x}) UNION
    {compiler_var_name vb 0}) ==> not_fresh_at sc x) /\
  compiler_var_name ec.cs_next_var 0 NOTIN
    ((R UNION {x | len = Var x \/ src = Var x \/ dst = Var x}) UNION
      {compiler_var_name vb 0})``;

(* The baseline s0/G0/tn0 is fixed while the header state changes. *)
val array_header_invariant = ``\j s G tn.
  ~s.vs_halted /\ s.vs_current_bb = cl /\ s.vs_inst_idx = 0 /\
  eval_operand (Var (compiler_var_name vb 0)) s = SOME (n2w j) /\
  op_prov G (Var (compiler_var_name vb 0)) = NONE /\
  op_taint tn (Var (compiler_var_name vb 0)) = {} /\
  eval_operand len s = SOME (n2w (LENGTH vs)) /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  op_prov G src = SOME sp /\ op_prov G dst = SOME dp /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!i. i < j ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory dtv (EL i vs) (b+i*ds) m) /\
  (!i. j <= i /\ i < LENGTH vs ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv (EL i vs) (a+i*ss) m) /\
  (?aid. FLOOKUP s.vs_allocas aid = SOME sp) /\
  (?aid. FLOOKUP s.vs_allocas aid = SOME dp) /\
  tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
  (!x. x IN R ==> lookup_var x s = lookup_var x s0 /\
    FLOOKUP G x = FLOOKUP G0 x /\ FLOOKUP tn.t_var x = FLOOKUP tn0.t_var x) /\
  (!i. ~(b <= i /\ i < b + LENGTH vs * ds) ==>
    mem_bytes_at i 1 s.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
  (!i. ~(b <= i /\ i < b + LENGTH vs * ds) /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (s with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
    vs_current_bb := s0.vs_current_bb; vs_inst_idx := s0.vs_inst_idx;
    vs_prev_bb := s0.vs_prev_bb|>) = s0``;

Theorem intcall_typed_array_headers_counted:
  ^typed_array_child_callback ==>
  !D ctx fn PG ce tenv dt st sc ec id vb cl bl el len dst src ds ss
    vs stv dtv a b sp dp R hbb bbb ebb s0 G0 tn0 k s G tn.
  ^array_loop_static /\ k <= LENGTH vs /\ (^array_header_invariant) k s G tn ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    (^array_header_invariant) (LENGTH vs) t H tf
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `Inv = ^array_header_invariant` >>
  `Inv k s G tn` by simp[Abbr `Inv`] >>
  `!j u H tf. j <= LENGTH vs /\ Inv j u H tf ==> ~u.vs_halted` by
    simp[Abbr `Inv`] >>
  `!j u H tf. j < LENGTH vs /\ Inv j u H tf ==>
    ?z K tm. gas_path_ptr D 0 ctx fn PG H tf u 0 K tm (OK z) /\ Inv (SUC j) z K tm` by
    (rpt gen_tac >> qunabbrev_tac `Inv` >> BETA_TAC >> strip_tac >>
     `?z K tm. gas_path_ptr D 0 ctx fn PG H tf u 0 K tm (OK z) /\
       (\s0 G0 tn0. ^array_header_invariant) u H tf (j+1) z K tm` by
       (BETA_TAC >> irule intcall_typed_array_header_successor_counted >>
        conj_tac >- first_assum ACCEPT_TAC >>
        simp[] >>
        qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
        simp[] >> rpt (first_assum (irule_at Any) >> simp[]) >>
        qexists_tac `el` >> gvs[]) >>
     qpat_assum `gas_path_ptr D 0 ctx fn PG H tf u 0 _ _ _` (irule_at Any) >>
     qpat_x_assum `(\s0 G0 tn0 j s G tn. _) _ _ _ _ _ _ _`
       (strip_assume_tac o BETA_RULE) >>
     asm_simp_tac std_ss [ADD1] >>
     rpt (first_assum (irule_at Any)) >>
     fs[venom_state_component_equality]) >>
  drule_all intcall_array_header_iteration_counted >>
  simp[Abbr `Inv`]
QED
