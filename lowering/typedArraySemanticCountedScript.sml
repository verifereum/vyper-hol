Theory typedArraySemanticCounted
Ancestors
  typedArrayTraversalCounted typedArrayControlCounted placeMemoryArrayForward
  placeMemoryChildForward placeMemoryCopyEffect allocaHistory fragGasPathMem
  fragGasMode context compileEnv emitHelper emitHelperProps exprLoweringProps
  bodyMemAssignTopCopyPaths fragExecMem instMemFrontier venomExecSemantics
  venomState venomInst freshWrites list rich_list arithmetic

Theorem typed_memory_array_condition_effect_counted:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done) /\
  next.cs_current_bb = (if i < N then blabel else exit) /\
  next.cs_current_insts = [] /\ alloca_history func s ==>
  ?t. typed_copy_effect ctx func old next s t d n /\
      lookup_var counter t = SOME (n2w i) /\ t.vs_memory = s.vs_memory /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >>
  `gas_path_mem ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))` by
    (irule typed_memory_array_condition_path_mem >> simp[eval_operand_def] >>
     metis_tac[]) >>
  qexists `jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)` >>
  reverse conj_tac
  >- (fs[lookup_var_def] >>
      simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
            jump_to_def] >>
      irule alloca_history_jump >> simp[] >> qexists `s` >>
      simp[jump_to_def, update_var_def]) >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[gas_marked_path_def] >> drule gas_path_mem_exec >> simp[]
QED

Theorem array_backedge_path[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >>
  qabbrev_tac `code = [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
                      mk_inst id2 ASSIGN [Var inc] [counter]]` >>
  qabbrev_tac `q = update_var counter (n2w (SUC i))
                    (update_var inc (n2w (SUC i)) s)` >>
  `gas_marked_path T ctx func s 0
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule topcopy_seq_path >>
     simp[Abbr `code`, Abbr `q`, mk_inst_def, is_terminator_def,
       IS_PREFIX_APPEND, run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       exec_pure1_def, eval_operand_def, lookup_var_update_var,
       GSYM wordsTheory.word_add_n2w, ADD1]) >>
  `gas_marked_path T ctx func (q with vs_inst_idx := s.vs_inst_idx + 2) 0
    (OK (jump_to hdr (q with vs_inst_idx := s.vs_inst_idx + 2)))` by
    (irule topcopy_jump_path >> simp[Abbr `q`, update_var_def] >>
     qexists `mk_inst id3 JMP [Label hdr] []` >>
     simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def] >>
     `LENGTH (DROP s.vs_inst_idx bb.bb_instructions) = 3` by
       (pure_asm_rewrite_tac[] >> simp[]) >>
     `s.vs_inst_idx + 2 < LENGTH bb.bb_instructions` by fs[LENGTH_DROP] >>
     `EL 2 (DROP s.vs_inst_idx bb.bb_instructions) =
       mk_inst id3 JMP [Label hdr] []` by simp[] >>
     gvs[EL_DROP, get_instruction_def, mk_inst_def, ADD_COMM]) >>
  gvs[gas_marked_path_def, Abbr `code`] >>
  drule_all gas_path_mem_then >> simp[Abbr `q`]
QED

Theorem typed_memory_array_backedge_effect_counted:
  typed_copy_effect ctx func bst b5 s v d n /\
  gas_path_mem ctx func s 0 (OK v) /\ alloca_history func v /\
  lookup_var counter s = SOME (n2w i) /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==>
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  DROP (LENGTH b5.cs_current_insts) bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  SUC i < dimword (:256) /\
  head.cs_current_bb = hdr /\ head.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >>
  `lookup_var counter v = SOME (n2w i)` by
    metis_tac[typed_copy_effect_lookup] >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `gas_path_mem ctx func v 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (irule array_backedge_path >> simp[] >>
     metis_tac[]) >>
  `gas_path_mem ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (drule_all gas_path_mem_then >> simp[]) >>
  qexists `jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)` >>
  reverse conj_tac
  >- (simp[lookup_var_def, update_var_def, jump_to_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
      irule alloca_history_jump >> simp[] >> qexists `v` >> simp[]) >>
  qpat_x_assum `typed_copy_effect _ _ _ _ _ _ _ _` mp_tac >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_mem_exec]
QED

Theorem typed_memory_array_element_forward_counted:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  (!sty dtyv styv value dop sop a b u dword sword.
    type_widens_to tenv sty dt /\
    evaluate_type tenv dt = SOME dtyv /\ evaluate_type tenv sty = SOME styv /\
    type_memory_bytes cenv dt = type_memory_size dtyv /\
    type_memory_bytes cenv sty = type_memory_size styv /\
    value_has_type dtyv value /\ val_wf dtyv value /\
    value_has_type styv value /\ val_wf styv value /\
    val_in_memory styv value (w2n sword) u.vs_memory /\
    (w2n sword + type_memory_size styv <= w2n dword \/
     w2n dword + type_memory_size dtyv <= w2n sword) /\
    w2n sword + type_memory_size styv < dimword (:256) /\
    w2n dword + type_memory_size dtyv < dimword (:256) /\
    compile_store_memory_typed cenv dop dt sop sty a = ((),b) /\
    (!x. dop = Var x ==> not_fresh_at a x) /\
    (!x. sop = Var x ==> not_fresh_at a x) /\
    eval_operand dop u = SOME dword /\ eval_operand sop u = SOME sword /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\
    w2n sword + type_memory_size styv <= u.vs_alloca_next /\
    w2n dword + type_memory_size dtyv <= u.vs_alloca_next ==>
    ?t. val_in_memory dtyv value (w2n dword) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dword) (type_memory_size dtyv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t) /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >>
  drule_all typed_memory_array_addresses_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   alloca_inv u` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def,
         venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `?t. val_in_memory dtv v (w2n (dw + n2w (i * type_memory_size dtv))) t.vs_memory /\
       typed_copy_effect ctx func b4 b5 u t
         (w2n (dw + n2w (i * type_memory_size dtv))) (type_memory_size dtv) /\
       gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t` by
    (qpat_x_assum `!sty dtyv styv value dop sop a b u dword sword. _` irule >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac) >>
  `typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
    (simp[typed_copy_effect_def] >>
     conj_tac >- (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  (qexists `t` >> gvs[] >> conj_tac
   >- (irule typed_copy_effect_then >>
       qexistsl [`b4`, `b4`, `u`] >> simp[] >> metis_tac[not_fresh_at_mono]) >>
   drule_all gas_path_mem_then >> simp[])
QED

Theorem typed_memory_array_round_effect_counted:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ alloca_history func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst h1 LT [Var counter; length] [lt];
     mk_inst h2 ISZERO [Var lt] [done];
     mk_inst h3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i < N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done /\
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  bst.cs_current_bb = blabel /\ bst.cs_current_insts = [] /\
  head.cs_current_bb = s.vs_current_bb /\ head.cs_current_insts = [] /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME ebb /\
  DROP (LENGTH b5.cs_current_insts) ebb.bb_instructions =
    [mk_inst e1 ADD [Var counter; Lit 1w] [inc];
     mk_inst e2 ASSIGN [Var inc] [counter];
     mk_inst e3 JMP [Label head.cs_current_bb] []] /\
  (!a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory /\
       alloca_history func a ==>
       ?v. val_in_memory dtv value d v.vs_memory /\
           typed_copy_effect ctx func bst b5 a v d n /\
           gas_path_mem ctx func a 0 (OK v) /\ alloca_history func v) ==>
  ?t. val_in_memory dtv value d t.vs_memory /\
      typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i)) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >>
  `?a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory /\
       gas_path_mem ctx func s 0 (OK a) /\ alloca_history func a` by
    (irule typed_memory_array_condition_effect_counted >>
     qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  qpat_x_assum `!a. _ ==> ?v. _` drule_all >> strip_tac >>
  `?t. typed_copy_effect ctx func old head a t d n /\
       lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory /\
       gas_path_mem ctx func a 0 (OK t) /\ alloca_history func t` by
    (irule typed_memory_array_backedge_effect_counted >>
     qpat_assum `typed_copy_effect ctx func bst b5 a v d n` (irule_at Any) >>
     qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  qexists `t` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >> qexistsl [`old`, `bst`, `a`] >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED
