(* Aborting bytes suffix, with the pointer ghost on every edge. *)
Theory rawRevertPtrTail
Ancestors
  wordLoadStorePtr rawRevertPtrBoundary bodyPtrHashBuiltinsKeccakBytesRun
  typedCopyPtr typedCopyLoopHeaderPtr bodyPtrDefs fragGasSeqPtr fragGasPathPtr
  ptrDiscipline ptrSafeRun venomState venomInst venomExecSemantics
  words finite_map pred_set contextCodegenRel codegenRel valueEncodingProps
  exprSimHash list arithmetic exprSimRawRevertCore exprLoweringProps
  emitHelperProps emitHelper compileEnv loweringStateRelDefs ASCIInumbers fragExec exprOperandVar
  bodyPtrHashBuiltinsCases vyperTypeSystem loweringPosts

Theorem raw_revert_bytes_path_ptr:
  !D ctx fn PG G tn s bb il ia ir x l p b base cap n.
  ALL_DISTINCT [x;l;p] /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base:num,cap:num) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\
  op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst il MLOAD [Var x] [l]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst ia ADD [Var x;Lit 32w] [p]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst ir REVERT [Var p;Var l] []) ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn x s 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  `mload b s = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s = OK (update_var l (n2w n) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst il MLOAD [Var x] [l]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `(mk_inst il MLOAD [Var x] [l]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst il MLOAD [Var x] [l]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, hash_mload_ghost] >> strip_tac >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume raw_revert_bytes_path_ptr[add]:
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (qpat_x_assum `!PG. gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `PG` mp_tac) >>
     simp[Abbr `G1`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def]) >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   eval_operand (Var l) s1 = SOME (n2w n) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s1 =
    OK (update_var p (n2w b + 32w) s1)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst ia ADD [Var x;Lit 32w] [p]) s1` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst ia ADD [Var x;Lit 32w] [p])` by
    simp[Abbr `s1`, update_var_def] >>
  `(mk_inst ia ADD [Var x;Lit 32w] [p]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst ia ADD [Var x;Lit 32w] [p]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  qabbrev_tac `s2 = update_var p (n2w b+32w) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = G1 |+ (p,(rootbase,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (p,{})` >>
  suspend "revert"
QED

Resume raw_revert_bytes_path_ptr[revert]:
  `gas_path_ptr_edge D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` by
    (qpat_x_assum `!PG'. gas_path_ptr_edge _ _ _ _ _ G1 _ _ _ _ _ _`
       (qspec_then `PG` mp_tac) >>
     rewrite_tac[GSYM mk_inst_def] >>
     simp[hash_add_ghost, Abbr `G2`, Abbr `tn2`] >>
     simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
          op_prov_def, mk_inst_def]) >>
  `eval_operand (Var p) s2 = SOME (n2w (b+32)) /\
   eval_operand (Var l) s2 = SOME (n2w n) /\
   FLOOKUP G2 p = SOME (rootbase,cap) /\
   op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var l) = {}` by
    gvs[Abbr `s2`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`, ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, word_add_n2w] >>
  `~s2.vs_halted /\ lookup_block s2.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst ir REVERT [Var p;Var l] [])` by
    simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
  `w2n (n2w (b+32):bytes32) + w2n (n2w n:bytes32) <= rootbase+cap /\
   rootbase <= w2n (n2w (b+32):bytes32)` by (simp[] >> decide_tac) >>
  drule_all revert_counted_edge_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2 (Abort Revert_abort t)` by
    (irule (cj 3 gas_path_ptr_rules) >> simp[fragExecTheory.exit_result_def]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 (0+0) G2 tn2 (Abort Revert_abort t)` by
    (irule (cj 2 gas_path_ptr_rules) >> metis_tac[]) >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  `0 = 0+0` by simp[] >>
  metis_tac[cj 2 gas_path_ptr_rules]
QED

Finalise raw_revert_bytes_path_ptr

Theorem raw_revert_tail_path_ptr:
  !D ctx fn PG G tn s data sm u sb b rootbase cap n.
  compile_raw_revert data sm = (u,sb) /\ fn_has_code sm sb fn /\
  (!v. data = Var v ==> not_fresh_at sm v) /\
  (?x. data = Var x /\ FLOOKUP G x = SOME (rootbase,cap)) /\
  eval_operand data s = SOME (n2w b) /\ rootbase <= b /\
  b+32+n <= rootbase+cap /\ b+32 < dimword (:256) /\ n < dimword (:256) /\
  op_taint tn data = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule raw_revert_tail_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sm.cs_current_insts ++ new` >>
  `?bb. lookup_block sm.cs_current_bb fn.fn_blocks = SOME bb /\
    !i. i < LENGTH new ==> get_instruction bb (LENGTH sm.cs_current_insts+i) =
      SOME (EL i new)` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> gvs[same_blocks_def]) >>
  qabbrev_tac `l = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `p = STRING #"%" (toString (sm.cs_next_var+1))` >>
  `ALL_DISTINCT [x;l;p]` by
    (simp[ALL_DISTINCT, Abbr `l`, Abbr `p`, toString_11] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
    SOME (mk_inst sm.cs_next_id MLOAD [Var x] [l])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `new`, Abbr `l`]) >>
  `get_instruction bb (SUC (LENGTH sm.cs_current_insts)) =
    SOME (mk_inst (sm.cs_next_id+1) ADD [Var x;Lit 32w] [p])` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[Abbr `new`, Abbr `p`, ADD1]) >>
  `get_instruction bb (SUC (SUC (LENGTH sm.cs_current_insts))) =
    SOME (mk_inst (sm.cs_next_id+2) REVERT [Var p;Var l] [])` by
    (first_x_assum (qspec_then `2` mp_tac) >> simp[Abbr `new`, Abbr `l`, Abbr `p`, ADD1]) >>
  `b+32+n <= rootbase+cap` by decide_tac >>
  `!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  irule raw_revert_bytes_path_ptr >> metis_tac[]
QED

Theorem raw_revert_post_path_ptr:
  expr_post ctx fn cenv cx e es sa sm s0 ee (BytesV bs) data s /\
  expr_type e = BaseT (BytesT (Dynamic bound)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic bound))) /\
  ptr_val_ok cx (expr_type e) (BytesV bs) data G tn s /\
  lower_value compile_expr cenv (expr_type e) e sa = (data,sm) /\
  compile_raw_revert data sm = (u,sb) /\ fn_has_code sm sb fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (Abort Revert_abort t)
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `!v. data = Var v ==> not_fresh_at sm v` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `b+32+LENGTH bs <= b'+sz'` by decide_tac >>
  `!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  irule (Q.INST [`data` |-> `Var p`, `sm` |-> `sm`] (SPEC_ALL raw_revert_tail_path_ptr)) >>
  simp[eval_operand_def] >>
  qexistsl_tac [`b`, `sz'`, `LENGTH bs`, `p`, `b'`, `sb`, `sm`] >>
  simp[AC ADD_ASSOC ADD_COMM]
QED
