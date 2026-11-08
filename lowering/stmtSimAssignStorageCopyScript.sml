(* Assignments to ABI-static storage or transient aggregates copy every
   encoded slot from memory. Source-static encoding coverage justifies
   that dense copy under the capacity-wide storage agreement mask.
   stmtSimAssignStorageSparse has the ABI-dynamic case. *)

Theory stmtSimAssignStorageCopy
Ancestors
  abiTypeBoundProps vyperABI vyperStorageCoverage
  valueEncodingProps exprSimTopLevelProps gasOutcome gasSummary gasContext
  stmtSimProps stmtSimForced
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec  exprSimLeaves exprSimOps  stmtSimAssign stmtSimAssignMem
  stmtSimAssignStorage exprSimHash exprOperandVar stmtSimDecl vyperExprNoControl
  stmtSimStoreCopy storageCopyLive accountsRelProps
  fragGasMode fragGasSeq fragGasPath venomExecProofs
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding stmtLoweringMono
  vyperContext vyperAST vyperInterpreter vyperState vyperStorage vyperStorageBackend vyperValue
  vyperTyping vyperStorageLayoutSafety vyperStorageFrame
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* Counted source-address/load prefix.  Intermediate states stay opaque. *)
Theorem storage_copy_source_prefix_path[local]:
  !ctx func bb s src b i cv mv sv vv id.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MUL [Var cv; Lit 32w] [mv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [src; Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    eval_operand src s = SOME b /\
    (!x. src = Var x ==> ~MEM x [mv;sv;vv]) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv] ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var vv) t = SOME (mload (w2n (b+n2w i*32w)) s) /\
      (!x. ~MEM x [mv;sv;vv] ==> lookup_var x t = lookup_var x s) /\
      store_copy_normalize s t = store_copy_normalize s s /\
      t.vs_memory = s.vs_memory /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+3 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u1 = update_var mv (n2w i*32w) s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s = OK u1` by
    (simp[Abbr `u1`] >> irule step_MUL >> simp[eval_operand_lit]) >>
  `gas_path_edge ctx func s 0 (OK s1)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id MUL [Var cv; Lit 32w] [mv]`, `u` |-> `u1`]
       tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s1`]) >>
  `gas_marked_path F ctx func s 0 (OK s1)` by
    (simp[gas_marked_path_def] >>
     drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s1`, Abbr `u1`, update_var_def]) >>
  `eval_operand src s1 = SOME b /\
   eval_operand (Var mv) s1 = SOME (n2w i*32w) /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = SUC s.vs_inst_idx /\ ~s1.vs_halted` by
    (Cases_on `src` >>
     gvs[Abbr `s1`, Abbr `u1`, eval_operand_def, lookup_var_update_var,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `u2 = update_var sv (b+n2w i*32w) s1` >>
  qabbrev_tac `s2 = u2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) s1 = OK u2` by
    (simp[Abbr `u2`] >> irule step_ADD >> simp[]) >>
  `gas_path_edge ctx func s1 0 (OK s2)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst (id+1) ADD [src; Var mv] [sv]`,
                    `u` |-> `u2`, `s` |-> `s1`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s2`]) >>
  `gas_marked_path F ctx func s1 0 (OK s2)` by
    (simp[gas_marked_path_def] >>
     drule_at (Pat `gas_path_edge _ _ s1 _ _`) (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s2`, Abbr `u2`, update_var_def]) >>
  `eval_operand (Var sv) s2 = SOME (b+n2w i*32w) /\
   s2.vs_memory = s.vs_memory /\
   s2.vs_current_bb = s.vs_current_bb /\
   s2.vs_inst_idx = s.vs_inst_idx+2 /\ ~s2.vs_halted` by
    simp[Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`,
         update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qabbrev_tac `u3 = update_var vv (mload (w2n (b+n2w i*32w)) s) s2` >>
  qabbrev_tac `s3 = u3 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv]) s2 = OK u3` by
    simp[Abbr `u3`, stepInstBaseLib.simp_opcode_clause ``MLOAD``,
         mk_inst_def, exec_read1_def, mload_def] >>
  `gas_path_edge ctx func s2 0 (OK s3)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst (id+2) MLOAD [Var sv] [vv]`,
                    `u` |-> `u3`, `s` |-> `s2`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s3`]) >>
  `gas_marked_path F ctx func s2 0 (OK s3)` by
    (simp[gas_marked_path_def] >>
     drule_at (Pat `gas_path_edge _ _ s2 _ _`) (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s3`, Abbr `u3`, update_var_def]) >>
  `gas_marked_path F ctx func s (0 + 0) (OK s2)` by
    (irule gas_marked_path_then >> qexists_tac `s1` >> fs[]) >>
  `gas_marked_path F ctx func s (0 + 0 + 0) (OK s3)` by
    (irule gas_marked_path_then >> qexists_tac `s2` >> fs[]) >>
  `gas_marked_path F ctx func s 0 (OK s3)` by fs[] >>
  qexists_tac `s3` >> simp[] >>
  gvs[Abbr `s3`, Abbr `u3`, Abbr `s2`, Abbr `u2`, Abbr `s1`, Abbr `u1`,
      eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      ALL_DISTINCT, store_copy_normalize_def]
QED

(* The store/counter half of the counted body, independent of the source buffer. *)
Theorem storage_copy_store_increment_path[local]:
  !ctx func bb s dst k i w loc cv vv dv nv id.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [dst; Var cv] [dv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
        [Var dv; Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ADD [Var cv; Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ASSIGN [Var nv] [cv]) /\
    eval_operand dst s = SOME k /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    eval_operand (Var vv) s = SOME w /\ ~s.vs_call_ctx.cc_static /\
    ALL_DISTINCT [cv;vv;dv;nv] ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      (!x. ~MEM x [dv;nv;cv] ==> lookup_var x t = lookup_var x s) /\
      store_copy_normalize s t = store_copy_normalize s
        ((if loc = LocStorage then sstore else tstore) (k+n2w i) w s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+4 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u1 = update_var dv (k+n2w i) s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst id ADD [dst; Var cv] [dv]) s = OK u1` by
    (simp[Abbr `u1`] >> irule step_ADD >> simp[]) >>
  `gas_path_edge ctx func s 0 (OK s1)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id ADD [dst; Var cv] [dv]`,
                    `u` |-> `u1`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s1`]) >>
  `gas_marked_path F ctx func s 0 (OK s1)` by
    (simp[gas_marked_path_def] >> drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s1`, Abbr `u1`, update_var_def]) >>
  `eval_operand (Var dv) s1 = SOME (k+n2w i) /\
   eval_operand (Var vv) s1 = SOME w /\
   eval_operand (Var cv) s1 = SOME (n2w i) /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = SUC s.vs_inst_idx /\ ~s1.vs_halted /\
   ~s1.vs_call_ctx.cc_static` by
    gvs[Abbr `s1`, Abbr `u1`, eval_operand_def, update_var_def,
        lookup_var_def, FLOOKUP_UPDATE, ALL_DISTINCT] >>
  qabbrev_tac `u2 = (if loc = LocStorage then sstore else tstore) (k+n2w i) w s1` >>
  qabbrev_tac `s2 = u2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `step_inst_base (mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
      [Var dv; Var vv] []) s1 = OK u2` by
    (Cases_on `loc = LocStorage` >>
     simp[Abbr `u2`, stepInstBaseLib.simp_opcode_clause ``SSTORE``,
          stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def, exec_write2_def]) >>
  `gas_path_edge ctx func s1 0 (OK s2)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst (id+1)
       (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] []`,
       `u` |-> `u2`, `s` |-> `s1`] tuple_straight_line_edge) >>
     Cases_on `loc = LocStorage` >>
     simp[mk_inst_def, is_terminator_def, Abbr `s2`]) >>
  `gas_marked_path F ctx func s1 0 (OK s2)` by
    (simp[gas_marked_path_def] >>
     drule_at (Pat `gas_path_edge _ _ s1 _ _`) (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     Cases_on `loc = LocStorage` >>
     gvs[Abbr `s2`, Abbr `u2`, sstore_def, tstore_def]) >>
  `eval_operand (Var cv) s2 = SOME (n2w i) /\
   s2.vs_current_bb = s.vs_current_bb /\
   s2.vs_inst_idx = s.vs_inst_idx+2 /\ ~s2.vs_halted` by
    (Cases_on `loc = LocStorage` >>
     gvs[Abbr `s2`, Abbr `u2`, sstore_def, tstore_def, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `u3 = update_var nv (n2w i+1w) s2` >>
  qabbrev_tac `s3 = u3 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `step_inst_base (mk_inst (id+2) ADD [Var cv; Lit 1w] [nv]) s2 = OK u3` by
    (simp[Abbr `u3`] >> irule step_ADD >> simp[eval_operand_lit]) >>
  `gas_path_edge ctx func s2 0 (OK s3)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst (id+2) ADD [Var cv; Lit 1w] [nv]`,
                    `u` |-> `u3`, `s` |-> `s2`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s3`]) >>
  `gas_marked_path F ctx func s2 0 (OK s3)` by
    (simp[gas_marked_path_def] >>
     drule_at (Pat `gas_path_edge _ _ s2 _ _`) (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s3`, Abbr `u3`, update_var_def]) >>
  `eval_operand (Var nv) s3 = SOME (n2w i+1w) /\
   s3.vs_current_bb = s.vs_current_bb /\
   s3.vs_inst_idx = s.vs_inst_idx+3 /\ ~s3.vs_halted` by
    simp[Abbr `s3`, Abbr `u3`, update_var_def,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qabbrev_tac `u4 = update_var cv (n2w i+1w) s3` >>
  qabbrev_tac `s4 = u4 with vs_inst_idx := SUC s3.vs_inst_idx` >>
  `step_inst_base (mk_inst (id+3) ASSIGN [Var nv] [cv]) s3 = OK u4` by
    simp[Abbr `u4`, stepInstBaseLib.simp_opcode_clause ``ASSIGN``, mk_inst_def] >>
  `gas_path_edge ctx func s3 0 (OK s4)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst (id+3) ASSIGN [Var nv] [cv]`,
                    `u` |-> `u4`, `s` |-> `s3`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `s4`]) >>
  `gas_marked_path F ctx func s3 0 (OK s4)` by
    (simp[gas_marked_path_def] >>
     drule_at (Pat `gas_path_edge _ _ s3 _ _`) (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     gvs[Abbr `s4`, Abbr `u4`, update_var_def]) >>
  `gas_marked_path F ctx func s 0 (OK s4)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `s1` >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `s2` >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `s3` >> simp[]) >>
  qexists_tac `s4` >> simp[] >> Cases_on `loc = LocStorage` >>
  gvs[Abbr `s4`, Abbr `u4`, Abbr `s3`, Abbr `u3`, Abbr `s2`, Abbr `u2`,
      Abbr `s1`, Abbr `u1`, eval_operand_def, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, sstore_def, tstore_def, store_copy_normalize_def,
      arithmeticTheory.ADD1, wordsTheory.word_add_n2w]
QED

(* A typed source value always has a successful storage write. *)
Theorem typed_storage_copy_write:
  !cx tr slot tvt v es.
    value_has_type tvt v /\ ~cx.txn.is_static ==>
    ?writes.
      encode_value tvt v = SOME writes /\
      write_storage_slot cx tr slot tvt v es =
        (INL (), set_storage cx es tr
          (apply_writes slot writes (get_storage cx es tr)))
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (encode_value tvt v)` by
    metis_tac[value_has_type_equiv] >>
  Cases_on `encode_value tvt v` >> gvs[write_storage_slot_eq]
QED

(* The empty shortcut does not evaluate the RHS in generated code. *)
Theorem assign_storage_empty_code[local]:
  !cenv lctx ty nsid e sa sf c tr slot.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    c = cenv /\
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; Lit 0w] sa =
      ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_store_at_loc_def]
QED

(* Expose the RHS prefix independently of the later assignment dispatch.
   In particular this interface remains valid when RHS evaluation fails. *)
Theorem assign_storage_copy_code_parts:
  !cenv lctx ty nsid e sa sf c tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = expr_type e ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Lit slot)
        (if tr then LocTransient else LocStorage) op (is_word_type vtyp)
        (vv_location vv) vtyp (lowered_value_type cenv e)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >>
  simp[lower_value_def, comp_bind_def]
QED

(* Once source layout compatibility is known, only the size dispatch
   remains. No dynamic-array path or normalization can be selected. *)
Theorem assign_storage_copy_suffix:
  !cenv dst src tr loc typ src_ty mem_size.
    ~is_word_type typ /\ ~is_abi_dynamic cenv.ce_struct_fields typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = mem_size ==>
    compile_assign_value cenv dst
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty mem_size =
    (if mem_size DIV 32 = 1 then
       do loaded <- emit_op MLOAD [src];
          emit_void (if tr then TSTORE else SSTORE) [dst; loaded]
       od
     else
       do (if tr then compile_memory_to_transient src dst (mem_size DIV 32)
           else compile_memory_to_storage src dst (mem_size DIV 32));
          return ()
       od)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def] >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def]
QED

(* A value's footprint is its type's memory size unless it is a bytestring. *)
Theorem topcopy_val_footprint:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

(* The word copy loop ends in its exit block, which is open. *)
Theorem word_copy_loop_op_open:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop_op src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_op_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def, block_is_terminated_def]
QED

Theorem assign_storage_copy_suffix_open:
  !cenv dst src tr loc typ src_ty mem_size sa sb.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F loc typ src_ty mem_size sa = ((),sb) /\
    ~is_word_type typ /\ ~is_abi_dynamic cenv.ce_struct_fields typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = mem_size ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC[assign_storage_copy_suffix] >> simp[] >>
  Cases_on `mem_size DIV 32 = 1`
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  irule word_copy_loop_op_open >> Cases_on `tr` >>
  fs[compile_word_copy_loop_def] >> metis_tac[]
QED

Theorem storage_copy_dyn_live_word[local]:
  !st base cap len i b.
    w2n (lookup_storage (n2w base) st) = len /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead st base cap (base + i) b ==>
    32 * i < 32 + len
Proof
  rpt gen_tac >> strip_tac >>
  fs[dyn_bytes_dead_def] >> decide_tac
QED

Theorem storage_copy_word_address:
  !w:bytes32 i len.
    w2n w + len < dimword (:256) /\ 32 * i < len ==>
    w2n (w + n2w i * 32w) = w2n w + 32 * i
Proof
  Cases >> rpt gen_tac >> strip_tac >>
  gvs[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w,
      wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `n + i * 32 < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD]
QED

Theorem storage_copy_length_type[local]:
  !typ.
    has_length_word typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
    (?n. typ = BaseT (BytesT (Dynamic n))) \/
    (?n. typ = BaseT (StringT n))
Proof
  gen_tac >> strip_tac >> Cases_on `typ` >>
  gvs[has_length_word_def, is_bytestring_type_def]
  >- (rename1 `is_bytestring_type (BaseT bt)` >>
      Cases_on `bt` >> gvs[is_bytestring_type_def] >>
      rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
      Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  rename1 `has_length_word (ArrayT elem bd)` >>
  Cases_on `bd` >> gvs[has_length_word_def, is_bytestring_type_def]
QED

(* The repaired Empty branch evaluates only its type, not any operands. *)
Theorem storage_copy_empty_eval[local]:
  !cx ann typ args tvt es.
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    (do result <- eval_expr cx (TypeBuiltin ann Empty typ args);
        read_result cx result od) es =
    (if args = [] then (INL (default_value tvt), es)
     else (INR (Error (TypeError "TypeBuiltin args")), es))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `args` >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_sum_def, evaluate_type_builtin_def, read_result_def] >>
  simp[evaluate_def, bind_def, return_def, read_result_def]
QED

Theorem storage_copy_empty_rhs[local]:
  !cx e typ tvt es r es1.
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    expr_type e = typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    (!v st. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,st) ==> value_has_type tvt v) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r,es1) ==>
    es1 = es /\
    (!tail. (do result <- eval_expr cx e; read_result cx result od)
       (es with gas_obs := tail) = (r, es with gas_obs := tail)) /\
    ((?v. r = INL v /\ encode_value tvt v = SOME [(0,0w)]) \/
     (?msg. r = INR (Error (TypeError msg))))
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. typ = BaseT (BytesT (Dynamic n))) \/
   (?n. typ = BaseT (StringT n))` by
    (irule storage_copy_length_type >> metis_tac[]) >>
  Cases_on `e` >>
  qpat_x_assum `is_empty_value_expr _` mp_tac >>
  simp[is_empty_value_expr_def] >> strip_tac
  >>~- ([`Literal t lit`],
      Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
      rename1 `BytesL bs` >> Cases_on `bs` >>
      gvs[is_empty_value_expr_def, expr_type_def, evaluate_type_def, AllCaseEqs(),
          evaluate_def, bind_def, return_def, read_result_def,
          vyperValueOperationTheory.evaluate_literal_def, encode_value_def, encode_dyn_bytes_slots_def,
          value_has_type_def, bytes_to_slots_def, bytes_to_slots_aux_def])
  >>~- ([`TypeBuiltin ann tb t args`],
      Cases_on `tb` >>
      qpat_x_assum `is_empty_value_expr _` mp_tac >>
      pure_rewrite_tac[is_empty_value_expr_def] >>
      qpat_x_assum `typ = _` SUBST_ALL_TAC >>
      qpat_x_assum `!ann' t' args'. _` mp_tac >>
      simp[] >> strip_tac >> gvs[expr_type_def] >>
      qmatch_asmsub_abbrev_tac `TypeBuiltin at Empty tt args` >>
      drule storage_copy_empty_eval >>
      disch_then (qspecl_then [`at`, `args`] assume_tac) >>
      Cases_on `args` >> unabbrev_all_tac >>
      simp[storage_copy_empty_eval] >>
      gvs[evaluate_type_def, AllCaseEqs(), default_value_def,
          encode_value_def, encode_dyn_bytes_slots_def, bytes_to_slots_def,
          bytes_to_slots_aux_def]) >>
  rename1 `Builtin t b args` >> Cases_on `b` >>
  fs[is_empty_value_expr_def] >>
  rename1 `MakeArray ot bd` >> Cases_on `ot` >>
  fs[is_empty_value_expr_def] >>
  rename1 `MakeArray (SOME elem_ty) bd` >> Cases_on `args` >>
  gvs[is_empty_value_expr_def, expr_type_def] >>
  gvs[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
      assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  gvs[evaluate_def, bind_def, return_def, get_accounts_def,
      lift_sum_def, evaluate_builtin_def, read_result_def,
      evaluate_type_def, AllCaseEqs(), value_has_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) elem_ty` >>
  gvs[return_def, raise_def, value_has_type_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, builtin_args_length_ok_def,
      get_accounts_def, read_result_def]
QED

Theorem storage_copy_length_head[local]:
  !base tv v len tail st.
    encode_value tv v = SOME ((0,n2w len)::tail) /\
    value_has_type tv v /\
    (!off w. MEM (off,w) tail ==> 0 < off) /\
    base + type_slot_size tv <= dimword (:256) /\
    len < dimword (:256) /\ base < dimword (:256) ==>
    w2n (lookup_storage (n2w base)
      (apply_writes (n2w base) ((0,n2w len)::tail) st)) = len
Proof
  rpt gen_tac >> strip_tac >> rename1 `kk + type_slot_size tv <= _` >>
  `!off. MEM off (MAP FST tail) ==> off < type_slot_size tv` by
    (drule (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     simp[] >> metis_tac[]) >>
  simp[Once apply_writes_def, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >>
  `lookup_storage (n2w kk)
      (apply_writes (n2w kk) tail
        (update_storage (n2w kk) (n2w len) st)) =
   lookup_storage (n2w kk) (update_storage (n2w kk) (n2w len) st)` by
    (mp_tac (Q.SPECL [`tail`, `kk`,
       `update_storage (n2w kk) (n2w len) st`, `0`]
       vyperEncodeDecodeTheory.apply_writes_lookup_miss_num) >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     `0 < off` by (fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
     `kk + off < dimword (:256)` by (res_tac >> decide_tac) >>
     gvs[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem storage_copy_dyn_head[local]:
  !tv v cap bs writes k st.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
    w2n (lookup_storage (n2w k) (apply_writes (n2w k) writes st)) = LENGTH bs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[encode_dyn_bytes_slots_def, AllCaseEqs()] >>
  irule storage_copy_length_head >>
  conj_tac
  >- (simp[indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[]) >>
  simp[] >> qexistsl_tac [`tv`, `v`] >> simp[]
QED

Theorem storage_copy_dyn_footprint[local]:
  !tv v cap bs writes k st i b.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead (apply_writes (n2w k) writes st) k cap (k+i) b ==>
    32*i < 32 + LENGTH bs
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (lookup_storage (n2w k) (apply_writes (n2w k) writes st)) = LENGTH bs` by
    (irule storage_copy_dyn_head >> simp[] >>
     qexistsl_tac [`cap`, `tv`, `v`] >> gvs[]) >>
  irule storage_copy_dyn_live_word >> metis_tac[]
QED

Theorem storage_copy_live_footprint[local]:
  !tv v writes k st i b.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b ==>
    32*i < val_footprint tv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (gvs[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  Cases_on `v` >> fs[val_footprint_def] >>
  Cases_on `tv` >> fs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> fs[]
  >- (`encode_value (BaseTV (StringT n)) (StringV s) =
         encode_dyn_bytes_slots n (MAP (n2w o ORD) s)` by simp[NoAsms, encode_value_def] >>
      `LENGTH (MAP (n2w o ORD) s : word8 list) < dimword (:256)` by
        (gvs[value_has_type_def, well_formed_type_value_def] >> decide_tac) >>
      drule storage_copy_dyn_footprint >>
      simp[dead_bytes_def, type_slot_size_def] >> disch_then irule >>
      gvs[encode_value_def, type_slot_size_def, dead_bytes_def] >>
      qexistsl_tac [`b`, `k`, `st`] >> simp[] >> decide_tac) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> fs[] >>
  rename1 `BytesV bs` >>
  `encode_value (BaseTV (BytesT (Dynamic n))) (BytesV bs) =
     encode_dyn_bytes_slots n bs` by simp[NoAsms, encode_value_def] >>
  `LENGTH bs < dimword (:256)` by
    (gvs[value_has_type_def, well_formed_type_value_def] >> decide_tac) >>
  drule storage_copy_dyn_footprint >>
  simp[dead_bytes_def, type_slot_size_def] >> disch_then irule >>
  gvs[encode_value_def, type_slot_size_def, dead_bytes_def] >>
  qexistsl_tac [`b`, `k`, `st`] >> simp[] >> decide_tac
QED

Theorem storage_copy_live_memory_word[local]:
  !tv v writes k st i b (w:bytes32) s.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b /\
    w2n w + val_footprint tv v < dimword (:256) ==>
    mload (w2n (w + n2w i * 32w)) s =
      mem_word_at (w2n w + 32*i) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `32*i < val_footprint tv v` by (drule_all storage_copy_live_footprint >> simp[]) >>
  drule_all storage_copy_word_address >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem storage_copy_capacity_bound[local]:
  !n. n < dimword (:256) ==> 1 + word_size n < dimword (:256)
Proof
  rpt strip_tac >> Cases_on `n < 2`
  >- (`n = 0 \/ n = 1` by decide_tac >>
      gvs[vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >> EVAL_TAC) >>
  `0 < n` by decide_tac >>
  drule vyperArithTheory.word_size_le >> strip_tac >>
  `word_size n < n` by
    (spose_not_then assume_tac >>
     drule_all vyperArithTheory.word_size_not_lt_self >> decide_tac) >>
  decide_tac
QED

Theorem storage_copy_count_bound[local]:
  !tv v.
    well_formed_type_value tv /\ val_footprint tv v < dimword (:256) ==>
    type_slot_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (gvs[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  Cases_on `v` >> fs[val_footprint_def] >>
  Cases_on `tv` >> fs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> fs[]
  >- (fs[well_formed_type_value_def, type_slot_size_def] >>
      qspec_then `n` mp_tac storage_copy_capacity_bound >> simp[]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> fs[] >>
  fs[well_formed_type_value_def, type_slot_size_def] >>
  qspec_then `n` mp_tac storage_copy_capacity_bound >> simp[]
QED

Theorem storage_copy_post_words[local]:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv w writes k st.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) ==>
    type_slot_size tv < dimword (:256) /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b) ==>
         mload (w2n (w + n2w i * 32w)) s =
           mem_word_at (w2n w + 32*i) s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_post_footprint_bound >> strip_tac >>
  `well_formed_type_value tv` by
    (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
  conj_tac
  >- (irule storage_copy_count_bound >> simp[] >> qexists_tac `v` >> decide_tac) >>
  rpt strip_tac >> irule storage_copy_live_memory_word >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists_tac `v` >> simp[]
QED

Theorem storage_copy_backend_fold:
  !is k ws s tr.
    FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is =
    if tr then
      s with vs_transient :=
        (s.vs_call_ctx.cc_address =+
          FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
            (contract_transient s) is) s.vs_transient
    else
      s with vs_accounts :=
        (s.vs_call_ctx.cc_address =+
          (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
            FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
              (contract_storage s) is)) s.vs_accounts
Proof
  Induct >> rpt gen_tac >> Cases_on `tr` >>
  simp[FOLDL, sstore_def, tstore_def, contract_storage_def,
       contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
QED

(* The copy prefix writes storage only: the call context stays sbase's. *)
Theorem store_copy_prefix_call_ctx[local]:
  !i. (store_copy_prefix loc b k sbase i).vs_call_ctx = sbase.vs_call_ctx
Proof
  Induct >- simp[store_copy_prefix_def, COUNT_LIST_def] >>
  `store_copy_prefix loc b k sbase (SUC i) =
   (if loc = LocStorage then sstore else tstore) (k + n2w i)
     (mload (w2n (b + n2w i * 32w)) sbase) (store_copy_prefix loc b k sbase i)` by
    simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC] >>
  pop_assum SUBST1_TAC >>
  Cases_on `loc = LocStorage` >> fs[sstore_def, tstore_def]
QED

Theorem storage_copy_body_path[local]:
  !ctx func bb sa loc b k sbase i s src dst cv mv sv vv dv nv id.
    store_copy_frame sa loc b k sbase i s /\ ~sbase.vs_call_ctx.cc_static /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var cv;Lit 32w] [mv]) /\
    get_instruction bb (s.vs_inst_idx+1) = SOME (mk_inst (id+1) ADD [src;Var mv] [sv]) /\
    get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MLOAD [Var sv] [vv]) /\
    get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [dst;Var cv] [dv]) /\
    get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4)
      (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] []) /\
    get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
    get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv]) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+7 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_memory = sbase.vs_memory /\ s.vs_labels = sbase.vs_labels` by
    (qpat_assum `store_copy_frame _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [store_copy_frame_def]) >>
     strip_tac >>
     `store_copy_prefix loc b k sbase i =
      FOLDL (\t j. (if ~(loc = LocStorage) then tstore else sstore)
        (k+n2w j) (mload (w2n (b+n2w j*32w)) sbase) t) sbase (COUNT_LIST i)` by
       (Cases_on `loc = LocStorage` >> simp[store_copy_prefix_def]) >>
     gvs[storage_copy_backend_fold] >>
     qpat_x_assum `store_copy_normalize _ _ = _`
       (fn th => mp_tac (Q.AP_TERM `\t. (t.vs_memory,t.vs_labels)` th)) >>
     Cases_on `loc = LocStorage` >> simp[store_copy_normalize_def]) >>
  `eval_operand src s = SOME b /\ eval_operand dst s = SOME k` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[store_copy_frame_def, eval_operand_def] >> metis_tac[]) >>
  `(!x. src = Var x ==> ~MEM x [mv;sv;vv]) /\
   ALL_DISTINCT [cv;mv;sv;vv]` by (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  drule_all (REWRITE_RULE [arithmeticTheory.ADD1] storage_copy_source_prefix_path) >>
  disch_then (qspec_then `ctx` (qx_choose_then `sm` strip_assume_tac)) >>
  `sm.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s sm = _`
       (fn th => assume_tac th >> mp_tac (AP_TERM ``\t. t.vs_labels``
         (REWRITE_RULE [store_copy_normalize_def] th))) >> simp[]) >>
  `sm.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `store_copy_normalize s sm = _`
       (mp_tac o AP_TERM ``\t. t.vs_call_ctx``) >>
     simp[NoAsms, store_copy_normalize_def]) >>
  `s.vs_call_ctx = sbase.vs_call_ctx` by
    (qpat_assum `store_copy_frame _ _ _ _ _ _ _`
       (mp_tac o AP_TERM ``\t. t.vs_call_ctx`` o cj 2 o
        REWRITE_RULE [store_copy_frame_def]) >>
     simp[NoAsms, store_copy_normalize_def, store_copy_prefix_call_ctx]) >>
  `~sm.vs_call_ctx.cc_static` by fs[] >>
  `eval_operand dst sm = SOME k /\ ALL_DISTINCT [cv;vv;dv;nv]` by
    (Cases_on `dst` >> gvs[eval_operand_def, ALL_DISTINCT] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `sm`, `id` |-> `id+3`,
                  `w` |-> `mload (w2n ((b:bytes32)+n2w i*32w)) s`]
    (SPEC_ALL storage_copy_store_increment_path)) >>
  simp[arithmeticTheory.ADD1, arithmeticTheory.ADD_ASSOC] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `sm` >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  rpt (qpat_x_assum `get_instruction _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `gas_marked_path _ _ _ _ _ _` kall_tac) >>
  `store_copy_normalize sbase sm = store_copy_normalize sbase s` by
    (qpat_assum `store_copy_normalize s sm = _`
       (mp_tac o AP_TERM ``store_copy_normalize sbase`` o
        REWRITE_RULE [store_copy_normalize_def]) >>
     simp[store_copy_normalize_def]) >>
  `store_copy_normalize sbase t = store_copy_normalize sbase
      ((if loc = LocStorage then sstore else tstore) (k+n2w i)
        (mload (w2n (b+n2w i*32w)) s) sm)` by
    (qpat_assum `store_copy_normalize sm t = _`
       (mp_tac o AP_TERM ``store_copy_normalize sbase`` o
        REWRITE_RULE [store_copy_normalize_def]) >>
     simp[store_copy_normalize_def]) >>
  fs[store_copy_frame_def] >>
  `store_copy_prefix loc b k sbase (i+1) =
    (if loc = LocStorage then sstore else tstore) (k+n2w i)
      (mload (w2n (b+n2w i*32w)) sbase) (store_copy_prefix loc b k sbase i)` by
    simp[store_copy_prefix_def, GSYM arithmeticTheory.ADD1,
         COUNT_LIST_SNOC, FOLDL_SNOC] >>
  `store_copy_normalize sbase
      ((if loc = LocStorage then sstore else tstore) (k+n2w i)
        (mload (w2n (b+n2w i*32w)) s) sm) =
    (if loc = LocStorage then sstore else tstore) (k+n2w i)
      (mload (w2n (b+n2w i*32w)) s) (store_copy_normalize sbase sm)` by
    (Cases_on `loc = LocStorage` >>
     POP_ASSUM_LIST (fn ths =>
       pure_rewrite_tac [hd ths, COND_CLAUSES]) >>
     simp[NoAsms, store_copy_normalize_def, sstore_def, tstore_def]) >>
  simp[mload_def]
QED

(* Counted header, including the conditional transfer. *)
Theorem storage_copy_header_path[local]:
  !ctx func bb sa loc b k sbase i n s cv tv id exit loop_body.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
    i <= n /\ n < dimword (:256) /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = (if i = n then exit else loop_body) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `((n2w i:bytes32) = n2w n) = (i = n)` by
    (`i < dimword (:256)` by decide_tac >>
     simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  qabbrev_tac `u = update_var tv (bool_to_word (i = n)) s` >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s = OK u` by
    (simp[Abbr `u`] >>
     qpat_assum `(n2w i = n2w n) = (i = n)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> simp[eval_operand_lit]) >>
  `gas_path_edge ctx func s 0 (OK r)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst id EQ [Var cv;Lit (n2w n)] [tv]`,
       `u` |-> `u`] tuple_straight_line_edge) >>
     simp[mk_inst_def, is_terminator_def, Abbr `r`]) >>
  `gas_path ctx func s 0 (OK r)` by
    (drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     simp[Abbr `r`, Abbr `u`, update_var_def]) >>
  `eval_operand (Var tv) r = SOME (bool_to_word (i = n)) /\
   r.vs_current_bb = s.vs_current_bb /\ r.vs_inst_idx = SUC s.vs_inst_idx /\
   ~r.vs_halted` by
    simp[Abbr `r`, Abbr `u`, eval_operand_def, lookup_var_update_var, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) r =
    OK (jump_to (if i = n then exit else loop_body) r)` by
    (simp[step_inst_base_def, mk_inst_def] >>
     Cases_on `i = n` >> gvs[bool_to_word_def]) >>
  `gas_path_edge ctx func r 0
     (OK (jump_to (if i = n then exit else loop_body) r))` by
    (simp[gas_path_edge_def] >>
     qexists_tac `0` >>
     simp[gasCountTheory.gas_count_step_def, mk_inst_def] >>
     disj2_tac >> disj2_tac >> disj1_tac >>
     qexists_tac `if i = n then exit else loop_body` >>
     simp[is_terminator_def, step_inst_non_invoke] >> gvs[mk_inst_def]) >>
  `gas_path ctx func r 0 (OK (jump_to (if i = n then exit else loop_body) r))` by
    (drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >> simp[jump_to_def]) >>
  qexists_tac `jump_to (if i = n then exit else loop_body) r` >>
  conj_tac
  >- (simp[gas_marked_path_def] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  simp[jump_to_def, Abbr `r`, Abbr `u`, eval_operand_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       store_copy_frame_def, store_copy_normalize_def] >>
  gvs[store_copy_frame_def, store_copy_normalize_def, eval_operand_def,
      lookup_var_def] >> metis_tac[]
QED

Theorem compile_store_copy_path[local]:
  !ctx func loc src dst n sa u sb sbase b k.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
    fn_has_code sa sb func /\ n < dimword (:256) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    ~sbase.vs_halted /\ ~sbase.vs_call_ctx.cc_static /\
    sbase.vs_current_bb = sa.cs_current_bb /\
    sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func sbase 0 (OK t) /\
      store_copy_frame sa loc b k sbase n t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def, word_scale_def, compile_ptr_load_def,
       compile_ptr_store_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, fresh_label_def, fresh_var_def, emit_inst_def,
       emit_op_def, emit_void_def, fresh_id_def, emit_def, new_block_def] >>
  map_every qabbrev_tac
    [`hdr = fresh_label_output "wcopy_cond" sa.cs_next_label`,
     `loop_body = fresh_label_output "wcopy_body" (sa.cs_next_label+1)`,
     `exit = fresh_label_output "wcopy_exit" (sa.cs_next_label+2)`,
     `cv = STRING #"%" (toString sa.cs_next_var)`,
     `tv = STRING #"%" (toString (sa.cs_next_var+1))`,
     `mv = STRING #"%" (toString (sa.cs_next_var+2))`,
     `sv = STRING #"%" (toString (sa.cs_next_var+3))`,
     `vv = STRING #"%" (toString (sa.cs_next_var+4))`,
     `dv = STRING #"%" (toString (sa.cs_next_var+5))`,
     `nv = STRING #"%" (toString (sa.cs_next_var+6))`] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  strip_tac >>
  `ALL_DISTINCT [cv;tv;mv;sv;vv;dv;nv] /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dv;nv])` by
    (simp[Abbr `cv`, Abbr `tv`, Abbr `mv`, Abbr `sv`, Abbr `vv`,
          Abbr `dv`, Abbr `nv`, ALL_DISTINCT, fresh_var_distinct] >>
     rw[not_fresh_at_def] >> irule fresh_var_distinct >> decide_tac) >>
  qpat_x_assum `!bb. MEM bb (TAKE _ _) ==> _` kall_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block loop_body func.fn_blocks = SOME body_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block hdr func.fn_blocks = SOME hdr_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block sa.cs_current_bb func.fn_blocks = SOME entry_bb` >>
  qmatch_goalsub_abbrev_tac `store_copy_frame sa store_loc b k sbase n` >>
  `!i s. store_copy_frame sa store_loc b k sbase i s /\
     eval_operand (Var cv) s = SOME (n2w i) /\ ~s.vs_halted /\
     s.vs_current_bb = loop_body /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path F ctx func s 0 (OK t) /\
       store_copy_frame sa store_loc b k sbase (SUC i) t /\
       eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
       t.vs_current_bb = loop_body /\ t.vs_inst_idx = 7 /\ ~t.vs_halted` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`bb` |-> `body_bb`, `id` |-> `sa.cs_next_id+4`,
                     `loc` |-> `store_loc`] (SPEC_ALL storage_copy_body_path)) >>
     (impl_tac >-
       (simp[Abbr `body_bb`, Abbr `store_loc`, get_instruction_def,
             arithmeticTheory.ADD_ASSOC] >>
        gvs[ALL_DISTINCT] >> metis_tac[])) >>
     simp[]) >>
  `!i s. store_copy_frame sa store_loc b k sbase i s /\
     eval_operand (Var cv) s = SOME (n2w i) /\ i <= n /\ ~s.vs_halted /\
     s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path F ctx func s 0 (OK t) /\
       store_copy_frame sa store_loc b k sbase i t /\
       eval_operand (Var cv) t = SOME (n2w i) /\
       t.vs_current_bb = (if i = n then exit else loop_body) /\
       t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`bb` |-> `hdr_bb`, `id` |-> `sa.cs_next_id+2`,
                     `loc` |-> `store_loc`] (SPEC_ALL storage_copy_header_path)) >>
     (impl_tac >-
       (simp[Abbr `hdr_bb`, get_instruction_def, arithmeticTheory.ADD_ASSOC] >>
        gvs[ALL_DISTINCT] >> metis_tac[])) >> simp[]) >>
  `!s jbb jid lbl. ~s.vs_halted /\
     lookup_block s.vs_current_bb func.fn_blocks = SOME jbb /\
     get_instruction jbb s.vs_inst_idx = SOME (mk_inst jid JMP [Label lbl] []) ==>
     gas_marked_path F ctx func s 0 (OK (jump_to lbl s))` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> strip_tac >>
     `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
       (simp[gas_path_edge_def] >> qexists_tac `0` >>
        simp[gasCountTheory.gas_count_step_def, mk_inst_def] >>
        disj2_tac >> disj2_tac >> disj1_tac >> qexists_tac `lbl` >>
        simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
             is_terminator_def]) >>
     simp[gas_marked_path_def] >>
     drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >> simp[jump_to_def]) >>
  `!i s. store_copy_frame sa store_loc b k sbase i s /\
     eval_operand (Var cv) s = SOME (n2w i) /\ ~s.vs_halted /\
     s.vs_current_bb = loop_body /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path F ctx func s 0 (OK t) /\
       store_copy_frame sa store_loc b k sbase (SUC i) t /\
       eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
       t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i s. _ ==> ?t. _ /\ _ /\ _ /\ t.vs_current_bb = loop_body /\ _`
       (qspecl_then [`i`, `s`] mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `r` strip_assume_tac) >>
     `gas_marked_path F ctx func r 0 (OK (jump_to hdr r))` by
       (qpat_assum `!s jbb jid lbl. _` irule >>
        (conj_tac >- simp[]) >> qexistsl_tac [`body_bb`, `sa.cs_next_id+11`] >>
        simp[Abbr `body_bb`, get_instruction_def]) >>
     qexists_tac `jump_to hdr r` >> conj_tac
     >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
         qexists_tac `r` >> simp[]) >>
     gvs[store_copy_frame_def, store_copy_normalize_def, jump_to_def,
         eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `!i s. _ ==> ?t. _ /\ _ /\ _ /\ t.vs_current_bb = loop_body /\ _` kall_tac >>
  qabbrev_tac `u0 = update_var cv 0w sbase` >>
  qabbrev_tac `r0 = u0 with vs_inst_idx := SUC sbase.vs_inst_idx` >>
  `gas_path_edge ctx func sbase 0 (OK r0)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]`,
       `u` |-> `u0`, `bb` |-> `entry_bb`, `s` |-> `sbase`]
       tuple_straight_line_edge) >>
     simp[Abbr `r0`, Abbr `u0`, Abbr `entry_bb`, get_instruction_def,
          EL_APPEND_EQN, mk_inst_def, is_terminator_def, step_inst_base_def,
          eval_operand_def]) >>
  `gas_marked_path F ctx func sbase 0 (OK r0)` by
    (simp[gas_marked_path_def] >> drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     simp[Abbr `r0`, Abbr `u0`, update_var_def]) >>
  `gas_marked_path F ctx func r0 0 (OK (jump_to hdr r0))` by
    (qpat_assum `!s jbb jid lbl. _` irule >>
     (conj_tac >- simp[Abbr `r0`, Abbr `u0`, update_var_def]) >>
     qexistsl_tac [`entry_bb`, `sa.cs_next_id+1`] >>
     simp[Abbr `r0`, Abbr `u0`, update_var_def, Abbr `entry_bb`,
          get_instruction_def, EL_APPEND_EQN, arithmeticTheory.ADD1]) >>
  `store_copy_frame sa store_loc b k sbase 0 (jump_to hdr r0) /\
   eval_operand (Var cv) (jump_to hdr r0) = SOME 0w /\
   ~(jump_to hdr r0).vs_halted` by
    (simp[store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def,
          Abbr `r0`, Abbr `u0`, update_var_def, jump_to_def,
          eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
          COUNT_LIST_def] >>
     conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
       qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
     qpat_x_assum `sbase.vs_current_bb = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `sbase.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[]) >>
  `!remaining i s. i + remaining = n /\
     store_copy_frame sa store_loc b k sbase i s /\
     eval_operand (Var cv) s = SOME (n2w i) /\ ~s.vs_halted /\
     s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path F ctx func s 0 (OK t) /\
       store_copy_frame sa store_loc b k sbase n t /\
       ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (qpat_assum `!i s. _ /\ _ /\ i <= n /\ _ ==> _` mp_tac >>
     qpat_assum `!i s. _ ==> ?t. _ /\ _ /\ _ /\ t.vs_current_bb = hdr /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     disch_then (mk_asm "body") >> disch_then (mk_asm "header") >>
     Induct_on `remaining`
     >- (rpt gen_tac >> simp[] >> strip_tac >>
         qpat_x_assum `i = n` SUBST_ALL_TAC >>
         asm "header" (qspecl_then [`n`, `s`] mp_tac) >>
         (impl_tac >- simp[]) >>
         disch_then (qx_choose_then `t` strip_assume_tac) >>
         qexists_tac `t` >> gvs[]) >>
     pop_assum (mk_asm "ih") >> rpt gen_tac >> strip_tac >>
     asm "header" (qspecl_then [`i`, `s`] mp_tac) >>
     (impl_tac >- (simp[] >> decide_tac)) >>
     disch_then (qx_choose_then `h` strip_assume_tac) >>
     `i <> n` by decide_tac >>
     qpat_x_assum `h.vs_current_bb = _` mp_tac >> simp[] >> disch_tac >>
     asm "body" (qspecl_then [`i`, `h`] mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `r` strip_assume_tac) >>
     asm "ih" (qspecl_then [`SUC i`, `r`] mp_tac) >>
     (impl_tac >- (simp[] >> decide_tac)) >>
     disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `h` >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `r` >> simp[]) >>
  qpat_assum `!remaining i s. _` (qspecl_then [`n`, `0`, `jump_to hdr r0`] mp_tac) >>
  (impl_tac >- simp[jump_to_def]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> fs[Abbr `store_loc`, Abbr `exit`] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `r0` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `jump_to hdr r0` >> simp[]
QED

Theorem storage_copy_accounts_fold[local]:
  !cx es s tr k ws is stor.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    accounts_rel cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  simp[storage_copy_backend_fold] >> Cases_on `tr` >> gvs[]
  >- (irule accounts_rel_set_transient >>
      qexistsl_tac [`es`, `s`, `stor`] >>
      simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]) >>
  irule accounts_rel_set_storage >>
  qexistsl_tac [`es`, `s`, `stor`] >>
  simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem storage_copy_state_fold[local]:
  !ctx func cenv cx es s tr k ws is stor.
    stmt_state_rel ctx func cenv cx es s /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all storage_copy_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, storage_copy_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, storage_copy_backend_fold,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, storage_copy_backend_fold, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, storage_copy_backend_fold]
QED

Theorem storage_copy_initial_agree[local]:
  !ctx func cenv cx es s tr.
    stmt_state_rel ctx func cenv cx es s ==>
    storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)
Proof
  rpt strip_tac >> Cases_on `tr` >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
     transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]
QED

Theorem storage_copy_state_region[local]:
  !ctx func cenv cx es s tr mid id subs k tv v writes off mem ws res es'.
    stmt_state_rel ctx func cenv cx es s /\
    declared_storage_region cx mid id subs = SOME (tr, k, tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (k, tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
    (!i. i < type_slot_size tv ==> MEM i (MAP FST writes)) /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes k writes (get_storage cx es tr))
                (w2n k) tv (w2n k + i) b) ==>
         ws i = mem_word_at (off + 32 * i) mem) /\
    write_storage_slot cx tr k tv v es = (res, es') ==>
    res = INL () /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t)
        s (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  `!i b. i < type_slot_size tv /\ b < 32 /\
     ~dead_bytes (apply_writes k writes (get_storage cx es tr))
       (w2n k) tv (w2n k + i) b ==> MEM i (MAP FST writes)` by simp[] >>
  drule_all storage_agree_copy_region >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[write_storage_slot_eq] >>
  irule storage_copy_state_fold >> simp[]
QED

Theorem storage_copy_state_zero[local]:
  !ctx func cenv cx es s tr k.
    stmt_state_rel ctx func cenv cx es s ==>
    stmt_state_rel ctx func cenv cx
      (set_storage cx es tr (update_storage k 0w (get_storage cx es tr)))
      ((if tr then tstore else sstore) k 0w s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  `storage_agree
     (storage_dead cx tr (update_storage k 0w (get_storage cx es tr)))
     (update_storage k 0w (get_storage cx es tr))
     (update_storage k 0w
       (if tr then contract_transient s else contract_storage s))` by
    (irule storage_agree_update >> goal_assum (drule_at Any) >>
     metis_tac[storage_dead_update_zero]) >>
  drule storage_copy_state_fold >>
  disch_then (qspecl_then [`tr`, `k`, `\i. 0w`, `[0]`] mp_tac) >>
  simp[wordsTheory.WORD_ADD_0] >> disch_then irule >> simp[]
QED

Theorem storage_copy_control_frame[local]:
  !ctx func cenv cx es s V bb ix prev.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt gen_tac >>
  `fmp_room ctx func
     (s with <|vs_vars := V; vs_current_bb := bb;
               vs_inst_idx := ix; vs_prev_bb := prev|>) =
   fmp_room ctx func (s with vs_vars := V)` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, immutable_base_zero_alt,
       lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
QED

Theorem storage_copy_normalized_state:
  !ctx func cenv cx es s t sa.
    stmt_state_rel ctx func cenv cx es
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) /\
    local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[storage_copy_control_frame] >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     ((t with vs_vars := s.vs_vars) with vs_vars := t.vs_vars)` suffices_by simp[] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

(* Storage writes keep the call context. *)
Theorem storage_fold_call_ctx[local]:
  !l s f g tr.
    (FOLDL (\t i. (if tr then tstore else sstore) (f i) (g i) t) s l).vs_call_ctx =
    s.vs_call_ctx
Proof
  Induct >> simp[FOLDL] >> Cases_on `tr` >> simp[sstore_def, tstore_def]
QED

Theorem storage_copy_bulk_run[local]:
  !ctx func cenv cx es' tr src k n sa sb u s b.
    compile_word_copy_loop src (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) /\
    n < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_store_copy_path >>
  disch_then (qspecl_then [`ctx`, `func`, `s`, `b`, `k`] mp_tac) >>
  `~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, storage_fold_call_ctx] >>
  (impl_tac >- (Cases_on `tr` >> simp[eval_operand_def])) >> strip_tac >>
  fs[store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def] >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (strip_assume_tac o MATCH_MP gas_path_normal o MATCH_MP gas_marked_path_exec) >>
  qexists_tac `t` >> simp[] >>
  qmatch_asmsub_abbrev_tac `norm = FOLDL _ _ _` >>
  `stmt_state_rel ctx func cenv cx es' norm` by
    (Cases_on `tr` >> gvs[Abbr `norm`]) >>
  `stmt_state_rel ctx func cenv cx es' t` by
    (irule storage_copy_normalized_state >>
     qexistsl_tac [`s`, `sa`] >> fs[Abbr `norm`] >>
     Cases_on `tr` >> gvs[]) >>
  simp[] >>
  `(if (if tr then LocTransient else LocStorage) = LocStorage
     then sstore else tstore) = (if tr then tstore else sstore)` by
    (Cases_on `tr` >> simp[]) >>
  qpat_x_assum `norm = _`
    (mp_tac o AP_TERM ``\t:venom_state. t.vs_allocas``) >>
  simp[Abbr `norm`, storage_copy_backend_fold] >>
  Cases_on `tr` >> simp[] >> metis_tac[]
QED

Theorem storage_copy_one_run[local]:
  !ctx func cenv cx es' tr src k sa sm sb op s b.
    emit_op MLOAD [src] sa = (op,sm) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit k;op] sm = ((),sb) /\
    eval_operand src s = SOME b /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      ((if tr then tstore else sstore) k (mload (w2n b) s) s) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
  drule_all emitted_insts_append >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Var out` >>
  `not_local_ptr cenv es'.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `u = update_var out (mload (w2n b) s) s` >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s = OK u` by
    (simp[Abbr `u`] >> irule step_MLOAD >> simp[]) >>
  `gas_path_edge ctx func s 0 (OK r)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst sa.cs_next_id MLOAD [src] [out]`,
                    `u` |-> `u`] tuple_straight_line_edge) >>
     simp[Abbr `r`, mk_inst_def, is_terminator_def] >>
     disch_then irule >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[mk_inst_def]) >>
  `gas_marked_path F ctx func s 0 (OK r)` by
    (simp[gas_marked_path_def] >> drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >>
     simp[Abbr `r`, Abbr `u`, update_var_def]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_split >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    (Cases_on `tr` >> fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def]) >>
  `eval_operand op r = SOME (mload (w2n b) s) /\
   ~r.vs_halted /\ ~r.vs_call_ctx.cc_static /\ r.vs_current_bb = sm.cs_current_bb /\
   r.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (gvs[Abbr `r`, Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
         FLOOKUP_UPDATE, same_blocks_def, IS_PREFIX_APPEND3]) >>
  drule_all assign_storage_store_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func r 0 (OK t)` >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `r` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es'
     (update_var out (mload (w2n b) s)
       ((if tr then tstore else sstore) k (mload (w2n b) s) s))` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `t = update_var out (mload (w2n b) s)
       ((if tr then tstore else sstore) k (mload (w2n b) s) s)
       with vs_inst_idx := SUC (SUC s.vs_inst_idx)` by
    (Cases_on `tr` >>
     simp[Abbr `t`, Abbr `r`, Abbr `u`, sstore_def, tstore_def,
          update_var_def, LET_THM, arithmeticTheory.ADD1]) >>
  `stmt_state_rel ctx func cenv cx es' t` by
    (qpat_assum `t = _` (fn th => rewrite_tac[th, stmt_state_rel_inst_idx]) >> simp[]) >>
  qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
    (strip_assume_tac o MATCH_MP gas_path_normal o MATCH_MP gas_marked_path_exec) >>
  qexists_tac `t` >> simp[] >>
  Cases_on `tr` >>
  simp[Abbr `t`, Abbr `r`, Abbr `u`, sstore_def, tstore_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, LET_THM, same_blocks_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[sstore_def, tstore_def, update_var_def, LET_THM, arithmeticTheory.ADD1] >>
  qexists_tac `fuel` >> simp[]
QED

Theorem storage_copy_suffix_run[local]:
  !ctx func cenv cx es' tr src k n typ src_ty loc sa sb s b.
    compile_assign_value cenv (Lit k)
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty (32 * n) sa = ((),sb) /\
    ~is_word_type typ /\ ~is_abi_dynamic cenv.ce_struct_fields typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = 32 * n /\
    0 < n /\ n < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  `32 * n DIV 32 = n` by
    (irule arithmeticTheory.DIV_UNIQUE >> qexists_tac `0` >> simp[]) >>
  dep_rewrite.DEP_REWRITE_TAC[assign_storage_copy_suffix] >>
  qpat_x_assum `32 * n DIV 32 = n` (fn th => simp[th]) >>
  Cases_on `n = 1`
  >- (gvs[] >>
      simp[comp_bind_def, AllCaseEqs()] >> strip_tac >>
      Cases_on `emit_op MLOAD [src] sa` >> gvs[] >>
      `COUNT_LIST 1 = [0]` by EVAL_TAC >>
      fs[wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES] >>
      drule_all storage_copy_one_run >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >> metis_tac[]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_bind_def, comp_return_def, AllCaseEqs()] >> strip_tac >>
  fs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `_ sa = (u,sf)` >>
  `compile_word_copy_loop src (Lit k) n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (u,sf)` by
    (Cases_on `tr` >> gvs[]) >>
  drule_all storage_copy_bulk_run >> simp[]
QED

Theorem storage_copy_post_region:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv tr mid id slot es'.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    post_value_type cenv e = expr_type e /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    ~is_abi_dynamic cenv.ce_struct_fields (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ value_has_type tv v /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') ==>
    ?w. eval_operand op s = SOME w /\ type_slot_size tv < dimword (:256) /\
      stmt_state_rel ctx func cenv cx es'
        (FOLDL (\t i. (if tr then tstore else sstore)
          (n2w slot+n2w i) (mload (w2n (w+n2w i*32w)) s) t)
          s (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  `slot < dimword (:256)` by decide_tac >>
  `IS_SOME (encode_value tv v)` by metis_tac[value_has_type_equiv] >>
  Cases_on `encode_value tv v` >> gvs[] >>
  rename1 `encode_value tv v = SOME writes` >>
  `~vyper_is_dynamic (get_tenv cx) (expr_type e)` by
    (drule_all abi_props_vyper_typed >> simp[]) >>
  `!i. i < type_slot_size tv ==> MEM i (MAP FST writes)` by
    (rpt strip_tac >> drule_all encode_value_live_written >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   expr_val_rel cx (expr_type e) v op s` by fs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `well_formed_type_value tv` by
    (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  drule_all storage_copy_post_words >>
  disch_then (qspec_then `get_storage cx es1 tr` strip_assume_tac) >>
  qexists_tac `w` >> simp[] >>
  ho_match_mp_tac (cj 2 storage_copy_state_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`, `id`, `[]`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem assign_storage_empty_stmt_frag[local]:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    expr_type e = typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    (!gs v st. (do result <- eval_expr cx e; read_result cx result od)
       (es with gas_obs := gs) = (INL v,st) ==> value_has_type tvt v) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` assume_tac) >>
  Cases_on `(do result <- eval_expr cx e; read_result cx result od)
              (es with gas_obs := [])` >>
  rename1 `_ = (rr, ee)` >>
  `!v st. (do result <- eval_expr cx e; read_result cx result od)
       (es with gas_obs := []) = (INL v,st) ==> value_has_type tvt v` by
    metis_tac[] >>
  drule_all storage_copy_empty_rhs >> strip_tac >> gvs[ETA_THM]
  >- (`FLOOKUP cenv.ce_module_vars (src,id) =
         SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
        (irule toplevel_storage_ce_vars >>
         gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
      drule_all assign_storage_empty_code >> strip_tac >> gvs[] >>
      `~s0.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
        fs[stmt_state_rel_def, state_rel_def] >>
      `eval_operand (Lit 0w) s0 = SOME 0w` by simp[eval_operand_def] >>
      drule_all assign_storage_store_path >>
      disch_then (qspec_then `ctx` assume_tac) >>
      drule_then (qspecl_then [`tr`, `n2w slot`] assume_tac)
        storage_copy_state_zero >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def] >>
      qexistsl_tac [`INL ()`,
        `set_storage cx es tr (update_storage (n2w slot) 0w (get_storage cx es tr))`,
        `OK ((if tr then tstore (n2w slot) 0w s0 else sstore (n2w slot) 0w s0)
              with vs_inst_idx := SUC s0.vs_inst_idx)`] >>
      conj_tac >- (conj_tac >-
        (gen_tac >>
         qpat_x_assum `!tail. _ = (INL v, _)`
           (qspec_then `tail` mp_tac) >>
         simp[bind_def] >> strip_tac >>
         gvs[AllCaseEqs()] >>
         Cases_on `tr` >>
         simp[write_storage_slot_eq, apply_writes_def,
              wordsTheory.WORD_ADD_0, wordsTheory.n2w_mod,
              set_storage_def, get_storage_def]) >>
        first_assum ACCEPT_TAC) >>
      `sb.cs_current_bb = sa.cs_current_bb /\
       LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
        (Cases_on `tr` >>
         gvs[emit_void_def, comp_bind_def, fresh_id_def,
             comp_ignore_bind_def, comp_return_def, emit_def]) >>
      `~block_is_terminated sb` by
        (Cases_on `tr` >> gvs[] >>
         drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
         simp[is_terminator_def]) >>
      qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx ee z` >>
      `stmt_state_rel ctx func cenv cx (ee with gas_obs := [])
        (z with <|vs_gas_readings := z.vs_gas_readings;
                  vs_inst_idx := SUC s0.vs_inst_idx|>)` by
        (irule msg_gas_state_frame >> simp[]) >>
      fs[] >>
      disj1_tac >> simp[stmt_post_def, stmt_lands_def] >>
      gvs[Abbr `ee`, Abbr `z`, cenv_top_ext_refl] >>
      Cases_on `tr` >>
      gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspec_then `[]` mp_tac) >>
  qpat_x_assum `!tail. _ = (INR _, _)` (qspec_then `[]` mp_tac) >>
  simp[bind_def] >> strip_tac >>
  gvs[AllCaseEqs(), stmt_res_ok_def]
QED

Theorem storage_copy_success_run[local]:
  !ctx func cenv cx e es es1 es' v tv tr mid id slot sa sm sf op loc s0 s1.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s1 /\
    ~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    ~is_abi_dynamic cenv.ce_struct_fields (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ value_has_type tv v /\
    lowered_value_type cenv e = expr_type e /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_assign_value cenv (Lit (n2w slot))
      (if tr then LocTransient else LocStorage) op F loc
      (expr_type e) (expr_type e) (type_memory_size tv) sm = ((),sf) /\
    fn_has_code sa sm func /\ fn_has_code sm sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s1 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x t = SOME u) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_lower_value_var >> simp[] >> disch_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  drule_all storage_copy_post_region >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [valueEncodingPropsTheory.type_memory_size_slots]) >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)
    storage_copy_suffix_run >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `s1`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[ci_mono_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  conj_tac >- metis_tac[] >>
  metis_tac[]
QED


(* Assignment to a non-word ABI-static storage or transient variable.
   The region fits the slot space and is apart from other declared regions. *)
Theorem compile_assign_storage_copy_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot
   tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    ~is_abi_dynamic cenv.ce_struct_fields typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (n2w slot, tvt) ==>
       ranges_disjoint slot (type_slot_size tvt)
                       (w2n k') (type_slot_size tv')) /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==>
       value_has_type tvt v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      es
Proof
  gen_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule assign_storage_empty_stmt_frag >> metis_tac[]) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_storage_copy_code_parts >> strip_tac >>
  qpat_x_assum `~(has_length_word _ /\ _)` kall_tac >> gvs[] >>
  fs[] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` assume_tac) >>
  irule forced_then_stmt_outcome >>
  qexistsl_tac [
    `\v ee t. expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
              t.vs_current_bb = sB.cs_current_bb /\
              t.vs_inst_idx = LENGTH sB.cs_current_insts`,
    `e`, `write_storage_slot cx tr (n2w slot) tvt`] >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[forced_then_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `value_has_type tvt v` by
    (qpat_x_assum `!gs v es1. _ ==> value_has_type _ _` irule >>
     fs[ETA_THM] >> metis_tac[]) >>
  `~cx.txn.is_static` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule typed_storage_copy_write >>
  disch_then (qspecl_then [`cx`, `tr`, `n2w slot`, `ee`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  drule_all (SRULE [] storage_copy_success_run) >> strip_tac >>
  qabbrev_tac `ee' = set_storage cx ee tr
    (apply_writes (n2w slot) writes (get_storage cx ee tr))` >>
  `ee'.gas_obs = []` by (Cases_on `tr` >> simp[Abbr `ee'`, set_storage_def]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `ee'`, `OK t'`] >>
  conj_tac >- fs[write_storage_slot_gas_obs] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  disj1_tac >> irule assign_storage_copy_suffix_open >> metis_tac[]
QED
