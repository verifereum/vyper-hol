(*
 * Expression simulation: the leaves (#636, Leaves)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the expressions
 * without subexpressions.  Each concludes expr_sim_ok (exprSimHyps).
 *
 * TOP-LEVEL:
 *   compile_name_vv_sim      — a local of any type: its pointer variable,
 *                              as a memory pointer, no code
 *   compile_name_sim         — a local: word locals by compile_name_word_sim
 *                              (exprSim), the rest by compile_name_other_sim
 *                              (compile_name_vv_sim and unwrap_value)
 *   compile_literal_sim      — a literal: bool, integer and decimal literals
 *                              of a word type by compile_literal_word_sim
 *                              (exprSim), the rest by
 *                              compile_literal_other_sim: address and bytesN
 *                              literals by compile_literal_bytes_word_sim,
 *                              bytes and string literals by
 *                              compile_literal_memory_sim, from
 *                              compile_literal_other_vv_sim
 *                              (exprSimLiteralBuffer)
 *   compile_env_case_sim     — an environment read: by compile_env_sim
 *                              (exprSim), block.prevhash by
 *                              compile_prevhash_sim, msg.gas by
 *                              compile_msg_gas_sim (msgGasPost)
 *   compile_toplevel_name_sim — storage, transient, immutable and constant
 *                              reads: a storage or transient variable by
 *                              compile_toplevel_storage_vv_sim, a pointer
 *                              to its slot, whose ce_module_vars entry
 *                              comes from storage_vars_rel and
 *                              transient_vars_rel; its slot decodes by
 *                              expr_sim_inv's storage clauses
 *                              (compile_toplevel_storage_undecodable_sim)
 *   compile_flag_member_case_sim — a flag member: the literal 2 ** id, by
 *                              expr_sim_inv's flag members clause
 *
 * Helpers: expr_sim_of_vv_sim_memory, eval_expr_toplevel_storage,
 *   toplevel_storage_ce_vars, toplevel_storage_read_decodes,
 *   compile_toplevel_no_module_sim
 *
 * Unprovable as the definitions stand, to be fixed in the lowering, in
 * state_rel or in the judgment before their PRs:
 *   compile_toplevel_immutable_sim — immutables and constants (row 3),
 *                              which lookup_global reads from the
 *                              immutables: nothing puts them in
 *                              ce_module_vars,
 *                              so the lowering may emit INVALID where the
 *                              source reads a value (#563 for immutables).
 *)

Theory exprSimLeaves
Ancestors
  exprSimTopLevel
  exprSimName
  exprSimProps exprSimMemoryForce exprSimUnwrapProps
  exprSimHypsDefs
  msgGasPost
  exprSimDefs
  loweringPosts
  list finite_map
  exprSimBufferForce exprLowering exprLoweringProps
  freshWrites builtinProps varsExt vyperContext exprSimUnop exprSimHyps exprSimUnwrap
  compileEnv loweringStateRelDefs accountsRelProps loweringSlice
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeEnv vyperTyping vyperTypeGlobalLookupSoundness
  vyperValueOperation valueEncoding fragExec venomState exprSimLiteralBuffer
  vyperStorageLayoutSafety vyperLookupStorage vyperTypeValues
  exprSimNameWord
  exprSimNameValue
  exprSimLiteralWord
  exprSimLiteralBytes
  exprSimEnv
  exprSimFlagWord
  exprSimValues exprSimUnopProps gasNormalPrefix gasSummary fragGasMode fragGasSeq

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== No code before unwrap_value ===== *)

(* expr_sim_of_vv_sim (exprSimUnwrap) for a form whose compile_expr emits
   no code and hands out a pointer into memory: the compile state does not
   move, so compile_expr_extends is not needed, and unwrap_value is
   unwrap_memory_sim's load or nothing, so no cheated unwrap case is. *)

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag expr_sim_of_vv_sim_memory)
  in
    if null axioms andalso null (Thm.hyp expr_sim_of_vv_sim_memory) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "MEMORY_FORCE_AUDIT expr_sim_of_vv_sim_memory OK\n"
    else raise Fail "expr_sim_of_vv_sim_memory: admitted proof dependency"
  end;

(* ===== Locals ===== *)

(* A local held through its pointer variable p, as expr_sim_inv's locals
   clause has every local: its value_vv is p as a memory pointer, no code,
   and local_ptrs_rel lays the value out at p's word, inside the local's
   region. *)

(* ===== Literals ===== *)


Theorem compile_literal_memory_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rpt strip_tac >> irule exprSimBufferForceTheory.expr_sim_of_vv_sim_buffer >>
  `(?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)` by
    (gvs[expr_sim_pre_def, well_typed_expr_def] >> Cases_on `l` >> gvs[] >>
     Cases_on `ann` >> gvs[well_typed_literal_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  `expr_vv_ok cenv (Literal ann l)` by
    (irule compile_literal_other_vv_sim >> gvs[]) >>
  `expr_vv_sim ctx func cenv cx ty (Literal ann l) es` by
    (gvs[expr_vv_ok_def] >> metis_tac[]) >>
  simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def] >>
  rpt gen_tac >>
  simp[compile_expr_def, compile_literal_vv_def, vyperASTTheory.expr_type_def,
       is_word_type_def, comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  simp[contextTheory.base_ptr_def, is_word_type_def] >>
  rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      is_word_type_def, comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  simp[contextTheory.base_ptr_def, is_word_type_def]
QED

Theorem compile_literal_other_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\
    ~(is_word_type ann /\
      ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rpt strip_tac >> Cases_on `is_word_type ann`
  >- (Cases_on `l` >> gvs[]
      >~ [`BytesL bs`] >- (irule compile_literal_bytes_word_sim >> metis_tac[]) >>
      gvs[expr_sim_pre_def, well_typed_expr_def] >>
      Cases_on `ann` >> gvs[well_typed_literal_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[well_typed_literal_def, is_word_type_def]) >>
  irule compile_literal_memory_sim >> metis_tac[]
QED

Theorem compile_literal_sim:
  !cenv ann l. expr_sim_ok cenv (Literal ann l)
Proof
  rw[expr_sim_ok_def] >>
  Cases_on `is_word_type ann /\
            ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))`
  >- (irule compile_literal_word_sim >> fs[]) >>
  irule compile_literal_other_sim >> metis_tac[]
QED


(* A bytes literal is a word unless it is annotated with a dynamic bytes
   type. *)

Theorem compile_literal_case_sim:
  !cenv ann l. expr_ok cenv (Literal ann l)
Proof
  rpt gen_tac >>
  Cases_on `(?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)`
  >- (simp[expr_ok_def, compile_literal_sim] >>
      irule compile_literal_other_vv_sim >> simp[]) >>
  irule expr_ok_stack >> simp[compile_literal_sim] >> rpt conj_tac
  >~ [`eval_expr`]
  >- (rpt strip_tac >> drule eval_expr_literal_value >> simp[]) >>
  Cases_on `l` >> gvs[]
  >~ [`BytesL bs`]
  >- (`!n. ann <> BaseT (BytesT (Dynamic n))` by
        (rpt strip_tac >> gvs[is_word_type_def]) >>
      simp[compile_expr_def, vyperASTTheory.expr_type_def] >> rpt gen_tac >>
      drule compile_literal_bytes_stack >>
      disch_then (qspecl_then [`bs`, `sa`] strip_assume_tac) >> simp[])
  >~ [`BoolL b`]
  >- (Cases_on `b` >>
      simp[compile_expr_def, compile_literal_vv_def, comp_return_def]) >>
  simp[compile_expr_def, compile_literal_vv_def, comp_return_def]
QED

(* ===== Environment reads ===== *)

(* block.prevhash: compile_env_var PrevHash emits NUMBER, SUB 1,
   BLOCKHASH, with no check.  call_ctx_rel's tx_env_ok makes the source's
   evaluate_block_hash (block_number - 1) succeed (block_number <> 0 and
   the hash list is nonempty) with EL 0 block_hashes, and its bc_blockhash
   clause gives the same at block_number - 1.  So the source read succeeds
   whatever the gas observations, and the three instructions, none of them
   GAS, run as a zero-mark path from s0. *)
Theorem compile_prevhash_sim:
  !cenv ann args. expr_sim_ok cenv (Builtin ann (Env PrevHash) args)
Proof
  rw[expr_sim_ok_def] >>
  `args = [] /\ ann = env_item_type PrevHash` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> irule expr_sim_values >> rpt strip_tac >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `tx_env_ok cx.txn` by gvs[call_ctx_rel_def] >>
  `!tail. bind (eval_expr cx (Builtin (env_item_type PrevHash) (Env PrevHash) []))
            (read_result cx) (es with gas_obs := tail) =
          (INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))),
           es with gas_obs := tail)` by
    (simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
          builtin_args_length_ok_def, read_result_def] >>
     simp[Once evaluate_def, bind_def, read_result_def, return_def,
          evaluate_builtin_def, tx_env_ok_evaluate_prevhash]) >>
  drule lower_value_env >> strip_tac >>
  drule compile_prevhash_shape >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_prevhash_run >> strip_tac >>
  `(drop_fresh sa s0).vs_block_ctx = s0.vs_block_ctx` by simp[drop_fresh_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[listTheory.EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> rename1 `vars_ext tt t` >>
  drule call_ctx_rel_prevhash >> strip_tac >>
  `eval_operand op t = SOME (HD cx.txn.block_hashes)` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = tt with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  drule_all compile_prevhash_frame >> strip_tac >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
     PURE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  `gas_path ctx func s0 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     impl_tac >- fs[listTheory.EVERY_MEM] >>
     `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
       (simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM] >>
        rpt strip_tac >> first_x_assum drule >> rw[] >> gvs[]) >>
     `s0.vs_inst_idx + LENGTH (emitted_insts sa sb) =
      LENGTH sb.cs_current_insts` by
       (gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
        PURE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC,
                      rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
     simp[]) >>
  `t.vs_allocas = s0.vs_allocas /\ t.vs_memory = s0.vs_memory /\
   t.vs_halted = s0.vs_halted /\ t.vs_current_bb = s0.vs_current_bb /\
   t.vs_gas_readings = s0.vs_gas_readings` by
    (qpat_x_assum `t = _ with vs_vars := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_x_assum `t = _ with vs_vars := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     simp[lookup_var_def] >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule msg_gas_state_frame >>
  disch_then (qspecl_then [`t.vs_gas_readings`,
    `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[]`, `BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))`,
    `es`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
       GSYM ETA_THM] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, env_item_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes,
       locals_kept_mem, lookup_var_def]
QED


Theorem compile_env_case_sim:
  !cenv ann item args. expr_sim_ok cenv (Builtin ann (Env item) args)
Proof
  rpt gen_tac >> Cases_on `item = PrevHash`
  >- simp[compile_prevhash_sim] >>
  Cases_on `item = MsgGas`
  >- simp[compile_msg_gas_sim] >>
  rw[expr_sim_ok_def] >>
  `args = [] /\ ann = env_item_type item` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> irule compile_env_sim >> simp[]
QED

(* An environment read goes to the builtin dispatcher, whatever its
   arguments (as exprBopLowering's compile_expr_bop). *)
Theorem compile_expr_env:
  !cenv ty ann item args st.
    compile_expr cenv ty (Builtin ann (Env item) args) st =
    compile_builtin_dispatch cenv ann ty (Env item) args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def] >>
  namedCases_on `args` ["", "arg rest"] >> simp[] >>
  Cases_on `arg` >> simp expr_sizes
  >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: suffix) _`]
  >- (namedCases_on `suffix` ["", "arg2 tail2"] >> simp expr_sizes >>
      Cases_on `arg2` >> simp expr_sizes
      >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: Name _ _ :: suffix2) _`]
      >- (namedCases_on `suffix2` ["", "arg3 tail3"] >> simp expr_sizes >>
          Cases_on `arg3` >> simp expr_sizes
          >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: Name _ _ :: Name _ _ :: suffix3) _`]
          >- (Cases_on `suffix3` >> simp expr_sizes) >>
          rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes) >>
      rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes) >>
  rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes
QED

Theorem compile_env_case_ok:
  !cenv ann item args. expr_ok cenv (Builtin ann (Env item) args)
Proof
  rpt gen_tac >> irule expr_ok_stack >> simp[compile_env_case_sim] >>
  rpt conj_tac
  >~ [`eval_expr`]
  >- (rpt strip_tac >> drule eval_expr_builtin_value >> simp[]) >>
  rpt gen_tac >>
  simp[compile_expr_env] >> simp[Once compile_expr_def] >>
  metis_tac[as_stack_val_stack]
QED

(* ===== Top-level names and flag members ===== *)

(* Integrity gate: memory forcing must not introduce admitted dependencies
   into the existing Name and memory-literal consumers. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "MEMORY_CONSUMER_AUDIT OK\n"
     else raise Fail "memory consumer inherited admission"
  end) [compile_name_other_sim, compile_name_sim, compile_name_case_sim,
        compile_literal_memory_sim];
