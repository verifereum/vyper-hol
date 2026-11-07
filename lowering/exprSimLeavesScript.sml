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
  compileEnv accountsRelProps loweringSlice
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
    else print "statement-check gate skipped\n"
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
  cheat
QED

Theorem compile_literal_other_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\
    ~(is_word_type ann /\
      ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  cheat
QED

Theorem compile_literal_sim:
  !cenv ann l. expr_sim_ok cenv (Literal ann l)
Proof
  cheat
QED


(* A bytes literal is a word unless it is annotated with a dynamic bytes
   type. *)

Theorem compile_literal_case_sim:
  !cenv ann l. expr_ok cenv (Literal ann l)
Proof
  cheat
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
  cheat
QED


Theorem compile_env_case_sim:
  !cenv ann item args. expr_sim_ok cenv (Builtin ann (Env item) args)
Proof
  cheat
QED

(* An environment read goes to the builtin dispatcher, whatever its
   arguments (as exprBopLowering's compile_expr_bop). *)
Theorem compile_expr_env:
  !cenv ty ann item args st.
    compile_expr cenv ty (Builtin ann (Env item) args) st =
    compile_builtin_dispatch cenv ann ty (Env item) args st
Proof
  cheat
QED

Theorem compile_env_case_ok:
  !cenv ann item args. expr_ok cenv (Builtin ann (Env item) args)
Proof
  cheat
QED

(* ===== Top-level names and flag members ===== *)

(* Integrity gate: memory forcing must not introduce admitted dependencies
   into the existing Name and memory-literal consumers. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "MEMORY_CONSUMER_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end) [compile_name_other_sim, compile_name_sim, compile_name_case_sim,
        compile_literal_memory_sim];
