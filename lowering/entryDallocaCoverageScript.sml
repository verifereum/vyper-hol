(* Generic boundary for the unchanged body endpoint. *)
Theory entryDallocaCoverage
Ancestors
  exprLoweringProps venomInst list

Theorem context_without_dalloca_fmp_room:
  (!f. MEM f ctx.ctx_functions ==>
    ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)) /\
  MEM func ctx.ctx_functions ==> fmp_room ctx func s
Proof
  strip_tac >> simp[fmp_room_def] >> metis_tac[]
QED

(* DALLOCA coverage ledger (diagnostic, not a compiler exclusion theorem).

   Emission boundary:
   defs/contextScript:252 defines compile_alloc_dynamic = emit_op DALLOCA.
   The production callers found by source search are
   builtinSystem:40-46 (compile_msg_data_to_memory), builtinCreate:194,249
   (copy/blueprint creation). exprLowering:2763-2781 reaches the former
   through RawCallCalldataTarget; :2584-2619/:2798 reaches creation through
   CreateTarget. Other raw-call forms are rejected by the same support
   boundary, whether or not they dynamically allocate.

   Universal source coverage, unlike the finite supportedExprProps:316
   examples, is visible directly in supportedExprs:10-51,63-103:
   pure expressions reject every Call; effect expressions admit only
   IntCall, ExtCall and the two Send forms. RawCallTarget,
   RawCallCalldataTarget and every CreateTarget flag combination fall into
   the false catch-all. Recursive pure/effect/place branches check their
   children. supportedStmts supplies the corresponding statement traversal.
   This still needs a checked mutual source-to-compiler exclusion theorem;
   expr_evm_run_root alone is not that theorem.

   All source bodies, not only the selected body:
   supportedProgram:54-57 checks EVERY declaration; :89-104 exports
   supported_program_declaration and supported_program_function.
   supported_function_body:30-39 exports supported_stmts with bindings.
   supportedDecls:31-37 rejects defaults universally (NULL defaults) and
   nonreentrancy. classify_function (compileVyper:287-309) only selects
   FunctionDecl bodies: all ordinary externals, all internals, and the
   selected __default__ fallback inherit this support; constructor slot is
   not compiled by lower_vyper_runtime_unit. Packaging (:1010,1105 and
   package_fallback_fn) retains these bodies; set_*_package_target only
   updates ce_target. Need classification provenance lemmas for all three
   runtime collections, not just selected lookup_function.

   Generated code/context boundary:
   moduleLowering:756-821 emits dispatch, every external body's entry checks,
   positional registration and guarded body, fallback (or empty REVERT),
   and every internal body. Dynamic ABI decoders use static allocations
   and loops, not compile_alloc_dynamic. Their full emitted instructions
   must be covered, including scratch code and blocks unreachable at run
   time. Creation/raw-call exclusion does not follow merely from trace
   correctness. Existing leaf opcode lists (calldataWordLeaf,
   calldataDynInit, calldataDynStep and encoder phase files) can discharge
   concrete emission cases but no general whole-lowering opcode exclusion
   theorem was found by the no_dalloca/without_dalloca/opcode-preservation
   searches. A compositional compile-state instruction-predicate invariant
   is the missing structural interface, not another execution simulation.

   vyperCompiler:630-648 runs compile_generate_runtime and then extraction,
   with policy/context checks; it does not execute an optimizer here.
   extract_context_with_internals:137-149 partitions
   REVERSE cs_blocks ++ [current block] via package_internal_blocks:97-110
   into __entry and internal functions without changing instructions.
   Need a block-subset/partition preservation lemma to lift the instruction
   predicate to EVERY context function's fn_insts, and context membership
   from the selected __entry lookup. fn_ptr_ok_check is not an exclusion.

   Recommended production route: prove source/classification provenance,
   compositional emitted-instruction exclusion (mutual expression/place and
   statement recursion plus decoder/encoder boundaries), then extraction
   preservation. No uncovered supported DALLOCA trigger was found. This is
   an audit conclusion only: none of those missing preservation theorems is
   asserted here. The checked generic boundary above is usable once that
   context-wide premise is produced; other body-start resources remain.
*)
