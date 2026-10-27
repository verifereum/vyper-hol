(* Independent checked-frontend bytecode witnesses for internal functions
   whose source names equal, or extend, labels the lowering makes itself
   (#546, a05-07). Internal functions are labelled internal_fn_label, so no
   source name can collide with a codegen, entry or external label.
   TOP-LEVEL: p69_int_name_code_end_matches_python_oracle,
              p87_int_name_revert_matches_python_oracle,
              p88_int_name_fn_prefix_matches_python_oracle,
              p90_int_name_fn_prefix_unused_matches_python_oracle,
              p89_int_name_entry_matches_python_oracle,
              nm_int_entry_matches_python_oracle,
              nm_int_deploy_matches_python_oracle,
              p70_int_name_reachable_matches_python_oracle,
              p71_int_name_return_label_matches_python_oracle,
              p69_int_name_code_end_supported, p87_int_name_revert_supported,
              p70_int_name_reachable_supported,
              p71_int_name_return_label_supported. *)
Theory evalCompilerInternalLabels
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../internal-labels/oracle/p69_int_name_code_end.json",
   "../internal-labels/oracle/p69_int_name_code_end.hex",
   "../internal-labels/oracle/p87_int_name_revert.json",
   "../internal-labels/oracle/p87_int_name_revert.hex",
   "../internal-labels/oracle/p88_int_name_fn_prefix.json",
   "../internal-labels/oracle/p88_int_name_fn_prefix.hex",
   "../internal-labels/oracle/p90_int_name_fn_prefix_unused.json",
   "../internal-labels/oracle/p90_int_name_fn_prefix_unused.hex",
   "../internal-labels/oracle/p89_int_name_entry.json",
   "../internal-labels/oracle/p89_int_name_entry.hex",
   "../internal-labels/oracle/nm_int_entry.json",
   "../internal-labels/oracle/nm_int_entry.hex",
   "../internal-labels/oracle/nm_int_deploy.json",
   "../internal-labels/oracle/nm_int_deploy.hex",
   "../internal-labels/oracle/p70_int_name_reachable.json",
   "../internal-labels/oracle/p70_int_name_reachable.hex",
   "../internal-labels/oracle/p71_int_name_return_label.json",
   "../internal-labels/oracle/p71_int_name_return_label.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../internal-labels/oracle"

(* a05-07: an internal function named code_end is not the codegen data-section
   label: the call returns y + 1 instead of jumping to the end of the
   code. *)
val p69_int_name_code_end = memoryStoreWitnessLib.evaluate fixture_root "p69_int_name_code_end"
Theorem p69_int_name_code_end_matches_python_oracle:
  ^(#term p69_int_name_code_end) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p69_int_name_code_end")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p69_int_name_code_end))) >> EVAL_TAC
QED

(* a05-07: an internal function named revert is not the codegen revert stub: the
   call returns y + 1 instead of reverting. *)
val p87_int_name_revert = memoryStoreWitnessLib.evaluate fixture_root "p87_int_name_revert"
Theorem p87_int_name_revert_matches_python_oracle:
  ^(#term p87_int_name_revert) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p87_int_name_revert")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p87_int_name_revert))) >> EVAL_TAC
QED

(* a05-07: an internal fn_foo next to an external foo does not share the external
   entry label "fn_foo" (was compile_vyper = NONE). *)
val p88_int_name_fn_prefix = memoryStoreWitnessLib.evaluate fixture_root "p88_int_name_fn_prefix"
Theorem p88_int_name_fn_prefix_matches_python_oracle:
  ^(#term p88_int_name_fn_prefix) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p88_int_name_fn_prefix")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p88_int_name_fn_prefix))) >> EVAL_TAC
QED

(* a05-07: the same, with fn_foo called only from another external function (was
   compile_vyper = NONE). *)
val p90_int_name_fn_prefix_unused = memoryStoreWitnessLib.evaluate fixture_root "p90_int_name_fn_prefix_unused"
Theorem p90_int_name_fn_prefix_unused_matches_python_oracle:
  ^(#term p90_int_name_fn_prefix_unused) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p90_int_name_fn_prefix_unused")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p90_int_name_fn_prefix_unused))) >> EVAL_TAC
QED

(* a05-07: an internal function named __entry does not share the runtime unit's
   entry label (was compile_vyper = NONE). *)
val p89_int_name_entry = memoryStoreWitnessLib.evaluate fixture_root "p89_int_name_entry"
Theorem p89_int_name_entry_matches_python_oracle:
  ^(#term p89_int_name_entry) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p89_int_name_entry")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p89_int_name_entry))) >> EVAL_TAC
QED

(* a05-07: the same with no arguments (was compile_vyper = NONE). *)
val nm_int_entry = memoryStoreWitnessLib.evaluate fixture_root "nm_int_entry"
Theorem nm_int_entry_matches_python_oracle:
  ^(#term nm_int_entry) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_int_entry")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_int_entry))) >> EVAL_TAC
QED

(* a05-07: an internal function named __deploy, called from the constructor
   and from an external function, does not share the deploy unit's entry
   label; it is labelled ..._deploy in the deploy unit and ..._runtime in the
   runtime unit. *)
val nm_int_deploy = memoryStoreWitnessLib.evaluate fixture_root "nm_int_deploy"
Theorem nm_int_deploy_matches_python_oracle:
  ^(#term nm_int_deploy) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_int_deploy")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_int_deploy))) >> EVAL_TAC
QED

(* a05-07: a reachable_ prefix, once excluded by the whitelist, compiles as
   before. *)
val p70_int_name_reachable = memoryStoreWitnessLib.evaluate fixture_root "p70_int_name_reachable"
Theorem p70_int_name_reachable_matches_python_oracle:
  ^(#term p70_int_name_reachable) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p70_int_name_reachable")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p70_int_name_reachable))) >> EVAL_TAC
QED

(* a05-07: a return_label_ prefix, once excluded by the whitelist, compiles as
   before. *)
val p71_int_name_return_label = memoryStoreWitnessLib.evaluate fixture_root "p71_int_name_return_label"
Theorem p71_int_name_return_label_matches_python_oracle:
  ^(#term p71_int_name_return_label) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p71_int_name_return_label")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p71_int_name_return_label))) >> EVAL_TAC
QED

(* The whitelist no longer excludes internal names that equal codegen
   labels. *)
Theorem p69_int_name_code_end_supported:
  supported_program
    ^(memoryStoreWitnessLib.program fixture_root "p69_int_name_code_end")
Proof
  EVAL_TAC
QED

Theorem p87_int_name_revert_supported:
  supported_program
    ^(memoryStoreWitnessLib.program fixture_root "p87_int_name_revert")
Proof
  EVAL_TAC
QED

(* The whitelist no longer excludes the reachable_ and return_label_
   prefixes. *)
Theorem p70_int_name_reachable_supported:
  supported_program
    ^(memoryStoreWitnessLib.program fixture_root "p70_int_name_reachable")
Proof
  EVAL_TAC
QED

Theorem p71_int_name_return_label_supported:
  supported_program
    ^(memoryStoreWitnessLib.program fixture_root "p71_int_name_return_label")
Proof
  EVAL_TAC
QED
