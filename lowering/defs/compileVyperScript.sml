(*
 * Top-Level Vyper Compiler: toplevel list → byte list option
 *
 * Packages the full compilation pipeline:
 *   1. Module analysis: extract metadata from toplevel list
 *   2. Lowering: Vyper AST → Venom IR (via compile_generate_runtime)
 *   3. Optimization: pipeline of Venom passes
 *   4. Codegen: Venom IR → EVM bytecode
 *
 * TOP-LEVEL:
 *   compiler_config        -- compiler options not derivable from source
 *   default_compiler_config -- sensible defaults
 *   compile_vyper          -- toplevel list → byte list option
 *
 * Helper:
 *   selector_has_trailing_zeroes -- check if selector has trailing zero bytes
 *   compute_selector      -- compute (sel_num, label, htz) from function
 *   build_selectors        -- build selector table from external functions
 *   package_external_fn    -- package external fn for compile_generate_runtime
 *   package_internal_fn    -- package internal fn for compile_generate_runtime
 *   package_fallback_fn    -- package fallback fn
 *   compute_fn_eom_map     -- build fn_eom_map from compiled context
 *)

Theory compileVyper
Ancestors
  moduleAnalysis
  vyperCompiler
  venomPipeline
  codegen
  selectorDispatch
  vyperContext
  compileEnv
  vyperAST

(* ===== Compiler Configuration ===== *)

(* Options not derivable from source code *)
Datatype:
  compiler_config = <|
    cc_dispatch_strategy : string;
    cc_bucket_count : num;
    cc_fn_metadata_bytes : num;
    cc_entry_label : string;
    cc_data_seg : data_section list;
    cc_use_transient_locks : bool
  |>
End

Definition default_compiler_config_def:
  default_compiler_config = <|
    cc_dispatch_strategy := "linear";
    cc_bucket_count := 0;
    cc_fn_metadata_bytes := 0;
    cc_entry_label := "__entry";
    cc_data_seg := [];
    cc_use_transient_locks := F
  |>
End

(* ===== Selector Construction ===== *)

(* Check if a selector number has trailing zero bytes.
   Used by sparse dispatch: if the selector value's low byte is 0,
   calldata shorter than 4 bytes could false-match via zero-padding. *)
Definition selector_has_trailing_zeroes_def:
  selector_has_trailing_zeroes (sel_num : num) = (sel_num MOD 256 = 0)
End

(* Compute selector entry for one external function.
   Returns (selector_num, entry_label, has_trailing_zeroes).
   Uses function_selector (keccak256 of ABI signature) and
   calldata_method_id to get the 4-byte selector as a num. *)
Definition compute_selector_def:
  compute_selector tenv func_name (arg_types : type list) =
    let abi_types = vyper_to_abi_types tenv arg_types in
    let sel_bytes = function_selector func_name abi_types in
    let sel_num = w2n (calldata_method_id sel_bytes) in
    let entry_lbl = "fn_" ++ func_name in
    (sel_num, entry_lbl, selector_has_trailing_zeroes sel_num)
End

(* Build selector table from classified external functions. *)
Definition build_selectors_def:
  build_selectors tenv [] = [] ∧
  build_selectors tenv
    ((_, _, _, fname, fargs, _, _, _) :: rest) =
    compute_selector tenv fname (MAP SND fargs) ::
    build_selectors tenv rest
End

(* ===== Function Packaging ===== *)

(* Package an external function into the tuple format expected by
   compile_external_fn_bodies:
   (entry_lbl, cenv, pos_args, min_cds, is_payable, is_nr, nkey,
    use_trans, is_view, body, ret_type) *)
Definition package_external_fn_def:
  package_external_fn tops use_trans nkey_map
    (_, mut, nr, fname, fargs, dflts, ret, body) =
    let entry_lbl = "fn_" ++ fname in
    let cenv_base = build_compile_env tops External mut fname
                      fargs ret body use_trans in
    let cenv = if ret ≠ NoneT then update_cenv_ret_abi cenv_base ret
               else cenv_base in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    let min_cds = min_calldata_size cenv_final fargs (LENGTH dflts) in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    (entry_lbl, cenv_final, pos_args, min_cds,
     is_payable, nr, nkey, use_trans, is_view,
     body, SOME ret)
End

(* Package an internal function into the tuple format expected by
   compile_internal_fn_bodies:
   (fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
    is_view, is_ctor, imm_len, imm_aid, body, ret_type) *)
Definition package_internal_fn_def:
  package_internal_fn tops use_trans nkey_map
    (vis, mut, nr, fname, fargs, _, ret, body) =
    let fn_lbl = "fn_" ++ fname in
    let cenv = build_compile_env tops vis mut fname fargs ret body use_trans in
    let sft_types = (λname. MAP (FST o SND)
                      (make_struct_fields_map tops name)) in
    let rc = returns_stack_count sft_types ret in
    let has_ret_buf = (rc = 0 ∧ ret ≠ NoneT) in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let is_view = (mut = View) in
    let is_ctor = (vis = Deploy) in
    (* Internal function params: (name, pass_via_stack) pairs *)
    let pvs = compute_pass_via_stack (MAP SND fargs) rc in
    let params = ZIP (MAP FST fargs, pvs) in
    (fn_lbl, cenv_final, params, has_ret_buf,
     nr, nkey, use_trans, is_view,
     is_ctor, 0n, 0n,
     body, SOME ret)
End

(* Package fallback function *)
Definition package_fallback_fn_def:
  package_fallback_fn tops use_trans nkey_map NONE = NONE ∧
  package_fallback_fn tops use_trans nkey_map
    (SOME (_, mut, nr, fname, fargs, _, ret, body)) =
    let cenv = build_compile_env tops External mut fname
                 fargs ret body use_trans in
    let nkey = nkey_map fname in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    SOME (cenv, is_payable, nr, nkey, use_trans, is_view,
          body, if ret = NoneT then NONE else SOME ret)
End

(* ===== End-of-Memory Map ===== *)

(* Compute fn_eom_map: for each function in the compiled context,
   fn_eom = 0 (conservative: user memory starts at 0, spills above).
   A more precise version would compute max alloca offset per function
   from the compile_env, but 0 is correct when the entry code
   initializes memory properly. *)
Definition compute_fn_eom_map_def:
  compute_fn_eom_map (ctx : venom_context) =
    FOLDL (λacc fn. acc |+ (fn.fn_name, 0n))
      FEMPTY ctx.ctx_functions
End

(* ===== Full Compilation ===== *)

(* compile_vyper: the clean top-level compiler function.

   Takes a compiler config, optimization pipeline, and toplevel list.
   Produces bytecode (byte list option).

   The pipeline is a parameter — instantiate with:
   - venom_pipeline ircf ricf threshold (o2_fn_passes ...)  for O2
   - venom_pipeline ircf ricf threshold (o3_fn_passes ...)  for O3
   - venom_pipeline ircf ricf threshold (os_fn_passes ...)  for Os
   - I                                                       for no optimization *)
Definition compile_vyper_def:
  compile_vyper (cfg : compiler_config)
                (pipeline : venom_context -> venom_context)
                (tops : toplevel list) =
    (* 1. Extract module metadata *)
    let tenv = type_env tops in
    let nkey_map = make_nkey_map tops in
    let use_trans = cfg.cc_use_transient_locks in
    (* 2. Classify functions *)
    let (ext_fns, int_fns, fb_fn) = classify_functions tops in
    (* 3. Build selector table *)
    let selectors = build_selectors tenv ext_fns in
    (* 4. Package functions for lowering *)
    let external_fns = MAP (package_external_fn tops use_trans nkey_map)
                           ext_fns in
    let internal_fns = MAP (package_internal_fn tops use_trans nkey_map)
                           int_fns in
    let fallback_fn = package_fallback_fn tops use_trans nkey_map fb_fn in
    (* 5. Lower to Venom IR *)
    let ctx = run_lowering selectors external_fns internal_fns fallback_fn
                cfg.cc_dispatch_strategy cfg.cc_bucket_count
                cfg.cc_fn_metadata_bytes cfg.cc_entry_label in
    (* 6. Optimize *)
    let ctx' = pipeline ctx in
    (* 7. Codegen *)
    let fn_eom_map = compute_fn_eom_map ctx' in
    codegen ctx' fn_eom_map cfg.cc_data_seg
End
