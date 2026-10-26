(* Bounded default-store probes; not a general expression simulation. *)
Theory kwargDefaultProbe
Ancestors kwargBufferProps exprLowering localPtrsProps vyperExternalDefaultsTest
  venomInst venomState venomExecSemantics list

Theorem kwarg_sender_emission:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB
      [("who", Lit 128w, BaseT AddressT, Builtin (BaseT AddressT) (Env Sender) [])]
      4 0 (Lit 0w) kwarg_probe_state)).cs_current_insts =
    [(CALLER, []); (MSTORE, [Lit 128w; Var "%0"])]
Proof
  EVAL_TAC >> simp[]
QED

Theorem kwarg_bytes_default_emission:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB
      [("b", Lit 128w, BaseT (BytesT (Dynamic 10)),
        Literal (BaseT (BytesT (Dynamic 10))) (BytesL []))]
      4 0 (Lit 0w) kwarg_probe_state)).cs_current_insts =
    [(ALLOCA, [Lit 32w]); (MSTORE, [Var "%0"; Lit 0w]);
     (MLOAD, [Var "%0"]); (ADD, [Var "%1"; Lit 31w]);
     (AND, [Var "%2"; Lit (-32w)]); (ADD, [Var "%3"; Lit 32w]);
     (MCOPY, [Lit 128w; Var "%0"; Var "%4"])]
Proof
  EVAL_TAC >> simp[]
QED

Definition default_probe_env_def:
  default_probe_env = (ARB : compile_env) with
    <| ce_func_info := (\name. (1, 0, []));
       ce_func_param_types := (\name. []);
       ce_func_ids := (\name. 0);
       ce_is_ctor := F |>
End

(* A scalar internal return is first materialized into its return buffer,
   then unwrapped with MLOAD before writing the keyword buffer. The source
   lookup name is "g"; INVOKE uses its runtime internal-function label. *)
Theorem kwarg_intcall_emission:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs default_probe_env
      [("a", Lit 128w, BaseT (UintT 256),
        Call (BaseT (UintT 256)) (IntCall (NONE, "g")) [] NONE)]
      4 0 (Lit 0w) kwarg_probe_state)).cs_current_insts =
    [(ALLOCA, [Lit 32w]); (INVOKE, [Label "internal 0 g()_runtime"]);
     (ADD, [Var "%0"; Lit 0w]); (MSTORE, [Var "%2"; Var "%1"]);
     (MLOAD, [Var "%0"]); (MSTORE, [Lit 128w; Var "%3"])]
Proof
  EVAL_TAC >> simp[]
QED

Definition stateful_default_callee_def:
  stateful_default_callee = mk_raw_function "g"
    [<| bb_label := "g"; bb_instructions :=
      [mk_inst 0 SSTORE [Lit 0w; Lit 1w] [];
       mk_inst 1 RET [Lit 7w; Lit 0w] []] |>]
End

Theorem stateful_default_callee_run:
  run_function 1 ARB stateful_default_callee ss =
    IntRet <| iret_values := [7w]; iret_adopt_fmp := NONE |>
      ((sstore 0w 1w
        (ss with <| vs_current_bb := "g"; vs_inst_idx := 0 |>)) with vs_inst_idx := 1)
Proof
  simp[stateful_default_callee_def, mk_raw_function_def,
       run_function_def, fn_entry_label_def, entry_block_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, mk_inst_def,
       eval_phis_def, phi_prefix_length_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       step_inst_base_def, exec_write2_def, eval_operand_def] >>
  simp[Once exec_block_def, get_instruction_def, Once step_inst_def,
       step_inst_base_def, eval_operands_def, eval_operand_def,
       is_terminator_def]
QED

(* The callee's storage update must survive return, but does not destroy
   already initialized caller buffers. No account-equality premise is used. *)
Theorem default_storage_effect_merge:
  (merge_callee_state caller (sstore k v caller)).vs_memory = caller.vs_memory /\
  (merge_callee_state caller (sstore k v caller)).vs_accounts =
    (sstore k v caller).vs_accounts /\
  (merge_callee_state caller (sstore k v caller)).vs_vars = caller.vs_vars
Proof
  simp[merge_callee_state_def, sstore_def]
QED

Theorem default_storage_effect_preserves_earlier_buffers:
  local_ptrs_rel func cenv scopes ss ==>
  local_ptrs_rel func cenv scopes (merge_callee_state ss (sstore k v ss))
Proof
  simp[merge_callee_state_def, sstore_def,
       compileEnvTheory.local_ptrs_rel_def, compileEnvTheory.local_region_def,
       compileEnvTheory.local_backed_def, lookup_var_def]
QED

(* Unlike storage writes, copying a compound default needs a disjointness
   contract for the whole copied interval, not only its first word. *)
val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in kwargDefaultProbe: " ^ name))
  (DB.thms "kwargDefaultProbe");
