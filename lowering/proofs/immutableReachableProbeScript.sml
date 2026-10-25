(* Reachable constructor padding probes. No arbitrary initial memory. *)
Theory immutableReachableProbe
Ancestors compileVyper immutableConstructorAudit venomExecSemantics
  concretizeMemLocDefs integer_word alist e2eDeployDefs
Libs finite_mapLib computeLib wordsLib intLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos, i2w_def, fmap_to_alist_FEMPTY])

Definition padding_probe_tops_def:
  padding_probe_tops dirty =
    [VariableDecl Private Immutable "X" (BaseT (StringT 40)) NONE;
     FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
       ((if dirty then [AnnAssign "b" (BaseT (StringT 1))
          (Literal (BaseT (StringT 1)) (StringL "b"))] else []) ++
        [Assign (BaseTarget (TopLevelNameTarget (NONE,"X")))
          (Literal (BaseT (StringT 40)) (StringL "a"))]);
     FunctionDecl External Nonpayable F F "get" [] [] (BaseT (StringT 40))
       [Return (SOME (TopLevelName (BaseT (StringT 40)) (NONE,"X")))]]
End

val () = Globals.max_print_depth := 100
Definition padding_probe_unit_def:
 padding_probe_unit dirty = THE (lower_vyper_deploy_unit (padding_probe_tops dirty)
     (THE (resolve_o1_policy (o1_policy all_capabilities))) [])
End
Definition padding_probe_pipeline_def:
 padding_probe_pipeline dirty = run_venom_pipeline (K T) (K T) (K T)
   (THE (resolve_o1_policy (o1_policy all_capabilities))) o1_pipeline_spec
   (padding_probe_unit dirty)
End
Definition padding_probe_execution_def:
 padding_probe_execution dirty = run_context 20
   (THE (padding_probe_pipeline dirty)).po_unit.cu_context
   ((init_venom_state "__deploy") with vs_labels := FEMPTY |+ ("runtime_begin",0w))
End
val dirty_pipeline_eval = EVAL ``padding_probe_pipeline T``
val clean_pipeline_eval = EVAL ``padding_probe_pipeline F``
val () = computeLib.upd_compset (computeLib.add_thms
  [dirty_pipeline_eval, clean_pipeline_eval])

Theorem padding_probe_dirty_reachable:
  case padding_probe_execution T of
    Halt s => s.vs_returndata =
       TAKE 64 (encode_immutable_value (BaseTV (StringT 40)) (StringV "a")) ++
       REPLICATE 31 0w ++ [1w] /\
       DROP 64 (TAKE 96 s.vs_memory) = REPLICATE 31 0w ++ [1w]
  | _ => F
Proof
  EVAL_TAC
QED

Theorem padding_probe_clean_reachable:
  case padding_probe_execution F of
    Halt s => s.vs_returndata =
       encode_immutable_value (BaseTV (StringT 40)) (StringV "a")
  | _ => F
Proof
  EVAL_TAC
QED

Theorem padding_probe_dirty_not_canonical:
  case padding_probe_execution T of
    Halt s => s.vs_returndata <>
       encode_immutable_value (BaseTV (StringT 40)) (StringV "a")
  | _ => F
Proof
  EVAL_TAC
QED

Theorem padding_probe_call_free:
  constructor_call_free (padding_probe_tops T) /\
  constructor_call_free (padding_probe_tops F)
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >> gvs[] >> pop_assum mp_tac >> EVAL_TAC
QED

Theorem padding_probe_checker_accepts:
  IS_SOME (check_contract T [] 0w [(NONE,padding_probe_tops T)]) /\
  IS_SOME (check_contract F [] 0w [(NONE,padding_probe_tops T)]) /\
  IS_SOME (check_contract T [] 0w [(NONE,padding_probe_tops F)]) /\
  IS_SOME (check_contract F [] 0w [(NONE,padding_probe_tops F)])
Proof
  EVAL_TAC
QED

Definition padding_probe_runtime_def:
 padding_probe_runtime = checked_unit_pipeline
   (\rp u. run_venom_pipeline (K T) (K T) (K T) rp o1_pipeline_spec u)
   (K SOME) (THE (resolve_o1_policy (o1_policy all_capabilities)))
   (THE (lower_vyper_runtime_unit (padding_probe_tops T)
     (THE (resolve_o1_policy (o1_policy all_capabilities)))))
End
val runtime_eval = EVAL ``padding_probe_runtime``
val () = computeLib.upd_compset (computeLib.add_thms [runtime_eval])

Definition padding_probe_full_unit_def:
 padding_probe_full_unit = lower_vyper_deploy_unit (padding_probe_tops T)
   (THE (resolve_o1_policy (o1_policy all_capabilities)))
   (THE padding_probe_runtime)
End
Definition padding_probe_full_pipeline_def:
 padding_probe_full_pipeline = run_venom_pipeline (K T) (K T) (K T)
   (THE (resolve_o1_policy (o1_policy all_capabilities))) o1_pipeline_spec
   (THE padding_probe_full_unit)
End
val full_pipeline_eval = EVAL ``padding_probe_full_pipeline``
val () = computeLib.upd_compset (computeLib.add_thms [full_pipeline_eval])

Definition padding_probe_full_execution_def:
 padding_probe_full_execution = run_context 20
   (THE padding_probe_full_pipeline).po_unit.cu_context
   ((init_venom_state "__deploy") with
    <|vs_labels := FEMPTY |+ ("runtime_begin",0w);
      vs_code := THE padding_probe_runtime|>)
End

Theorem padding_probe_compilation_stages_succeed:
  IS_SOME padding_probe_runtime /\ IS_SOME padding_probe_full_unit /\
  IS_SOME padding_probe_full_pipeline
Proof
  EVAL_TAC
QED

Theorem padding_probe_full_deploy_not_canonical:
  case padding_probe_full_execution of
    Halt s => s.vs_returndata = THE padding_probe_runtime ++
       TAKE 64 (encode_immutable_value (BaseTV (StringT 40)) (StringV "a")) ++
       REPLICATE 31 0w ++ [1w] /\
       s.vs_returndata <> THE padding_probe_runtime ++
         encode_immutable_value (BaseTV (StringT 40)) (StringV "a")
  | _ => F
Proof
  EVAL_TAC
QED

(* Execute the actual entry-block prefix, stopping just before the first
   immutable store. This is a trace from the same empty initial memory. *)
Definition padding_probe_before_store_def:
 padding_probe_before_store =
  let ctx = (THE padding_probe_full_pipeline).po_unit.cu_context in
  let insts = (HD (HD ctx.ctx_functions).fn_blocks).bb_instructions in
  FOLDL (\r i. case r of OK s => step_inst 20 ctx i s | _ => r)
    (OK ((init_venom_state "__deploy") with
      <|vs_labels := FEMPTY |+ ("runtime_begin",0w);
        vs_code := THE padding_probe_runtime|>))
    (FST (SPLITP (\i. i.inst_id = 21) insts))
End

Theorem padding_probe_source_slice:
  case padding_probe_before_store of
    OK s => FLOOKUP s.vs_vars "%10" = SOME 96w /\
      read_memory 96 96 s =
        TAKE 64 (encode_immutable_value (BaseTV (StringT 40)) (StringV "a")) ++
        REPLICATE 31 0w ++ [1w]
  | _ => F
Proof
  EVAL_TAC
QED

(* The actual source literal produces a 64-byte temporary even though its
   annotation (and the immutable destination) has capacity 40. *)
Theorem padding_probe_literal_capacity:
  lowered_value_type cenv (Literal (BaseT (StringT 40)) (StringL "a")) =
    BaseT (StringT 1) /\
  type_memory_bytes cenv (BaseT (StringT 1)) = 64
Proof
  EVAL_TAC
QED

Theorem padding_probe_actual_allocation:
  let raw = padding_probe_unit T in
  let fin = (THE padding_probe_full_pipeline).po_unit in
    FIND (\i. i.inst_id = 15)
      (HD (HD raw.cu_context.ctx_functions).fn_blocks).bb_instructions =
       SOME <|inst_id := 15; inst_opcode := ALLOCA;
         inst_operands := [Lit 64w]; inst_outputs := ["%10"]|> /\
    FIND (\i. i.inst_id = 15)
      (HD (HD fin.cu_context.ctx_functions).fn_blocks).bb_instructions =
       SOME <|inst_id := 15; inst_opcode := ASSIGN;
         inst_operands := [Lit 96w]; inst_outputs := ["%10"]|>
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_REACHABLE_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed reachable probe: " ^ name)
  end) (DB.thms "immutableReachableProbe");
