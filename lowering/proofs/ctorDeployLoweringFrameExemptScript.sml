Theory ctorDeployLoweringFrameExempt
Ancestors
  ctorDeployLoweringDefs supportedProgram vyperTypeSystem e2eDefs
  o1PipelineCorrect concretizeMemLocDefs alist integer_word
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Theorem empty_signed_candidate_supported:
  supported_program
    [FunctionDecl Deploy Payable F F "__init__"
      [("arg",BaseT (BytesT (Dynamic 32)))] [] NoneT
      [AnnAssign "x" (BaseT (IntT 256))
        (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
          [Name (BaseT (BytesT (Dynamic 32))) "arg"]);
       Return NONE]]
Proof
  EVAL_TAC
QED

(* The proposed unwrapped dynamic decoder is outside the supported form. *)
Theorem dynamic_decode_candidate_rejected:
  ~supported_program
    [FunctionDecl Deploy Payable F F "__init__"
      [("arg",BaseT (BytesT (Dynamic 64)))] [] NoneT
      [AnnAssign "x" (BaseT (BytesT (Dynamic 1)))
        (TypeBuiltin (BaseT (BytesT (Dynamic 1))) (AbiDecode T)
          (BaseT (BytesT (Dynamic 1)))
          [Name (BaseT (BytesT (Dynamic 64))) "arg"]);
       Return NONE]]
Proof
  EVAL_TAC
QED

Theorem empty_signed_candidate_typed:
  let env = <| current_src := NONE;
               var_types := FEMPTY |+ ("arg",BaseT (BytesT (Dynamic 32)));
               var_assignable := FEMPTY |+ ("arg",F);
               bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
               toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
               fn_sigs := FEMPTY; flag_members := FEMPTY; event_fields := FEMPTY |> in
  IS_SOME (type_stmts env NoneT
    [AnnAssign "x" (BaseT (IntT 256))
      (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
        [Name (BaseT (BytesT (Dynamic 32))) "arg"]);
     Return NONE])
Proof
  EVAL_TAC
QED

Theorem empty_signed_candidate_lowering:
  IS_SOME
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       lower_vyper_deploy_unit
         [FunctionDecl Deploy Payable F F "__init__"
           [("arg",BaseT (BytesT (Dynamic 32)))] [] NoneT
           [AnnAssign "x" (BaseT (IntT 256))
             (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
               [Name (BaseT (BytesT (Dynamic 32))) "arg"]);
            Return NONE]]
         rp [0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w])
Proof
  EVAL_TAC
QED


Theorem empty_signed_candidate_pipeline:
  IS_SOME
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       case lower_vyper_deploy_unit
         [FunctionDecl Deploy Payable F F "__init__"
           [("arg",BaseT (BytesT (Dynamic 32)))] [] NoneT
           [AnnAssign "x" (BaseT (IntT 256))
             (TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
               [Name (BaseT (BytesT (Dynamic 32))) "arg"]);
            Return NONE]]
         rp [0x5bw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0x5fw;0xf1w;0x00w] of
         NONE => NONE
       | SOME u => checked_unit_pipeline
           o1PipelineCorrect$o1_pipeline (K SOME) rp u)
Proof
  CONV_TAC (RESTR_EVAL_CONV [``checked_unit_pipeline``]) >>
  CONV_TAC (RESTR_EVAL_CONV [``run_callee_first``, ``codegen_assembly``]) >>
  rewrite_tac[venomPipelineRunnerTheory.run_callee_first_def,
              venomPipelineRunnerTheory.run_named_fn_schedules_def] >>
  CONV_TAC (RESTR_EVAL_CONV [``run_configured_fn_pass_fold``, ``codegen_assembly``]) >>
  FAIL_TAC "staged fold entry"
QED
