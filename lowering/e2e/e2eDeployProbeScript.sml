Theory e2eDeployProbe
Ancestors e2eDeployChecks compileVyper vfmExecution frameOutcome
  concretizeMemLocDefs alist byte integer_word option
Libs finite_mapLib computeLib wordsLib
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
Definition probe_deploy_bytes_def:
  probe_deploy_bytes : word8 list =
    [91w;96w;38w;95w;144w;129w;97w;0w;19w;144w;57w;96w;38w;144w;243w;
     91w;95w;128w;253w;91w;96w;4w;54w;16w;21w;97w;0w;23w;87w;97w;0w;
     14w;86w;91w;97w;0w;19w;86w;91w;95w;95w;253w;91w;95w;53w;96w;
     224w;28w;80w;97w;0w;19w;86w;91w;95w;128w;253w]
End
Definition probe_runtime_bytes_def:
  probe_runtime_bytes = DROP 19 probe_deploy_bytes
End
Theorem probe_compile_empty:
  compile_vyper (K SOME) (o1_policy all_capabilities) [] =
    SOME (probe_deploy_bytes, probe_runtime_bytes)
Proof
  EVAL_TAC
QED

Definition probe_creation_state_def:
  probe_creation_state s = s with contexts :=
    [(ARB with <|msgParams := ARB with <|code := probe_deploy_bytes;
         parsed := parse_code 0 FEMPTY probe_deploy_bytes;
         outputTo := Code 1w; gasLimit := 1000000; static := F|>;
       pc := 0; stack := []; memory := []; logs := []; returnData := [];
       jumpDest := NONE; gasUsed := 0|>, ARB)]
End
