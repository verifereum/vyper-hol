Theory ctorDeployLoweringFrameRegion
Ancestors compileVyper concretizeMemLocDefs alist byte integer_word option callTrace
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Theorem pass_ctor_lowering_probe:
  IS_SOME
    (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
      (THE (resolve_o1_policy (o1_policy all_capabilities)))
      [0xf1w; 0xfaw; 0xf0w; 0xf5w])
Proof
  EVAL_TAC
QED

Theorem pass_ctor_data_probe:
  (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
      (THE (resolve_o1_policy (o1_policy all_capabilities)))
      [0xf1w; 0xfaw; 0xf0w; 0xf5w])).cu_data_segment =
  [<| ds_label := "runtime_begin";
      ds_items := [DataBytes [0xf1w; 0xfaw; 0xf0w; 0xf5w]] |>]
Proof
  EVAL_TAC
QED

Theorem pass_ctor_unoptimized_codegen_rejected:
  ~IS_SOME (finalize_codegen (K SOME)
    (THE (resolve_o1_policy (o1_policy all_capabilities)))
    (THE (lower_vyper_deploy_unit
      [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
      (THE (resolve_o1_policy (o1_policy all_capabilities)))
      [0xf1w; 0xfaw; 0xf0w; 0xf5w])))
Proof
  EVAL_TAC
QED

Theorem pass_ctor_pipeline_probe:
  IS_SOME
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       case lower_vyper_deploy_unit
         [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
         rp [0xf1w; 0xfaw; 0xf0w; 0xf5w] of
         NONE => NONE
       | SOME u => checked_unit_pipeline
           (\rp u. run_venom_pipeline (K T) (K T) (K T)
              rp o1_pipeline_spec u) (K SOME) rp u)
Proof
  EVAL_TAC
QED

Theorem pass_ctor_bytes_probe:
    (case resolve_o1_policy (o1_policy all_capabilities) of
       NONE => NONE
     | SOME rp =>
       case lower_vyper_deploy_unit
         [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
         rp [0xf1w; 0xfaw; 0xf0w; 0xf5w] of
         NONE => NONE
       | SOME u => checked_unit_pipeline
           (\rp u. run_venom_pipeline (K T) (K T) (K T)
              rp o1_pipeline_spec u) (K SOME) rp u) = SOME
      [91w; 96w; 4w; 95w; 144w; 129w; 97w; 0w; 19w; 144w; 57w;
       96w; 4w; 144w; 243w; 91w; 95w; 128w; 253w; 241w; 250w; 240w; 245w]
Proof
  EVAL_TAC
QED

