(* Packaged capacity bounds for singleton dynamic bytes and strings. *)
Theory extRetSingletonCapacityPtr
Ancestors
  returnMetadataPtr vyperABI vyperTypeABI contractABI compileEnv moduleLowering
  moduleLoweringProps vyperTypeSystem vyperContext arithmetic

val _ = Parse.hide "body";

Theorem external_frame_bytes_return_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (BytesT (Dynamic n)),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (BytesT (Dynamic n))) ==>
  next.ce_max_return_size = 64 + contractABI$ceil32 n
Proof
  strip_tac >> drule external_frame_return_size >> rpt (disch_then drule) >>
  simp[needs_external_call_wrap_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, is_dynamic_def, vyper_abi_size_bound_def,
       vyper_is_dynamic_def]
QED

Theorem external_frame_string_return_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (StringT n),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (StringT n)) ==>
  next.ce_max_return_size = 64 + contractABI$ceil32 n
Proof
  strip_tac >> drule external_frame_return_size >> rpt (disch_then drule) >>
  simp[needs_external_call_wrap_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, is_dynamic_def, vyper_abi_size_bound_def,
       vyper_is_dynamic_def]
QED

Theorem external_frame_bytes_live_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (BytesT (Dynamic n)),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (BytesT (Dynamic n))) /\ k <= n ==>
  0 < next.ce_max_return_size /\ 64 + contractABI$ceil32 k <= next.ce_max_return_size
Proof
  strip_tac >> drule_all external_frame_bytes_return_capacity >>
  drule ceil32_mono >> simp[]
QED

Theorem external_frame_string_live_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (StringT n),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (StringT n)) /\ k <= n ==>
  0 < next.ce_max_return_size /\ 64 + contractABI$ceil32 k <= next.ce_max_return_size
Proof
  strip_tac >> drule_all external_frame_string_return_capacity >>
  drule ceil32_mono >> simp[]
QED
