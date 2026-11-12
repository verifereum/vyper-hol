(* Allocation-facing bounds from the arbitrary statement's capacity guard. *)
Theory extRetSingletonWordCapacityPtr
Ancestors
  extRetSingletonCapacityPtr extRetCapacityFramePtr words

val _ = Parse.hide "body";

Overload ceil32[local] = “contractABI$ceil32”

Theorem frame_valued_return_capacity_word_bound:
  stmt_exprs_ok cenv (Return (SOME e)) /\
  cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
  cenv.ce_max_return_size < dimword(:256)
Proof
  strip_tac >> drule_all frame_valued_return_capacity_bound >>
  simp[dimword_def]
QED

Theorem external_frame_bytes_allocator_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (BytesT (Dynamic n)),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (BytesT (Dynamic n))) /\ k <= n /\
  stmt_exprs_ok next (Return (SOME e)) /\
  next.ce_is_external /\ ~next.ce_raw_return ==>
  0 < next.ce_max_return_size /\
  next.ce_max_return_size < dimword(:256) /\
  64 + ceil32 k <= next.ce_max_return_size
Proof
  strip_tac >> drule_all external_frame_bytes_live_capacity >>
  drule_all frame_valued_return_capacity_word_bound >> simp[]
QED

Theorem external_frame_string_allocator_capacity:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,BaseT (StringT n),body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (BaseT (StringT n)) /\ k <= n /\
  stmt_exprs_ok next (Return (SOME e)) /\
  next.ce_is_external /\ ~next.ce_raw_return ==>
  0 < next.ce_max_return_size /\
  next.ce_max_return_size < dimword(:256) /\
  64 + ceil32 k <= next.ce_max_return_size
Proof
  strip_tac >> drule_all external_frame_string_live_capacity >>
  drule_all frame_valued_return_capacity_word_bound >> simp[]
QED
