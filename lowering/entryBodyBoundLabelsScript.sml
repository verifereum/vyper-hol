(* Bound-label interfaces for the external-entry compiler wrappers. *)
Theory entryBodyBoundLabels
Ancestors
  bodyBoundLabels moduleLowering helperBoundLabels boundLabelRules
  compileEnv loweringShapeDefs

Theorem bound_labels_decode_args:
  (!l. compiler_label l ==> P l) ==>
  !xs ce off opc hi adj s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_decode_args ce xs off opc hi adj s))))
Proof
  strip_tac >> Induct >> simp[compile_decode_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_abi_clamp_basetype, cj 1 bound_labels_abi_decode,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[comp_return_def] >>
  rename1 `SOME loc` >> Cases_on `var_location_decode_operand loc` >>
  simp[comp_return_def, bound_labels_emit_void] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    cj 1 bound_labels_abi_decode]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_register_positional_args:
  (!l. compiler_label l ==> P l) ==>
  !xs ce off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_register_positional_args ce xs off s))))
Proof
  strip_tac >> Induct >> simp[compile_register_positional_args_def,
    comp_return_def] >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `var_location_memory_size loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer,
    bound_labels_decode_args, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_guarded_body:
  (!l. compiler_label l ==> P l) ==>
  !ce nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_guarded_body ce nr key trans view body rt s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_guarded_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_nonreentrant_lock,
    bound_labels_nonreentrant_unlock, cj 2 bound_labels_stmt_mutual,
    cj 2 bound_labels_primitives, bound_labels_emit_inst, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `rt` >> simp[bound_labels_emit_inst]
QED

Theorem bound_labels_external_function_body:
  (!l. compiler_label l ==> P l) ==>
  !ce args nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_function_body ce args nr key trans view body rt s))))
Proof
  rpt strip_tac >> simp[compile_external_function_body_def] >>
  irule bound_labels_bind >>
  simp[bound_labels_register_positional_args, bound_labels_guarded_body]
QED

Theorem bound_labels_fallback_body:
  (!l. compiler_label l ==> P l) ==>
  !ce pay nr key trans view body rt s.
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_fallback_body ce pay nr key trans view body rt s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_fallback_body_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_guarded_body,
    bound_labels_emit_op, bound_labels_emit_void, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_entry_checks:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_entry_checks min_cds pay s))))
Proof
  simp[compile_entry_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_emit_void, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_external_fn_bodies:
  (!l. compiler_label l ==> P l) ==>
  !xs s.
    EVERY (\(lbl,ce,args,mc,pay,nr,key,tr,view,body,rt). P lbl) xs /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_external_fn_bodies xs s))))
Proof
  strip_tac >> Induct >> simp[compile_external_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[compile_external_fn_bodies_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_new_block,
    bound_labels_entry_checks, bound_labels_external_function_body]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_selector_checks:
  (!l. compiler_label l ==> P l) ==>
  !xs mid s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_selector_checks mid xs s))))
Proof
  strip_tac >> Induct >> simp[compile_selector_checks_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_selector_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_selector_dispatch_linear:
  (!l. compiler_label l ==> P l) ==>
  !xs fb s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_selector_dispatch_linear xs fb s))))
Proof
  strip_tac >> rpt gen_tac >> simp[compile_selector_dispatch_linear_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block, bound_labels_selector_checks]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_runtime_linear_no_internals:
  (!l. compiler_label l ==> P l) ==>
  !sels exts fb bc mb db ei s.
    EVERY (\(lbl,ce,args,mc,pay,nr,key,tr,view,body,rt). P lbl) exts /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_generate_runtime sels exts [] fb Linear bc mb db ei s))))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_generate_runtime_def, compile_internal_fn_bodies_def] >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_selector_dispatch_linear,
    bound_labels_external_fn_bodies, bound_labels_new_block,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac]) >>
  namedCases_on `fb` ["", "fbody"] >> simp[bound_labels_emit_inst] >>
  PairCases_on `fbody` >>
  simp[bound_labels_fallback_body]
QED
