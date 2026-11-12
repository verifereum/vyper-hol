(* A local counted-edge exclusion; no source reachability is assumed. *)
Theory bodyPtrStructLitCallPath
Ancestors bodyPtrStructLitCallExclusion fragGasPathPtr

Theorem literal_mload_not_gas_path_ptr_edge:
  !D ctx fn PG G tn s n G' tn' r bb inst a.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = MLOAD /\ inst.inst_operands = [Lit a] /\
    ~in_revert_forward fn s ==>
    ~gas_path_ptr_edge D 0 ctx fn PG G tn s n G' tn' r
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def] >>
  metis_tac[literal_mload_not_ptr_safe_step]
QED

(* Internal-call exclusion diagnostic (current definitions, not old fixture).

   Nested inversion already exists: ptrSafeRun.ptr_safe_step_invoke
   (lines 478-486) states that opcode INVOKE, decode_invoke = SOME(nm,ops),
   lookup_function nm ctx.ctx_functions = SOME callee, eval_operands ops s =
   SOME args and setup_callee callee args s = SOME cs imply the equivalence
     ptr_safe_step D lo fuel ctx fn PG G tn inst s <=>
     ptr_inst_ok D lo fuel ctx fn G tn inst s /\
     ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops)
       FEMPTY (tn with t_var := FEMPTY) cs.
   Reuse it; no duplicate inversion theorem is needed. The callee inherits
   lo and fuel, not necessarily positive fuel. ptr_safe_blocks at zero is T;
   at SUC fuel it checks entry phis then ptr_safe_block at the smaller fuel.
   A nested run is not an outer gas_path_ptr subpath.

   Premise ledger:
   Linkage | body_inv (bodySim:61-87) fixes actual lowered unit/context and
     ce_func_return_type from tops. This alone is not a lookup_function or
     setup_callee success theorem; the call-lowering lookup bridge is needed.
   Reachability | The proposed mandatory literal-frame-load route FAILS on
     current moduleLowering:compile_internal_function (658-721).
     It emits RETPC_PARAM, sets ce_return_pc = SOME(PtrVar return_pc 0),
     and replaces a MemLoc return buffer by a PARAM operand when present.
     Therefore stmtLowering:1042's MLOAD literal belongs to the MemLoc
     branch, whereas linked bodies use the PtrVar branch at 1046.
     The return-buffer literal load at 748 is similarly bypassed by 751.
     No universal mandatory literal load follows for successful linked calls.
   Revert-forward | in_revert_forward is defined in contextCodegenRel:375,
     not ptrDiscipline. Its endpoints must be RETURNDATACOPY or REVERT by
     revert_forward_pair:346-357. Thus an actual MLOAD cannot be an endpoint,
     but that does not manufacture a reachable MLOAD in a linked callee.
   Child instantiation | body_expr_ptr_ok gives both judgments after body_inv
     and expr_body_pre. Instantiating expr_vv_sim_ptr still needs compiler
     equality, code inclusion, distinct IDs, reserved locals, no dalloca,
     nonconstructor, old return variables, gas_admissible, state relation,
     ghost_inv and control position (bodyPtrDefs:296-325). No arbitrary
     machine state from LayoutProbe supplies these. gas_outcome_ptr also
     admits a gas_exempt_cert F alternative (fragGasPathPtr:82); its success
     must be excluded before obtaining a nonempty checked path. Early exits
     and zero-step paths are not contradicted by the theorem above.

   Hence the unproved premise of a proposed successful-call contradiction is
   not just a reachability lemma: it would assert that every linked call
   reaches the obsolete MemLoc return branch. Current prologue definitions
   give no such premise. Do not try to use CallExclusion to remove all calls.
   Next supported representation candidate: declared return
     TupleT [BaseT(BytesT(Dynamic 1)); BaseT(BytesT(Dynamic 1))]
   with call annotation first bound 33, and two empty bytes values. Scalar
   tuple returns are supported; the old tuple containing an array is not.
   A genuine target counterexample still needs supported tops, successful
   lower_vyper_runtime_unit, get_module_code/context typing, exact ce maps,
   legal caller state/ghost, successful evaluation and gas admissibility,
   and the universal body_expr_ptr_ok child premise. None is claimed here.
   Alternatively a positive proof needs a semantic producer interface giving
   robust representation at the lowered type, not solely buffer capacity.
*)
