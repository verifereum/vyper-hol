Theory bodyIntCallReachableTargetMods
Ancestors
  bodyInvMetadataProps contractInvContextProps compileUnit compileEnv
  fragFuel vyperCompiler venomExecSemantics venomInst vyperContext

(* Successful lowering validates every INVOKE in the emitted context.  Apply
   that check at the actual cursor; no source-list inclusion is needed. *)
Theorem decoded_invoke_target[local]:
  lowering_context_ok ctx /\ MEM caller ctx.ctx_functions /\
  lookup_block t.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) ==>
  ?callee. lookup_function lbl ctx.ctx_functions = SOME callee
Proof
  strip_tac >>
  drule_all_then assume_tac lookup_block_get_instruction_fn_insts >>
  drule_then strip_assume_tac lowering_context_ok_integrity >>
  drule_all_then strip_assume_tac invoke_target_resolves_uniquely >>
  gvs[decode_invoke_def] >> goal_assum ACCEPT_TAC
QED

(* The argument metadata fixes the selected formal types.  The decode is
   of the compiler's label for this key, in the emitted caller itself. *)
Theorem selected_invoke_target_at_call_mods:
  contract_inv mods exps ctx cenv cx /\ MEM caller ctx.ctx_functions /\
  key = nsid_to_string (src,name) /\
  cenv.ce_func_param_types key = MAP SND (args : (string # type) list) /\
  lookup_block t.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (lbl,ops) /\
  lbl = internal_fn_label (cenv.ce_func_ids key) key
          (cenv.ce_func_param_types key) cenv.ce_is_ctor ==>
  lbl = internal_fn_label (build_func_ids_mods 0 mods key) key
          (MAP SND args) cx.in_deploy /\
  ?callee. lookup_function lbl ctx.ctx_functions = SOME callee
Proof
  strip_tac >>
  conj_tac
  >- (`cenv.ce_func_ids = build_func_ids_mods 0 mods` by fs[bodyInvSplitTheory.contract_inv_def] >>
      drule_then assume_tac contract_inv_constructor >> simp[]) >>
  drule_then assume_tac contract_inv_lowering_context >>
  irule decoded_invoke_target >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
