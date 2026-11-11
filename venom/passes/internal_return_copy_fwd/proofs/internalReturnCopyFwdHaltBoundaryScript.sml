Theory internalReturnCopyFwdHaltBoundary
Ancestors internalReturnCopyFwdHaltProbe internalReturnCopyFwdSim
  internalReturnCopyFwdDefs venomInst list finite_map reachableFnSim
  ptrDiscipline venomExecSemantics taintAgree o1LowerDloadShared

Theorem ircf_halt_boundary_transform:
  ircf_transform_ctx fn_meta rma ircf_halt_probe_ctx = ircf_halt_probe_ctx
Proof
  simp[ircf_transform_ctx_def, ircf_transform_function_def,
       ircf_halt_probe_ctx_def, ircf_halt_probe_fn_def,
       ircf_halt_probe_bb_def, mk_raw_function_def,
       ircf_transform_block_def, rich_listTheory.COUNT_LIST_GENLIST,
       GENLIST, FOLDL, mk_inst_def]
QED

Theorem ircf_halt_boundary_lookup:
  MEM ircf_halt_probe_fn ircf_halt_probe_ctx.ctx_functions /\
  lookup_function ircf_halt_probe_fn.fn_name ircf_halt_probe_ctx.ctx_functions =
    SOME ircf_halt_probe_fn /\
  lookup_block (ircf_halt_probe_state q b).vs_current_bb
    ircf_halt_probe_fn.fn_blocks = SOME ircf_halt_probe_bb /\
  (ircf_halt_probe_state q b).vs_allocas = FEMPTY
Proof
  EVAL_TAC
QED

Theorem ircf_halt_boundary_reach:
  block_reach (ircf_halt_probe_state q b) ircf_halt_probe_ctx
    [] [] FEMPTY entry_taint ircf_halt_probe_fn (ircf_halt_probe_state q b)
Proof
  rw[block_reach_def] >> irule frame_reachable_entry >>
  simp[ircf_halt_probe_ctx_def, ircf_halt_probe_fn_def,
       ircf_halt_probe_state_def, mk_raw_function_def,
       lookup_function_def, fn_entry_label_def, entry_block_def,
       FIND_thm, ircf_halt_probe_bb_def] >>
  gvs[ircf_halt_probe_fn_def, ircf_halt_probe_bb_def,
      ircf_halt_probe_state_def, mk_raw_function_def]
QED

Theorem ircf_halt_boundary_relation:
  ircf_R D fn_meta rma ircf_halt_probe_ctx [] [] FEMPTY entry_taint
    ircf_halt_probe_fn (ircf_halt_probe_state q b) (ircf_halt_probe_state q c)
Proof
  simp[ircf_R_def, ircf_gam_stk_def, ircf_cross_def,
       ircf_halt_probe_state_def] >>
  simp[taint_agree_def, ircf_halt_probe_state_def] >>
  reverse conj_tac
  >- (Cases_on `q` >> simp[venomStateTheory.venom_state_fn_updates]) >>
  `ld_shared_agree D q.vs_call_ctx.cc_address entry_taint q q`
    by irule ld_shared_agree_refl >>
  gvs[ld_shared_agree_def]
QED

(* These certificates may import the simulation definitions but must not
   inherit any admitted simulation theorem.  Check both oracle and axiom tags. *)
val _ = List.app (fn th =>
  case Tag.dest_tag (Thm.tag th) of
    ([], []) => ()
  | (["DISK_THM"], []) => ()
  | (os, axs) => raise Fail ("Halt boundary tags: oracles=" ^
      String.concatWith "," os ^ "; axioms=" ^ String.concatWith "," axs))
  [ircf_halt_boundary_transform, ircf_halt_boundary_lookup,
   ircf_halt_boundary_reach, ircf_halt_boundary_relation];
