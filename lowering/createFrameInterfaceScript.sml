Theory createFrameInterface
Ancestors
  list fragExec emitHelperProps builtinCreate rawCreateContractProbe
  vyperCompiler venomState venomExecSemantics venomInst compileEnv emitHelper

(* A live operand carries its VALUE, not just its definedness. In particular,
   salts and constructor-tuple pointers belong in this list. *)
Definition create_live_def:
  create_live live s <=>
    EVERY (\(op,w). eval_operand op s = SOME w) live
End

Definition create_operand_entry_def:
  create_operand_entry cs live s <=>
    fresh_vars_wrt cs s /\ create_live live s
End

Theorem create_live_update_fresh:
  create_operand_entry cs live s /\ cs.cs_next_var <= n ==>
  create_live live (update_var (STRING #"%" (toString n)) w s)
Proof
  rw[create_operand_entry_def, create_live_def, EVERY_MEM] >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  irule eval_operand_update_fresh >> simp[] >>
  qexists_tac `cs` >> simp[]
QED

(* General callback frame: s' may have arbitrary changes to source-owned
   state, but private saved operands retain their original values. Memory
   snapshot framing is a separate obligation, not implied by this frame. *)
Definition create_operand_frame_def:
  create_operand_frame live before after <=>
    create_live live before /\ create_live live after
End

Theorem create_live_frame_trans:
  create_operand_frame live s1 s2 /\
  create_operand_frame live s2 s3 ==>
  create_operand_frame live s1 s3
Proof
  simp[create_operand_frame_def]
QED

Theorem create_operand_entry_rejects_missing_salt:
  ~create_operand_entry (initial_compile_state "entry")
     [(Var "missing_salt", salt)] (init_venom_state "entry")
Proof
  simp[create_operand_entry_def, create_live_def, eval_operand_def,
       lookup_var_def, init_venom_state_def]
QED

(* Typed CFG contract template. The pipeline parameter will be instantiated
   with the callback-driven schedule once that definition exists. entry is
   indexed by the compile state; normal by the returned operand. source_exit
   must match operand/encoding exceptions OR the rof revert with returndata.
   This is a specification, NOT a theorem asserting pipeline correctness. *)
Definition create_pipeline_spec_def:
  create_pipeline_spec ctx (pipeline : operand compiler) entry normal source_exit <=>
    !cs result cs'. pipeline cs = (result,cs') ==>
      cs_extends cs cs' /\
      frag_exec ctx cs cs' (entry cs) (normal result) source_exit
End

(* A scheduled callback gets its ordinary source simulation in source_pre,
   source_normal and source_exit. It is permitted to exit exceptionally;
   no successful evaluation of the callback/pipeline is assumed. Private
   snapshots are supplied by saved and must be framed on NORMAL return. *)
Definition create_callback_spec_def:
  create_callback_spec ctx (callback : operand compiler)
      source_pre source_normal source_exit live saved <=>
    !cs op cs'. callback cs = (op,cs') ==>
      cs_extends cs cs' /\
      frag_exec ctx cs cs'
        (\s. source_pre cs s /\ create_live live s /\ saved s)
        (\s. source_normal op cs' s /\ create_live live s /\ saved s)
        source_exit
End

(* Concrete generated CFG: put a STOP continuation in the current success
   block. REVERSE cs_blocks restores emission order. Neither test runs just
   emitted_insts, which is empty after the final new_block. *)
Definition create_check_probe_fn_def:
  create_check_probe_fn addr =
    let cs = SND (compile_check_create_result (Lit addr) T
                    (initial_compile_state "entry")) in
    <| fn_name := "probe";
       fn_blocks := REVERSE cs.cs_blocks ++
         [<| bb_label := cs.cs_current_bb;
             bb_instructions := cs.cs_current_insts ++
                [mk_inst cs.cs_next_id STOP [] []] |>] |>
End

Theorem create_check_probe_contains_code:
  fn_has_code (initial_compile_state "entry")
    (SND (compile_check_create_result (Lit addr) T
      (initial_compile_state "entry"))) (create_check_probe_fn addr)
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >>
  gvs[] >> rule_assum_tac (CONV_RULE EVAL) >> gvs[] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  simp[Once EQ_SYM_EQ]
QED

(* CFG traversal probes still require bounded execution lemmas; code
   containment alone is deliberately not asserted to imply execution. *)

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createFrameInterface");
