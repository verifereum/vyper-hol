(* TOP-LEVEL: the actual final LOG instruction appends the requested event
   on a fragment path, without requiring generated SSA names to be undefined. *)
Theory abiLogEmit
Ancestors
  eventEmitProps abiStateFrame exprLoweringProps emitHelperProps compileEnv fragExec fragBlockPath
  venomState venomExecSemantics venomInst list rich_list words

Theorem emit_inst_LOG_path:
  !ctx func cs cs' topic_ops topics offset_op size_op off len ss.
    emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;offset_op]) [] cs = ((),cs') /\
    fn_has_code cs cs' func /\ LENGTH topic_ops < dimword(:256) /\
    eval_operands topic_ops ss = SOME topics /\ eval_operand offset_op ss = SOME off /\
    eval_operand size_op ss = SOME len /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := read_memory (w2n off) (w2n len) ss|>] /\
      out with vs_logs := ss.vs_logs = ss with vs_inst_idx := LENGTH cs'.cs_current_insts /\
      out.vs_memory = ss.vs_memory /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_inst >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  qabbrev_tac `written = ss with vs_logs := ss.vs_logs ++
    [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
       data := read_memory (w2n off) (w2n len) ss|>]` >>
  `run_inst_seq (emitted_insts cs cs') ss = OK written` by
    (asm_simp_tac bool_ss [] >> irule run_inst_seq_sing_ok >>
     mp_tac (Q.SPECL [`cs.cs_next_id`, `topic_ops`, `topics`, `offset_op`, `size_op`, `off`, `len`, `ss`] step_LOG) >>
     simp[Abbr`written`]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`, `written`] fragment_path_emitted) >>
  impl_tac >- (simp[same_blocks_def, mk_inst_def, is_terminator_def]) >> strip_tac >>
  qexists_tac `written with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  gvs[Abbr`written`, venom_state_component_equality] >>
  gen_tac >> Cases_on `arg_op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_state_frame_log_image:
  !original current out index.
    abi_state_frame original current /\
    out with vs_logs := current.vs_logs = current with vs_inst_idx := index ==>
    abi_state_frame original (out with vs_logs := original.vs_logs)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_state_frame_observables >> strip_tac >>
  qpat_x_assum `out with vs_logs := _ = _` (mp_tac o AP_TERM ``abi_state_context``) >>
  fs[abi_state_frame_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual final LOG fragment and external-state frame: " ^ name)
  end) (DB.thms "abiLogEmit")
