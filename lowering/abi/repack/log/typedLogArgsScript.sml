(* TOP-LEVEL: saved Log arguments retain their source values, source
   memory footprints and live operand names while fields are packed. *)
Theory typedLogArgs
Ancestors
  valueLoadProps valueEncoding compileEnv venomState venomInst list words arithmetic

Definition log_args_rel_def:
  log_args_rel [] [] [] ss = T /\
  log_args_rel ((src,ty)::ops) (tv::tvs) (v::vs) ss =
    (lowered_value_rel ty tv v src ss /\ log_args_rel ops tvs vs ss) /\
  log_args_rel _ _ _ ss = F
End

Definition log_arg_safe_def:
  log_arg_safe src ty tv ss dst_off byte_count <=>
    ~is_word_type ty ==> !src_addr.
      eval_operand src ss = SOME src_addr ==>
      w2n src_addr + type_memory_size tv < dimword(:256) /\
      (w2n src_addr + type_memory_size tv <= dst_off \/
        dst_off + byte_count <= w2n src_addr)
End

Definition log_args_safe_def:
  log_args_safe [] [] ss dst_off byte_count = T /\
  log_args_safe ((src,ty)::ops) (tv::tvs) ss dst_off byte_count =
    (log_arg_safe src ty tv ss dst_off byte_count /\
      log_args_safe ops tvs ss dst_off byte_count) /\
  log_args_safe _ _ ss dst_off byte_count = F
End

Definition log_args_avoid_def:
  log_args_avoid (ops:(operand # type) list) names <=>
    EVERY (\arg. EVERY (\name. FST arg <> Var name) names) ops
End

Theorem log_arg_safe_operand_frame:
  !src ty tv before after dst_off byte_count.
    eval_operand src after = eval_operand src before ==>
    (log_arg_safe src ty tv after dst_off byte_count =
      log_arg_safe src ty tv before dst_off byte_count)
Proof
  simp[log_arg_safe_def]
QED

Theorem log_arg_safe_subrange:
  !src ty tv ss outer_off outer_size inner_off inner_size.
    log_arg_safe src ty tv ss outer_off outer_size /\
    outer_off <= inner_off /\ inner_off + inner_size <= outer_off + outer_size ==>
    log_arg_safe src ty tv ss inner_off inner_size
Proof
  rpt gen_tac >> simp_tac bool_ss [log_arg_safe_def] >> strip_tac >>
  DISCH_TAC >> qx_gen_tac `src_addr` >> DISCH_TAC >>
  qpat_x_assum `~is_word_type ty ==> _` mp_tac >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspec_then `src_addr` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed saved Log argument predicates: " ^ name)
  end) (DB.thms "typedLogArgs")
