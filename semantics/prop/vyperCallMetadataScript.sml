(* Runtime external calls retain the module sources and storage layouts. *)
Theory vyperCallMetadata
Ancestors
  vyperInterpreter vyperState vyperContext vyperValue list pair

Theorem call_external_function_nondeploy_metadata:
  ~cx.in_deploy /\
  call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
    (res,am',rqs) ==>
  am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  strip_tac >>
  fs[call_external_function_def, AllCaseEqs(),
     Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  pairarg_tac >> gvs[] >>
  Cases_on `(do lock_if_nr cx nr (is_view_mut mut);
                 send_call_value mut cx; eval_stmts cx body od)
    (initial_state am [env] with <|outcomes := orc; requests := []; gas_obs := gobs'|>)` >>
  rename1 `(outcome, st)` >> Cases_on `outcome`
  >- gvs[AllCaseEqs(), abstract_machine_from_state_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[AllCaseEqs(), abstract_machine_from_state_def]
QED

Theorem call_external_metadata:
  !orc gobs am tx res am' rqs.
    call_external orc gobs am tx = (res,am',rqs) ==>
    am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  rpt gen_tac >>
  pure_rewrite_tac[call_external_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_at Any call_external_function_nondeploy_metadata >>
  simp[initial_evaluation_context_def]
QED

val () = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn oracle => oracle = "DISK_THM") ors then
       print "CALL_METADATA_AUDIT OK\n"
     else raise Fail "call metadata: admitted proof dependency"
  end) [call_external_function_nondeploy_metadata, call_external_metadata];
