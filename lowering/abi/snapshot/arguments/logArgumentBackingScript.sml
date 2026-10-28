(* TOP-LEVEL: saved arguments use private allocation-backed windows, or
   source-backed windows when the remaining arguments are pure. Backing
   survives source value changes, allocation growth and smaller writer sets.
   Empty footprints require no backing. *)
Theory logArgumentBacking
Ancestors
  logArgumentSourceWindows logArgumentSourceTypes sourceMemoryFrames
  abiAllocatedWindows abiWriterFrame allocationGrowth
  valueEncoding compileEnv venomState vyperTypeInvariants vyperState list pair words

Definition private_value_window_def:
  private_value_window cenv scopes ss writers offset byte_count <=>
    ?owner. ~MEM owner writers /\ abi_allocated_window ss owner offset byte_count /\
      source_memory_separated cenv scopes ss offset byte_count
End

Definition argument_value_window_def:
  argument_value_window cenv scopes ss writers source_ok offset byte_count <=>
    byte_count = 0 \/ private_value_window cenv scopes ss writers offset byte_count \/
    (source_ok /\ source_value_window cenv scopes ss offset byte_count)
End

Definition log_args_backed_def:
  log_args_backed cenv scopes ss writers source_ok (args:(operand # type) list) tvs <=>
    LIST_REL (\arg tv. ~is_word_type (SND arg) ==> !src_addr.
      eval_operand (FST arg) ss = SOME src_addr ==>
      argument_value_window cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)) args tvs
End

Theorem private_value_window_consistent_growth:
  !env cx es es1 cenv before after writers next_writers offset byte_count.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    private_value_window cenv es.scopes before writers offset byte_count /\ allocation_growth before after /\
    (!id. MEM id next_writers ==> MEM id writers) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    private_value_window cenv es1.scopes after next_writers offset byte_count
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `private_value_window _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [private_value_window_def]) >>
  disch_then (qx_choose_then `owner` strip_assume_tac) >>
  `~MEM owner next_writers` by
    (strip_tac >> qpat_x_assum `!id. MEM id next_writers ==> _` drule >> simp[]) >>
  `abi_allocated_window after owner offset byte_count` by (drule_all allocation_growth_window >> simp[]) >>
  qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `offset`, `byte_count`]
    mp_tac source_memory_separated_consistent_scopes >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  simp_tac bool_ss [private_value_window_def] >> qexists_tac `owner` >> simp[]
QED

Theorem argument_value_window_consistent_growth:
  !env cx es es1 cenv before after writers next_writers source_ok next_source offset byte_count.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    argument_value_window cenv es.scopes before writers source_ok offset byte_count /\
    allocation_growth before after /\ (!id. MEM id next_writers ==> MEM id writers) /\
    (source_ok ==> next_source) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    argument_value_window cenv es1.scopes after next_writers next_source offset byte_count
Proof
  rpt gen_tac >> strip_tac >> Cases_on `byte_count = 0` >- simp[argument_value_window_def] >>
  qpat_x_assum `argument_value_window _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [argument_value_window_def]) >> asm_simp_tac bool_ss [] >> strip_tac >|
   [`private_value_window cenv es1.scopes after next_writers offset byte_count` by
      (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`, `offset`, `byte_count`]
        mp_tac private_value_window_consistent_growth >>
       impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
    simp[argument_value_window_def],
    `source_value_window cenv es1.scopes after offset byte_count` by
      (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `offset`, `byte_count`]
        mp_tac source_value_window_consistent_frame >>
       impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
    fs[argument_value_window_def]]
QED

Theorem log_args_backed_consistent_growth:
  !args tvs env cx es es1 cenv before after writers next_writers source_ok next_source.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    log_args_backed cenv es.scopes before writers source_ok args tvs /\ allocation_growth before after /\
    (!id. MEM id next_writers ==> MEM id writers) /\ (source_ok ==> next_source) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    log_args_backed cenv es1.scopes after next_writers next_source args tvs
Proof
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_backed_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[log_args_backed_def] >>
  rename1 `log_args_backed cenv es.scopes before writers source_ok (arg::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_backed_def] >> strip_tac >> conj_tac
  >- (strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_value_window cenv es.scopes before writers source_ok (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type _ ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`,
        `source_ok`, `next_source`, `w2n src_addr`, `type_memory_size tv`]
        mp_tac argument_value_window_consistent_growth >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `!tvs env cx es es1 cenv before after writers next_writers source_ok next_source. _`
    (qspecl_then [`rest_tvs`, `env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`,
      `source_ok`, `next_source`] mp_tac) >>
  simp_tac bool_ss [log_args_backed_def] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED

Theorem log_args_backed_snoc:
  !args tvs cenv scopes ss writers source_ok src ty tv.
    log_args_backed cenv scopes ss writers source_ok args tvs /\
    (~is_word_type ty ==> !src_addr. eval_operand src ss = SOME src_addr ==>
      argument_value_window cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)) ==>
    log_args_backed cenv scopes ss writers source_ok (args ++ [(src,ty)]) (tvs ++ [tv])
Proof
  simp_tac bool_ss [log_args_backed_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_backed_def]) >>
  rpt gen_tac >> Cases_on `tvs` >> simp_tac (srw_ss()) [log_args_backed_def] >>
  strip_tac >> first_x_assum drule_all >> simp[log_args_backed_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed backing of general Log arguments: " ^ name)
  end) (DB.thms "logArgumentBacking")
