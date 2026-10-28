(* TOP-LEVEL: returned pointers originate in source windows or private
   allocations; the canonical empty pointer needs neither. This stronger
   provenance supplies copy-safety bounds as well as memory-read frames. *)
Theory logArgumentOrigins
Ancestors
  logArgumentBacking logArgumentSourceWindows logArgumentSourceTypes
  sourceMemoryFrames abiAllocatedWindows abiWriterFrame allocationGrowth
  valueEncoding compileEnv venomState vyperTypeInvariants vyperState list pair words

Definition argument_origin_def:
  argument_origin cenv scopes ss writers source_ok offset byte_count <=>
    (offset = 0 /\ byte_count = 0) \/
    private_value_window cenv scopes ss writers offset byte_count \/
    (source_ok /\ source_value_window cenv scopes ss offset byte_count)
End

Definition log_args_origins_def:
  log_args_origins cenv scopes ss writers source_ok (args:(operand # type) list) tvs <=>
    LIST_REL (\arg tv. ~is_word_type (SND arg) ==> !src_addr.
      eval_operand (FST arg) ss = SOME src_addr ==>
      argument_origin cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)) args tvs
End

Theorem argument_origin_window:
  !cenv scopes ss writers source_ok offset byte_count.
    argument_origin cenv scopes ss writers source_ok offset byte_count ==>
    argument_value_window cenv scopes ss writers source_ok offset byte_count
Proof
  simp[argument_origin_def, argument_value_window_def] >> rpt strip_tac >> simp[]
QED

Theorem argument_origin_consistent_growth:
  !env cx es es1 cenv before after writers next_writers source_ok next_source offset byte_count.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    argument_origin cenv es.scopes before writers source_ok offset byte_count /\
    allocation_growth before after /\ (!id. MEM id next_writers ==> MEM id writers) /\
    (source_ok ==> next_source) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) ==>
    argument_origin cenv es1.scopes after next_writers next_source offset byte_count
Proof
  rpt gen_tac >> strip_tac >> Cases_on `offset = 0 /\ byte_count = 0` >- simp[argument_origin_def] >>
  qpat_x_assum `argument_origin _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [argument_origin_def]) >>
  asm_simp_tac bool_ss [] >> strip_tac >|
   [`private_value_window cenv es1.scopes after next_writers offset byte_count` by
      (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`, `offset`, `byte_count`]
        mp_tac private_value_window_consistent_growth >>
       impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >> simp[argument_origin_def],
    `source_value_window cenv es1.scopes after offset byte_count` by
      (qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `offset`, `byte_count`]
        mp_tac source_value_window_consistent_frame >>
       impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >> fs[argument_origin_def]]
QED

Theorem log_args_origins_backed:
  !args tvs cenv scopes ss writers source_ok.
    log_args_origins cenv scopes ss writers source_ok args tvs ==>
    log_args_backed cenv scopes ss writers source_ok args tvs
Proof
  rpt gen_tac >> simp_tac bool_ss [log_args_origins_def, log_args_backed_def] >> DISCH_TAC >>
  irule LIST_REL_mono >>
  qexists_tac `\arg tv. ~is_word_type (SND arg) ==> !src_addr.
    eval_operand (FST arg) ss = SOME src_addr ==>
    argument_origin cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)` >> simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `type_memory_size tv` >>
  DISCH_TAC >> qx_gen_tac `src_addr` >> DISCH_TAC >>
  `argument_origin cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)` by
    (first_x_assum irule >> simp[]) >> drule_all argument_origin_window >> simp[]
QED

Theorem log_args_origins_consistent_growth:
  !args tvs env cx es es1 cenv before after writers next_writers source_ok next_source.
    env_scopes_consistent env cx es /\ env_scopes_consistent env cx es1 /\
    log_args_origins cenv es.scopes before writers source_ok args tvs /\ allocation_growth before after /\
    (!id. MEM id next_writers ==> MEM id writers) /\ (source_ok ==> next_source) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before) /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    log_args_origins cenv es1.scopes after next_writers next_source args tvs
Proof
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_origins_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[log_args_origins_def] >>
  rename1 `log_args_origins cenv es.scopes before writers source_ok (arg::rest) (tv::rest_tvs)` >>
  simp_tac (srw_ss()) [log_args_origins_def] >> strip_tac >> conj_tac
  >- (strip_tac >> qx_gen_tac `src_addr` >> DISCH_TAC >>
      `argument_origin cenv es.scopes before writers source_ok (w2n src_addr) (type_memory_size tv)` by
        (qpat_x_assum `~is_word_type _ ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
         disch_then (qspec_then `src_addr` mp_tac) >> simp[]) >>
      qspecl_then [`env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`,
        `source_ok`, `next_source`, `w2n src_addr`, `type_memory_size tv`]
        mp_tac argument_origin_consistent_growth >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `!tvs env cx es es1 cenv before after writers next_writers source_ok next_source. _`
    (qspecl_then [`rest_tvs`, `env`, `cx`, `es`, `es1`, `cenv`, `before`, `after`, `writers`, `next_writers`,
      `source_ok`, `next_source`] mp_tac) >> simp_tac bool_ss [log_args_origins_def] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED

Theorem log_args_origins_snoc:
  !args tvs cenv scopes ss writers source_ok src ty tv.
    log_args_origins cenv scopes ss writers source_ok args tvs /\
    (~is_word_type ty ==> !src_addr. eval_operand src ss = SOME src_addr ==>
      argument_origin cenv scopes ss writers source_ok (w2n src_addr) (type_memory_size tv)) ==>
    log_args_origins cenv scopes ss writers source_ok (args ++ [(src,ty)]) (tvs ++ [tv])
Proof
  simp_tac bool_ss [log_args_origins_def] >>
  Induct_on `args` >- (rpt gen_tac >> Cases_on `tvs` >> simp[]) >>
  rpt gen_tac >> Cases_on `tvs` >> simp_tac (srw_ss()) [] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed returned Log argument pointer origins: " ^ name)
  end) (DB.thms "logArgumentOrigins")
