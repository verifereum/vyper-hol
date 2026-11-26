(* Sequence a linked field, its no-gas read/store suffix and the tail. *)
Theory bodyStructFieldConsOutcomeMods
Ancestors
  bodyStructFieldCutsMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasOutcomeFullMods gasStorage fragGasOriginPtr fragGasSeqPtr fragExec
  gasExemptCertMods bodyFullShared stmtSimProps haltExitProj
  exprSimMemorySource exprSimHypsDefs exprSimDefs vyperInterpreter vyperState vyperStorageTrace
  vyperStorageFootprint typeLayoutProps valueEncodingDefs list

(* A pure return-value map does not change the trace, exemption source,
   or physical endpoint of the tail. *)
Triviality cons_return_map:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f
     (es,s,G,tn) Q R /\
  (!H vs ee g ts t. Q H (INL vs) ee g ts t ==> Q' H (INL (v::vs)) ee g ts t) /\
  (!H err ee g ts t. ~Q H (INR err) ee g ts t) /\
  (!H vs ee gt r. ~R H (INL vs) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind f (\vs. return (v::vs))) (es,s,G,tn) Q' R
Proof
  strip_tac >>
  `ignore_bind (bind f (\vs. return (v::vs))) (return ()) =
   ignore_bind f (return ())` by
    simp[ignore_bind_def,bind_assoc,bind_return] >>
  `!x. SND (bind f (\vs. return (v::vs)) x) = SND (f x)` by
    (gen_tac >> Cases_on `f x` >> rename1 `f x = (res,ee)` >>
     Cases_on `res` >> simp[bind_def,return_def]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ f _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      goal_assum (drule_at Any) >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR err => INR err`,
        `ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (gen_tac >> Cases_on `res` >> simp[bind_def,return_def]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      Cases_on `res` >> gvs[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* Take the pure read and the nil-mark machine suffix together, even though
   only the suffix executes instructions. Its path needs only valid horizons. *)
Triviality read_then_fields:
  read_result cx tv mid = (INL v,mid) /\ mid.gas_obs = [] /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_exprs cx es) (\vs. return (v::vs))) (mid,u,G2,tn2) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (read_result cx tv) (\w. bind (eval_exprs cx es) (\vs. return (w::vs))))
    (mid,t,G1,tn1) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`!w. storage_trace_frame (bind (eval_exprs _ _) (\vs. return (w::vs)))`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  qexists_tac `\H res ee g ts s. res = INL v /\ ee = mid /\ g = G2 /\ ts = tn2 /\ s = u` >>
  conj_tac
  >- (qx_genl_tac [`marks`,`res`,`ee`,`g`,`ts`,`s`] >> BETA_TAC >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
        fs[storage_trace_domain_def] >>
      first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
      disj1_tac >> qexists_tac `v` >> simp[]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G2`,`mid`,`INL v`,`u`,`tn2`] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  simp[read_result_gas_obs]
QED

(* Keep the chosen head marks, evaluation, and all-horizon path together
   at the head endpoint. This lets the caller transport reachable headroom
   from that very execution, even after specialising to another horizon. *)
Triviality struct_field_head_path:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f
    (es,s,G,tn) Q R /\
  (!marks res ee g ts t.
     (!tail. f (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
                  (res,ee with gas_obs := tail)) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,g,ts)) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res (ee with gas_obs := []) g ts t) ==>
     !H. valid_horizon cx st0 H ee.storage_trace ==> Q' H res (ee with gas_obs := []) g ts t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f
    (es,s,G,tn) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ f _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> conj_tac
          >- (qexists_tac `marks` >> simp[] >> rpt strip_tac >>
              first_x_assum drule >> gvs[exit_result_def]) >>
          simp[] >> rpt strip_tac >> first_x_assum drule >> gvs[exit_result_def]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The same final post serves the tail and the whole list: only its
   names, evaluated layouts and starting prefix/offset differ. *)
val list_post = ``\names tvs cells off (H : (bool # 256 word # type_value) list # num list) (res : value list + exception) ee g ts z.
  ?vs added. res = INL vs /\ expr_sim_inv_mods mods ce cx env ee /\
    LIST_REL value_has_type tvs vs /\
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) anchor (root,addr,capacity,aid)
      (H,DF H,ee,sb,g,ts,z) (cells ++ added) (off + type_memory_size_list tvs) /\
    (!m. mem_agree_outside ts.t_mem z.vs_memory m ==>
      fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) (addr+off) m)``;

val list_exit = ``\(H : (bool # 256 word # type_value) list # num list) res ee (gt : (string |-> num # num) # taint) r. ?exc. (res : value list + exception) = INR exc /\
  expr_exit (INR exc : eval_result + exception) r /\
  halt_exit H cx ee (INR exc : eval_result + exception) r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Triviality struct_field_read_continuation:
  read_result cx tv mid = (INL v,mid) /\ value_has_type ftv v /\
  mid.gas_obs = [] /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (eval_exprs cx (MAP SND fs)) (mid,u,G2,tn2)
    (^list_post (MAP FST fs) tvs (cells ++ [(ftv,v,addr+off,type_memory_size ftv)])
       (off + type_memory_size ftv)) ^list_exit ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (bind (read_result cx tv)
      (\w. bind (eval_exprs cx (MAP SND fs)) (\vs. return (w::vs)))) (mid,t,G1,tn1)
    (^list_post (fname::MAP FST fs) (ftv::tvs) cells off) ^list_exit
Proof
  BETA_TAC >> strip_tac >> irule read_then_fields >>
  simp[] >> qexistsl_tac [`G2`,`tn2`,`u`] >>
  simp[] >>
  irule cons_return_map >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ _ _` (irule_at Any) >>
  BETA_TAC >> simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qexists_tac `[(ftv,v,addr+off,type_memory_size ftv)] ++ added` >>
  conj_tac >- gvs[typeLayoutPropsTheory.type_memory_size_list_sum,APPEND_ASSOC] >>
  rpt strip_tac >>
  `MEM (ftv,v,addr+off,type_memory_size ftv)
     ((cells ++ [(ftv,v,addr+off,type_memory_size ftv)]) ++ added)` by simp[] >>
  `val_in_memory ftv v (addr+off) m` by
    (drule_all (cj 3 struct_prefix_cell_lookup) >> simp[]) >>
  pure_once_rewrite_tac[valueEncodingDefsTheory.val_in_memory_def] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC]
QED

Theorem struct_field_cons_outcome_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (eval_expr cx e) (es,s,G,tn)
    (\H res ee g ts t. ?tv. res = INL tv /\ HeadQ H tv ee g ts t)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!marks tv mid G1 tn1 t.
    (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL tv,mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> HeadQ H tv mid G1 tn1 t) ==>
    ?v u G2 tn2. read_result cx tv mid = (INL v,mid) /\ value_has_type ftv v /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)) /\
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
        (eval_exprs cx (MAP SND fs)) (mid,u,G2,tn2)
        (\H res ee g ts z. ?vs added. res = INL vs /\
          expr_sim_inv_mods mods ce cx env ee /\ LIST_REL value_has_type tvs vs /\
          struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) anchor (root,addr,capacity,aid)
            (H,DF H,ee,sb,g,ts,z)
            ((cells ++ [(ftv,v,addr+off,type_memory_size ftv)]) ++ added)
            ((off + type_memory_size ftv) + type_memory_size_list tvs) /\
          (!m. mem_agree_outside ts.t_mem z.vs_memory m ==>
            fields_in_memory (ZIP (MAP FST fs,vs)) (ZIP (MAP FST fs,tvs))
              (addr+(off+type_memory_size ftv)) m)) ^list_exit) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (eval_exprs cx (e::MAP SND fs)) (es,s,G,tn)
    (\H res ee g ts z. ?vs added. res = INL vs /\
      expr_sim_inv_mods mods ce cx env ee /\ LIST_REL value_has_type (ftv::tvs) vs /\
      struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) anchor (root,addr,capacity,aid)
        (H,DF H,ee,sb,g,ts,z) (cells ++ added) (off + type_memory_size_list (ftv::tvs)) /\
      (!m. mem_agree_outside ts.t_mem z.vs_memory m ==>
        fields_in_memory (ZIP (fname::MAP FST fs,vs)) (ZIP (fname::MAP FST fs,ftv::tvs))
          (addr+off) m)) ^list_exit
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  pure_rewrite_tac[bind_assoc] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!tv. storage_trace_frame (bind (read_result _ tv) _)`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result] >>
      gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return]) >>
  qexists_tac `\H res mid G1 tn1 t. ?tv. res = INL tv /\
    ?marks. (!tail. eval_expr cx e
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (INL tv,mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> HeadQ H tv mid G1 tn1 t)` >>
  reverse conj_tac >- suspend "head" >>
  suspend "reached"
QED

Resume struct_field_cons_outcome_mods[head]:
  irule struct_field_head_path >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ _) _ _ _` (irule_at Any) >>
  BETA_TAC >> conj_tac >- suspend "head_normal" >>
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  simp[halt_exit_INR_type]
QED

Resume struct_field_cons_outcome_mods[head_normal]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >> gen_tac >> strip_tac >>
  `?tv. res = INL tv /\ HeadQ H tv (mid with gas_obs := []) G1 tn1 t` by
    (first_x_assum drule >> simp[]) >> gvs[] >>
  qexists_tac `marks` >> simp[] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)` by
    (first_x_assum drule >> simp[]) >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_path_ptr_ok_not_halted >> simp[]
QED

Resume struct_field_cons_outcome_mods[reached]:
  qx_genl_tac [`left`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?tv. _` (drule_then strip_assume_tac) >>
  disj1_tac >> qexists_tac `tv` >> asm_rewrite_tac[] >>
  qpat_assum `!marks tv mid G1 tn1 t. _ ==> ?v u G2 tn2. _`
    (qspecl_then [`marks`,`tv`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule (BETA_RULE struct_field_read_continuation) >> simp[] >>
  qexistsl_tac [`G2`,`tn2`,`u`] >> conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ _ _`
    (ACCEPT_TAC o PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC])
QED

Finalise struct_field_cons_outcome_mods
