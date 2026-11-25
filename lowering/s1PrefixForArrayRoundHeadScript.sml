(* The read and scope push preceding a nonslot array loop body are silent. *)
Theory s1PrefixForArrayRoundHead
Ancestors
  s1PrefixCompose s1PrefixDefs vyperStorageTrace vyperStorageFootprint vyperInterpreter
  vyperState finite_map

Theorem for_array_round_prefix_prepend:
  a = Value v /\
  push_scope_with_var id dtv v es = (INL (),eb) /\
  storage_trace_domain cx st0 eb.storage_trace /\
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (z,J,tz) [] (OK t,Gf,tnf)) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (finally (try (do eval_stmts cx loop_body; return F od)
       handle_loop_exception) pop_scope) (eb,t,Gf,tnf) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (do w <- read_result cx a;
        push_scope_with_var id dtv w;
        finally (try (do eval_stmts cx loop_body; return F od)
          handle_loop_exception) pop_scope od) (es,z,J,tz)
Proof
  strip_tac >>
  qabbrev_tac `clean = finally (try (do eval_stmts cx loop_body; return F od)
    handle_loop_exception) pop_scope` >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 clean (eb,z,J,tz)` by
    (irule gas_prefix_full_zero_prefix_guarded >>
     conj_tac
     >- simp[Abbr `clean`, storage_trace_frame_finally, storage_trace_frame_try,
             storage_trace_frame_ignore_bind, storage_trace_frame_pop_scope,
             storage_trace_frame_loop_handler, storage_trace_frame_return,
             evaluate_storage_trace_frame] >>
     simp[] >> qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[]) >>
  `eb = es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := dtv; value := v; popped := []|>))::es.scopes` by
    gvs[push_scope_with_var_def, return_def, evaluation_state_component_equality] >>
  `!gs. bind (read_result cx (Value v))
       (\w. ignore_bind (push_scope_with_var id dtv w) clean)
       (es with gas_obs := gs) = clean (eb with gas_obs := gs)` by
    (simp[bind_def, ignore_bind_def, read_result_def, return_def,
          push_scope_with_var_def] >>
     gen_tac >> AP_TERM_TAC >> simp[evaluation_state_component_equality]) >>
  qpat_x_assum `gas_prefix_full _ _ _ clean (eb,z,J,tz)` mp_tac >>
  simp[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks` >> simp[] >> metis_tac[]
QED
