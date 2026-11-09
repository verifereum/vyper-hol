(* This auxiliary relation records the chosen finite prefix, including the
   absence of an earlier endpoint. It is only a graph witness, not a new
   simulation judgment: semantic/source retention is a separate obligation. *)
Theory bodyPtrWordBuiltinsFirstHit
Ancestors fragGasPathPtr bodyPtrDefs arithmetic

Inductive word_ptr_first_hit:
  (!E D lo ctx fn PG G tn s.
    E s /\ ~s.vs_halted ==>
    word_ptr_first_hit E D lo ctx fn PG G tn s 0 G tn s) /\
  (!E D lo ctx fn PG G tn s k H un t n J vn u.
    ~E s /\ gas_path_ptr_edge D lo ctx fn PG G tn s k H un (OK t) /\
    word_ptr_first_hit E D lo ctx fn PG H un t n J vn u ==>
    word_ptr_first_hit E D lo ctx fn PG G tn s (k+n) J vn u)
End

Theorem word_ptr_first_hit_path:
  !E D lo ctx fn PG G tn s n H un t.
    word_ptr_first_hit E D lo ctx fn PG G tn s n H un t ==>
    gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\ E t
Proof
  ho_match_mp_tac word_ptr_first_hit_ind >>
  metis_tac[gas_path_ptr_rules]
QED

Theorem word_ptr_first_hit_decompose:
  !D lo ctx fn PG G tn s n J vn r.
    gas_path_ptr D lo ctx fn PG G tn s n J vn r ==>
    !u E. r = OK u /\ E u ==>
    ?a b H un t.
      n = a+b /\
      word_ptr_first_hit E D lo ctx fn PG G tn s a H un t /\
      gas_path_ptr D lo ctx fn PG H un t b J vn (OK u)
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[word_ptr_first_hit_rules, gas_path_ptr_rules, ADD_0])
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      Cases_on `E s`
      >- (drule word_ptr_first_hit_path >> strip_tac >>
          drule_all gas_path_ptr_then >> strip_tac >>
          `~s.vs_halted` by
            (fs[gas_path_ptr_edge_def]) >>
          qexistsl [`0`, `n+n'`, `G`, `tn`, `s`] >>
          simp[] >> conj_tac
          >- metis_tac[word_ptr_first_hit_rules]
          >> drule (cj 2 gas_path_ptr_rules) >>
          disch_then drule >> simp[AC ADD_ASSOC ADD_COMM])
      >> metis_tac[word_ptr_first_hit_rules, ADD_ASSOC])
  >> rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

(* Equality of the explicit source observations and of the full endpoint
   configuration is sufficient. PC equality alone supplies neither. *)
Theorem word_ptr_first_hit_expr_post_retained:
  word_ptr_first_hit
    (\t. t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
    D 0 ctx func PG G0 tn0 s0 (LENGTH short) H un t /\
  t = u /\ H = G /\ un = tn /\
  gas_explicit short s0.vs_gas_readings =
    gas_explicit marks s0.vs_gas_readings /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v, ee with gas_obs := tail)) /\
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op u /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn u /\
  ptr_val_ok cx (expr_type e) v op G tn u /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at D (ctx, func) PG short
    (bind (eval_expr cx e) (read_result cx)) (es, s0, G0, tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule word_ptr_first_hit_path >> strip_tac >>
  gvs[gas_summary_ptr_at_def] >>
  qexistsl [`INL v`, `ee`, `G`, `tn`, `OK t`] >> simp[] >>
  metis_tac[]
QED

