Theory dftPositionalFactor
Ancestors
  dftPositionalEdit relation list rich_list

Definition dft_pos_list_edge_def:
  dft_pos_list_edge R us vs <=>
    ?k v. k < LENGTH us /\ R k (EL k us) v /\
          vs = dft_pos_replace k v us
End


Theorem dft_pos_replace_cons[simp]:
  dft_pos_replace 0 v (h::t) = v::t /\
  dft_pos_replace (SUC k) v (h::t) = h::dft_pos_replace k v t
Proof simp[dft_pos_replace_lupdate, LUPDATE_def]
QED

Theorem dft_pos_list_head[local]:
  RTC (R 0) x y ==>
  RTC (dft_pos_list_edge R) (x::t) (y::t)
Proof
  map_every qid_spec_tac [`y`, `x`] >> ho_match_mp_tac RTC_INDUCT >>
  simp[] >> rpt strip_tac >> irule RTC_TRANS >>
  first_assum (irule_at Any) >> irule RTC_SINGLE >>
  simp[dft_pos_list_edge_def] >> qexistsl [`0`, `x'`] >> simp[]
QED

Theorem dft_pos_list_tail[local]:
  RTC (dft_pos_list_edge (\k. R (SUC k))) xs ys ==>
  RTC (dft_pos_list_edge R) (h::xs) (h::ys)
Proof
  map_every qid_spec_tac [`ys`, `xs`] >> ho_match_mp_tac RTC_INDUCT >>
  simp[] >> rpt strip_tac >> irule RTC_TRANS >>
  first_assum (irule_at Any) >> irule RTC_SINGLE >>
  gvs[dft_pos_list_edge_def] >> qexistsl [`SUC k`, `v`] >> simp[]
QED

Theorem dft_pos_list_factor:
  !xs R ys.
  LENGTH xs = LENGTH ys /\
  (!k. k < LENGTH xs ==> RTC (R k) (EL k xs) (EL k ys)) ==>
  RTC (dft_pos_list_edge R) xs ys
Proof
  Induct >> rpt gen_tac >> Cases_on `ys` >> simp[] >> strip_tac >>
  irule RTC_TRANS >> qexists `h'::xs` >> conj_tac
  >- (irule dft_pos_list_head >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule dft_pos_list_tail >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED

Definition dft_pos_block_swap_def:
  dft_pos_block_swap A j k b b' <=>
    ?pre x y post. b.bb_instructions = pre ++ [x;y] ++ post /\
      A j k pre x y post /\
      b' = b with bb_instructions := pre ++ [y;x] ++ post
End

Definition dft_pos_function_edge_def:
  dft_pos_function_edge A j f g <=>
    ?k b. k < LENGTH f.fn_blocks /\
      dft_pos_block_swap A j k (EL k f.fn_blocks) b /\
      g = f with fn_blocks := dft_pos_replace k b f.fn_blocks
End

Definition dft_pos_context_edge_def:
  dft_pos_context_edge A C D <=>
    ?j k pre x y post.
      j < LENGTH C.ctx_functions /\
      k < LENGTH (EL j C.ctx_functions).fn_blocks /\
      (EL k (EL j C.ctx_functions).fn_blocks).bb_instructions =
        pre ++ [x;y] ++ post /\
      A j k pre x y post /\
      D = dft_pos_edit_ctx j k pre x y post C
End

Theorem dft_pos_blocks_lift[local]:
  !bs cs. RTC (dft_pos_list_edge (dft_pos_block_swap A j)) bs cs ==>
    RTC (dft_pos_function_edge A j)
      (f with fn_blocks := bs) (f with fn_blocks := cs)
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  irule RTC_TRANS >> first_assum (irule_at Any) >> irule RTC_SINGLE >>
  gvs[dft_pos_list_edge_def, dft_pos_function_edge_def] >>
  qexistsl [`k`, `v`] >> simp[]
QED

Theorem dft_pos_function_factor:
  g = f with fn_blocks := g.fn_blocks /\
  LENGTH g.fn_blocks = LENGTH f.fn_blocks /\
  (!k. k < LENGTH f.fn_blocks ==>
    RTC (dft_pos_block_swap A j k) (EL k f.fn_blocks) (EL k g.fn_blocks)) ==>
  RTC (dft_pos_function_edge A j) f g
Proof
  strip_tac >>
  `RTC (dft_pos_list_edge (dft_pos_block_swap A j)) f.fn_blocks g.fn_blocks`
    by (irule dft_pos_list_factor >> simp[]) >>
  drule dft_pos_blocks_lift >> disch_then (qspec_then `f` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem dft_pos_functions_lift[local]:
  !fs gs. RTC (dft_pos_list_edge (dft_pos_function_edge A)) fs gs ==>
    RTC (dft_pos_context_edge A)
      (C with ctx_functions := fs) (C with ctx_functions := gs)
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  irule RTC_TRANS >> first_assum (irule_at Any) >> irule RTC_SINGLE >>
  gvs[dft_pos_list_edge_def, dft_pos_function_edge_def,
      dft_pos_block_swap_def] >>
  simp[dft_pos_context_edge_def, dft_pos_edit_ctx_def, dft_pos_edit_fn_def] >>
  qexistsl [`k`, `k'`, `pre`, `x`, `y`, `post`] >> simp[]
QED

Theorem dft_pos_context_factor:
  D = C with ctx_functions := D.ctx_functions /\
  LENGTH D.ctx_functions = LENGTH C.ctx_functions /\
  (!j. j < LENGTH C.ctx_functions ==>
    let f = EL j C.ctx_functions; g = EL j D.ctx_functions in
      g = f with fn_blocks := g.fn_blocks /\
      LENGTH g.fn_blocks = LENGTH f.fn_blocks /\
      (!k. k < LENGTH f.fn_blocks ==>
        RTC (dft_pos_block_swap A j k) (EL k f.fn_blocks) (EL k g.fn_blocks))) ==>
  RTC (dft_pos_context_edge A) C D
Proof
  strip_tac >>
  `RTC (dft_pos_list_edge (dft_pos_function_edge A))
      C.ctx_functions D.ctx_functions`
    by (irule dft_pos_list_factor >> simp[] >> rpt strip_tac >>
        irule dft_pos_function_factor >> first_x_assum drule >> simp[]) >>
  drule dft_pos_functions_lift >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> metis_tac[]
QED
