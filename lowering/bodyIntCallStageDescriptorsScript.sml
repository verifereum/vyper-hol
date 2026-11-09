(* Preserve source positions when turning the held list into staged values. *)
Theory bodyIntCallStageDescriptors
Ancestors
  bodyIntCallStageBinding bodyIntCallStageOwned vyperState
  list pair

Theorem staged_descriptors_projections:
  !H flags D.
  LENGTH flags = LENGTH H /\
  LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
    ty' = ty /\ flag' = flag /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D ==>
  MAP (\(ty,tv,v,flag,op). ty) D = MAP (\(ty,raw,vv). ty) H /\
  MAP (\(ty,tv,v,flag,op). flag) D = flags /\
  read_results cx (MAP (\(ty,raw,vv). raw) H) es =
    (INL (MAP (\(ty,tv,v,flag,op). v) D),es) /\
  EVERY (\(ty,tv,v,flag,op). evaluate_type (get_tenv cx) ty = SOME tv) D
Proof
  Induct >> rpt gen_tac
  >- (simp[] >> strip_tac >> gvs[read_results_def, return_def]) >>
  PairCases_on `h` >> Cases_on `flags` >> simp[] >>
  namedCases_on `D` ["", "desc descs"] >> simp[] >>
  PairCases_on `desc` >>
  simp[] >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  gvs[read_results_def, bind_def, return_def]
QED

Theorem staged_descriptors_type_sizes:
  !H flags D.
  LENGTH flags = LENGTH H /\
  EVERY (\(ty,raw,vv).
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         type_memory_bytes ce ty = type_memory_size tv) H /\
  LIST_REL (\(ty,raw,vv) flag. flag ==> is_word_type ty) H flags /\
  LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
    ty' = ty /\ flag' = flag /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D ==>
  EVERY (\(ty,tv,v,flag,op).
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (flag ==> is_word_type ty)) D
Proof
  Induct >> rpt gen_tac
  >- (simp[] >> strip_tac >> gvs[]) >>
  PairCases_on `h` >> Cases_on `flags` >> simp[] >>
  namedCases_on `D` ["", "desc descs"] >> simp[] >>
  PairCases_on `desc` >>
  simp[] >> strip_tac >> gvs[] >> first_x_assum irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
