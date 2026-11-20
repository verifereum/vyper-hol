(* Proof helpers for the [cv_pre] and termination goals of the semantics'
   cv translations. The definition theories use them for their own
   translations, so this depends on no theory above vyperMisc. *)
structure vyperCvLib :> vyperCvLib =
struct
  open HolKernel boolLib

  fun pre_constructor_rules tys =
    GSYM AND_IMP_INTRO ::
    List.concat (map (fn ty => #rewrs (TypeBase.simpls_of ty)) tys)

  (* Unwind translator-generated equalities before descending into their
     bodies. In particular, an impossible constructor premise discards its
     whole branch. *)
  fun mk_pre_cleanup_conv rewrites =
    let
      val root = CHANGED_CONV (FIRST_CONV
        [Rewrite.REWRITES_CONV rewrites, Unwind.UNWIND_FORALL_CONV])
      (* Only traverse logical structure: semantic expressions in equality
         premises are opaque. Reduce a false premise before visiting its body. *)
      fun cleanup tm =
        ((root THENC cleanup) ORELSEC
         (if is_forall tm then
            QUANT_CONV cleanup THENC TRY_CONV (root THENC cleanup)
          else if is_imp tm orelse is_conj tm then
            RATOR_CONV (RAND_CONV cleanup) THENC
            ((root THENC cleanup) ORELSEC
             (RAND_CONV cleanup THENC TRY_CONV (root THENC cleanup)))
          else ALL_CONV)) tm
    in cleanup end

  (* Find cv_fst/cv_snd subterms in the goal and add bounds as assumptions.
     Also adds c2n bounds for terms like c2n (cv_fst x). Returns ALL_TAC if
     no terms found. *)
  fun cv_bounds_tac (asl, concl) = let
    val cv_fst_tm = ``cv_fst``
    val cv_snd_tm = ``cv_snd``
    val c2n_tm = ``cv$c2n``
    fun is_cv_proj tm =
      is_comb tm andalso let val (f, _) = dest_comb tm in
        f ~~ cv_fst_tm orelse f ~~ cv_snd_tm
      end
    fun is_c2n tm =
      is_comb tm andalso (rator tm ~~ c2n_tm)
    (* Find all cv_fst/cv_snd projections *)
    fun find_cv_projs tm acc =
      if is_cv_proj tm then
        find_cv_projs (rand tm) (tm :: acc)
      else if is_comb tm then
        find_cv_projs (rator tm) (find_cv_projs (rand tm) acc)
      else acc
    (* Find all c2n applications (any argument, not just projections) *)
    fun find_c2n_projs tm acc =
      if is_c2n tm then (tm :: acc)
      else if is_comb tm then
        find_c2n_projs (rator tm) (find_c2n_projs (rand tm) acc)
      else acc
    val projs = find_cv_projs concl []
    val c2n_projs = find_c2n_projs concl []
    fun mk_proj_bound_tac proj = let
        val (f, a) = dest_comb proj
      in
        if f ~~ cv_fst_tm then
          ASSUME_TAC (SPEC a vyperMiscTheory.cv_size_cv_fst_le)
        else
          ASSUME_TAC (SPEC a vyperMiscTheory.cv_size_cv_snd_le)
      end
    fun mk_c2n_bound_tac c2n_app = let
        val inner = rand c2n_app
      in
        ASSUME_TAC (SPEC inner vyperMiscTheory.c2n_le_cv_size)
      end
    val proj_tacs = map mk_proj_bound_tac projs
    val c2n_tacs = map mk_c2n_bound_tac c2n_projs
    val all_tacs = proj_tacs @ c2n_tacs
  in
    if null all_tacs then ALL_TAC (asl, concl)
    else EVERY all_tacs (asl, concl)
  end
end
