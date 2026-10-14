(* Implementation-boundary compatibility for core relation consumers.
   Normalize ONLY equalities between the same residual mask. The datatype's
   regenerated component equality includes every current (and future) field;
   arbitrary state equalities remain compact for substitution/reconstruction.
   Fetch definitions lazily: this library is loaded while stateEquiv builds. *)
structure stateEquivMaskLib =
struct
open HolKernel boolLib bossLib venomStateTheory

fun mask_name tm =
  case strip_comb tm of
    (c, [_]) =>
      (case total dest_thy_const c of
         SOME {Thy = "stateFrame", Name, ...} =>
           if Name = "state_frame" orelse Name = "execution_frame"
           then SOME Name else NONE
       | _ => NONE)
  | _ => NONE

fun mask_eq_conv tm =
  let
    val (l,r) = dest_eq tm
    val name = case (mask_name l, mask_name r) of
      (SOME n, SOME m) => if n = m then n else raise UNCHANGED
    | _ => raise UNCHANGED
    val def = DB.fetch "stateFrame" (name ^ "_def")
  in
    (REWRITE_CONV [def] THENC
     simpLib.SIMP_CONV (srw_ss()) [venom_state_component_equality]) tm
  end

val _ = BasicProvers.logged_addfrags {thyname = "stateEquiv"}
  [simpLib.conv_ss {name = "core_complete_mask_equality", trace = 2,
    key = SOME ([], ``(s1:venom_state) = s2``),
    conv = K (K mask_eq_conv)}]
end
