open Expr

exception Bad_float of float
exception Bad_int of int32
exception Bad_bias

let debug = ref false

let bias_of_expr = function
    Int 0l | Float 0.0 -> TB_zero
  | Float 0.5 -> TB_addhalf
  | Float (-0.5) -> TB_subhalf
  | Int x -> raise (Bad_int x)
  | Float x -> raise (Bad_float x)
  | _ -> raise Bad_bias

exception Bad_cvar of expr

let cvar_of_expr = function
    Var_ref Cprev -> CC_cprev
  | Var_ref Aprev -> CC_aprev
  | Var_ref C0 -> CC_c0
  | Var_ref A0 -> CC_a0
  | Var_ref C1 -> CC_c1
  | Var_ref A1 -> CC_a1
  | Var_ref C2 -> CC_c2
  | Var_ref A2 -> CC_a2
  | Var_ref (K0 | K1 | K2 | K3) -> CC_const
  | Var_ref Texc -> CC_texc
  | Var_ref Texa -> CC_texa
  | Var_ref Rasc -> CC_rasc
  | Var_ref Rasa -> CC_rasa
  | Var_ref Extracted_const -> CC_const
  | Int 1l | Float 1.0 -> CC_one
  | Float 0.5 -> CC_half
  | Int 0l | Float 0.0 -> CC_zero
  | Int x -> raise (Bad_int x)
  | Float x -> raise (Bad_float x)
  | e -> raise (Bad_cvar e)

exception Bad_avar of expr

let avar_of_expr = function
    Var_ref Aprev -> CA_aprev
  | Var_ref A0 -> CA_a0
  | Var_ref A1 -> CA_a1
  | Var_ref A2 -> CA_a2
  | Var_ref Texa -> CA_texa
  | Var_ref Rasa -> CA_rasa
  | Var_ref Extracted_const -> CA_const
  | Int 0l | Float 0.0 -> CA_zero
  | x -> raise (Bad_avar x)

exception Bad_scale

let scale_of_expr = function
    Int 1l | Float 1.0 -> CS_scale_1
  | Int 2l | Float 2.0 -> CS_scale_2
  | Int 4l | Float 4.0 -> CS_scale_4
  | Float 0.5 -> CS_divide_2
  | Int x -> raise (Bad_int x)
  | Float x -> raise (Bad_float x)
  | _ -> raise Bad_scale

(* This maps EXPR using FUNC, before descending into each node.  This allows
   FUNC to map larger subexpressions without first mapping their leaves, when
   FUNC may do a transformation on either.  *)

let map_expr func expr =
  let rec scan e =
    match func e with
      Plus (a, b) -> Plus (scan a, scan b)
    | Minus (a, b) -> Minus (scan a, scan b)
    | Mult (a, b) -> Mult (scan a, scan b)
    | Matmul (a, b) -> Matmul (scan a, scan b)
    | Divide (a, b) -> Divide (scan a, scan b)
    | Modulus (a, b) -> Modulus (scan a, scan b)
    | Vec2 (a, b) -> Vec2 (scan a, scan b)
    | Vec3 (a, b, c) -> Vec3 (scan a, scan b, scan c)
    | S10 a -> S10 (scan a)
    | Neg a -> Neg (scan a)
    | Clamp a -> Clamp (scan a)
    | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
    | Assign (dv, cs, e) -> Assign (dv, cs, scan e)
    | Select (e, lsa) -> Select (scan e, lsa)
    | Concat (e, lsa) -> Concat (scan e, lsa)
    | Ceq (a, b) -> Ceq (scan a, scan b)
    | Cne (a, b) -> Cne (scan a, scan b)
    | Cgt (a, b) -> Cgt (scan a, scan b)
    | Clt (a, b) -> Clt (scan a, scan b)
    | Cgte (a, b) -> Cgte (scan a, scan b)
    | Clte (a, b) -> Clte (scan a, scan b)
    | Or (a, b) -> Or (scan a, scan b)
    | Xor (a, b) -> Xor (scan a, scan b)
    | And (a, b) -> And (scan a, scan b)
    | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
    | Texmap (idx, e) -> Texmap (idx, scan e)
    | Texcoord tc -> Texcoord tc
    | Indscale is -> Indscale is
    | Indmtx im -> Indmtx im
    | D_indmtx (dim, e) -> D_indmtx (dim, scan e)
    | Itexcoord -> Itexcoord
    | Z -> Z
    | Zbits (a, b) -> Zbits (a, scan b)
    | Int i -> Int i
    | Float f -> Float f
    | Var_ref vp -> Var_ref vp
    | CVar cv -> CVar cv
    | Protect e -> e in
  scan expr

let kcsel_of_var = function
    K0 -> KCSEL_K0
  | K1 -> KCSEL_K1
  | K2 -> KCSEL_K2
  | K3 -> KCSEL_K3
  | _ -> failwith "Not KCSEL"

exception Too_many_constants

(* Find special-valued "konst" constants in expression, and separate them
   out.  *)

let rewrite_const expr ~alpha =
  let which_const = ref None in
  let set_const x =
    match !which_const with
      None -> which_const := Some x; Protect (Var_ref Extracted_const)
    | Some foo ->
        if foo <> x then
          raise Too_many_constants
	else
	  Protect (Var_ref Extracted_const) in
  let rec rewrite_fn = function
    Mult (Minus (Int 1l, a), b) ->
      (* Avoid rewriting the "1" in (1-x)*y -- hack!  *)
      Protect (Mult (Minus (Int 1l, map_expr rewrite_fn a),
		     map_expr rewrite_fn b))
  | Float 1.0 | Int 1l when alpha -> set_const KCSEL_1
  | Float 0.875 -> set_const KCSEL_7_8
  | Float 0.75 -> set_const KCSEL_3_4
  | Float 0.625 -> set_const KCSEL_5_8
  | Float 0.5 when alpha -> set_const KCSEL_1_2
  | Float 0.375 -> set_const KCSEL_3_8
  | Float 0.25 -> set_const KCSEL_1_4
  | Float 0.125 -> set_const KCSEL_1_8
  | Var_ref (K0 | K1 | K2 | K3 as k)
  | Select (Var_ref (K0 | K1 | K2 | K3 as k),
	    ([| R; G; B |] | [| R; G; B; _ |])) when not alpha ->
      set_const (kcsel_of_var k)
  | Var_ref (K0 | K1 | K2 | K3 as k)
  | Select (Var_ref (K0 | K1 | K2 | K3 as k),
	    ([| A |] | [| _; _; _; A |])) when alpha ->
      set_const (kcsel_of_var k)
  | Select (Var_ref K0, ([| R; R; R |] | [| R; R; R; _ |])) when not alpha ->
      set_const KCSEL_K0_R
  | Select (Var_ref K1, ([| R; R; R |] | [| R; R; R; _ |])) when not alpha ->
      set_const KCSEL_K1_R
  | Select (Var_ref K2, ([| R; R; R |] | [| R; R; R; _ |])) when not alpha ->
      set_const KCSEL_K2_R
  | Select (Var_ref K3, ([| R; R; R |] | [| R; R; R; _ |])) when not alpha ->
      set_const KCSEL_K3_R
  | Select (Var_ref K0, ([| G; G; G |] | [| G; G; G; _ |])) when not alpha ->
      set_const KCSEL_K0_G
  | Select (Var_ref K1, ([| G; G; G |] | [| G; G; G; _ |])) when not alpha ->
      set_const KCSEL_K1_G
  | Select (Var_ref K2, ([| G; G; G |] | [| G; G; G; _ |])) when not alpha ->
      set_const KCSEL_K2_G
  | Select (Var_ref K3, ([| G; G; G |] | [| G; G; G; _ |])) when not alpha ->
      set_const KCSEL_K3_G
  | Select (Var_ref K0, ([| B; B; B |] | [| B; B; B; _ |])) when not alpha ->
      set_const KCSEL_K0_B
  | Select (Var_ref K1, ([| B; B; B |] | [| B; B; B; _ |])) when not alpha ->
      set_const KCSEL_K1_B
  | Select (Var_ref K2, ([| B; B; B |] | [| B; B; B; _ |])) when not alpha ->
      set_const KCSEL_K2_B
  | Select (Var_ref K3, ([| B; B; B |] | [| B; B; B; _ |])) when not alpha ->
      set_const KCSEL_K3_B
  | Select (Var_ref K0, ([| A; A; A |] | [| A; A; A; _ |])) when not alpha ->
      set_const KCSEL_K0_A
  | Select (Var_ref K1, ([| A; A; A |] | [| A; A; A; _ |])) when not alpha ->
      set_const KCSEL_K1_A
  | Select (Var_ref K2, ([| A; A; A |] | [| A; A; A; _ |])) when not alpha ->
      set_const KCSEL_K2_A
  | Select (Var_ref K3, ([| A; A; A |] | [| A; A; A; _ |])) when not alpha ->
      set_const KCSEL_K3_A
  | Select (Var_ref K0, ([| R |] | [| _; _; _; R |])) when alpha ->
      set_const KCSEL_K0_R
  | Select (Var_ref K1, ([| R |] | [| _; _; _; R |])) when alpha ->
      set_const KCSEL_K1_R
  | Select (Var_ref K2, ([| R |] | [| _; _; _; R |])) when alpha ->
      set_const KCSEL_K2_R
  | Select (Var_ref K3, ([| R |] | [| _; _; _; R |])) when alpha ->
      set_const KCSEL_K3_R
  | Select (Var_ref K0, ([| G |] | [| _; _; _; G |])) when alpha ->
      set_const KCSEL_K0_G
  | Select (Var_ref K1, ([| G |] | [| _; _; _; G |])) when alpha ->
      set_const KCSEL_K1_G
  | Select (Var_ref K2, ([| G |] | [| _; _; _; G |])) when alpha ->
      set_const KCSEL_K2_G
  | Select (Var_ref K3, ([| G |] | [| _; _; _; G |])) when alpha ->
      set_const KCSEL_K3_G
  | Select (Var_ref K0, ([| B |] | [| _; _; _; B |])) when alpha ->
      set_const KCSEL_K0_B
  | Select (Var_ref K1, ([| B |] | [| _; _; _; B |])) when alpha ->
      set_const KCSEL_K1_B
  | Select (Var_ref K2, ([| B |] | [| _; _; _; B |])) when alpha ->
      set_const KCSEL_K2_B
  | Select (Var_ref K3, ([| B |] | [| _; _; _; B |])) when alpha ->
      set_const KCSEL_K3_B
  | Select (Var_ref K0, ([| A |] | [| _; _; _; A |])) when alpha ->
      set_const KCSEL_K0_A
  | Select (Var_ref K1, ([| A |] | [| _; _; _; A |])) when alpha ->
      set_const KCSEL_K1_A
  | Select (Var_ref K2, ([| A |] | [| _; _; _; A |])) when alpha ->
      set_const KCSEL_K2_A
  | Select (Var_ref K3, ([| A |] | [| _; _; _; A |])) when alpha ->
      set_const KCSEL_K3_A
  | x -> x in
  let expr' = map_expr rewrite_fn expr in
  expr', !which_const

let swap_matches a b =
  let min_length = min (Array.length a) (Array.length b) in
  let matching = ref true in
  for i = 0 to min_length - 1 do
    match a.(i), b.(i) with
      (R | G | B | A), X
    | X, (R | G | B | A)
    | X, X -> ()
    | a, b when a = b -> ()
    | _ -> matching := false
  done;
  !matching

let set_swap_don't_cares sel ~alpha =
  match sel with
    [| a |] -> if alpha then [| X; X; X; a |] else [| a; X; X; X |]
  | [| a; b |] -> [| a; b; X; X |]
  | [| a; b; c |] -> [| a; b; c; X |]
  | [| a; b; c; d |] -> [| a; b; c; d |]
  | _ -> failwith "Unexpected swizzles"

type swizzle_info = {
  tex_swaps : lane_select array list;
  ras_swaps : lane_select array list
}

type swizzle_col_alpha_parts = {
  mutable colour_swaps : swizzle_info option;
  mutable alpha_swaps : swizzle_info option;
  mutable merged_tex_swaps : lane_select array option;
  mutable merged_ras_swaps : lane_select array option
}

exception Incompatible_swaps of lane_select array * lane_select array

let rewrite_swap_tables expr swizzles ~alpha =
  let select_cat_var avar cvar swaps lanes =
    let swaps = match swaps with
      Some s -> s
    | None -> failwith "Missing swizzles" in
    if alpha then begin
      match swaps, lanes with
	[| r1; _; _; _ |], ([| r2 |] | [| _; _; _; r2 |]) when r1 = r2 ->
          Concat (Var_ref avar, [| X; X; X; A |])
      | _ -> raise (Incompatible_swaps (swaps, lanes))
    end else begin
      match swaps, lanes with
	[| r1; _; _; _ |], [| r2 |] when r1 = r2 ->
          Concat (Var_ref cvar, [| R |])
      | [| r1; g1; _; _ |], [| r2; g2 |] when r1 = r2 && g1 = g2 ->
          Concat (Var_ref cvar, [| R; G |])
      | [| r1; g1; b1; _ |], [| r2; g2; b2 |] when r1 = r2 && g1 = g2
						   && b1 == b2 ->
          Concat (Var_ref cvar, [| R; G; B |])
      | _ -> raise (Incompatible_swaps (swaps, lanes))
    end in
  let select_sel_var avar cvar swaps lanes =
    let swaps = match swaps with
      Some s -> s
    | None -> failwith "Missing swizzles" in
    if alpha then begin
      match swaps, set_swap_don't_cares lanes ~alpha with
        [| _; _; _; sa |], [| _; _; _; la |] when sa = la -> Var_ref avar
      | _ -> raise (Incompatible_swaps (swaps, lanes))
    end else begin
      match swaps, lanes with
        [| r1; _; _; _ |], [| r2 |] when r1 = r2 ->
          Select (Var_ref cvar, [| r1 |])
      | [| _; _; _; sa |], ([| r; g; b |] | [| r; g; b; _ |])
        when sa = r && r = g && r = b ->
	  Var_ref avar
      | swaps, lanes when swap_matches swaps lanes -> Var_ref cvar
      | _ -> raise (Incompatible_swaps (swaps, lanes))
    end in
  map_expr
    (function 
      Concat (Var_ref Texture, lx) ->
	select_cat_var Texa Texc swizzles.merged_tex_swaps lx
    | Concat (Var_ref Raster, lx) ->
	select_cat_var Rasa Rasc swizzles.merged_ras_swaps lx
    | Select (Var_ref Texture, lx) ->
	select_sel_var Texa Texc swizzles.merged_tex_swaps lx
    | Select (Var_ref Raster, lx) ->
	select_sel_var Rasa Rasc swizzles.merged_ras_swaps lx
    | Var_ref Texture ->
	select_sel_var Texa Texc swizzles.merged_tex_swaps [| R; G; B; A |]
    | Var_ref Raster ->
	select_sel_var Rasa Rasc swizzles.merged_ras_swaps [| R; G; B; A |]
    | x -> x)
    expr

let find_swizzles expr ~alpha =
  let record_swizzle swiz t =
    let t' = set_swap_don't_cares t ~alpha in
    swiz := t' :: !swiz in
  let texswaps = ref []
  and rasswaps = ref [] in
  let tex_swiz = record_swizzle texswaps
  and ras_swiz = record_swizzle rasswaps in
  ignore (map_expr
    (fun node ->
      match node with
	Concat (Var_ref Texture, lx)
      | Select (Var_ref Texture, lx) -> tex_swiz lx; Protect node
      | Concat (Var_ref Raster, lx)
      | Select (Var_ref Raster, lx) -> ras_swiz lx; Protect node
      | Var_ref Texture -> tex_swiz [| R; G; B; A |]; node
      | Var_ref Raster -> ras_swiz [| R; G; B; A |]; node
      | _ -> node)
    expr);
  !texswaps, !rasswaps

type texcoord = S | T | U

type ind_matrix_type =
    T_ind_matrix of int
  | T_no_matrix
  | T_dyn_s
  | T_dyn_t

type indirect_info = {
  (* Settings in GX_SetIndTexOrder.  *)
  mutable ind_texmap : int;
  mutable ind_texcoord : int;
  (* Settings in GX_SetTevIndirect.  *)
  ind_tex_format : int;
  ind_tex_bias : float array;
  ind_tex_matrix : ind_matrix_type;
  ind_tex_scale : int;
  ind_tex_wrap_s : int32 option;
  ind_tex_wrap_t : int32 option;
  ind_tex_addprev : bool;
  ind_tex_unmodified_lod : bool;
  ind_tex_alpha_select : texcoord option;
  
  (* Other settings.  *)
  ind_tex_coordscale : (int * int) option;
}

exception Unrecognized_indirect_texcoord_part of string * expr

let match_tc_maybe_modulus = function
    Texcoord tc -> tc, None
  | Modulus (Texcoord tc, Vec2 (Int m, Int n)) -> tc, Some (m, n)
  | Modulus (Texcoord tc, Int m) -> tc, Some (m, m)
  | x -> raise (Unrecognized_indirect_texcoord_part ("texcoord", x))

let rec plain_float = function
    Int x -> Int32.to_float x
  | Float x -> x
  | Neg x -> -.(plain_float x)
  | x -> raise (Unrecognized_indirect_texcoord_part ("plain_float", x))

let match_bias = function
    Int x -> [| Int32.to_float x; Int32.to_float x; Int32.to_float x |]
  | Float x -> [| x; x; x |]
  | Vec3 (a, b, c) -> [| plain_float a; plain_float b; plain_float c |]
  | x -> raise (Unrecognized_indirect_texcoord_part ("bias", x))

let match_tm_maybe_bias = function
    Texmap (tm, Texcoord tc) -> tm, tc, [| 0.0; 0.0; 0.0 |]
  | Plus (Texmap (tm, Texcoord tc), bias) -> tm, tc, match_bias bias
  | x -> raise (Unrecognized_indirect_texcoord_part ("texmap", x))

let matrix_of_dynmtx = function
    Dyn_S -> T_dyn_s
  | Dyn_T -> T_dyn_t

let matrix_of_staticmtx = function
    Ind_matrix m -> T_ind_matrix m
  | No_matrix -> T_no_matrix

exception Conflicting_texcoords of int * int

let mix_texcoord a b =
  if a = b then a else raise (Conflicting_texcoords (a, b))

let texc_s = function
    Some (s, _) -> Some s
  | None -> None

let texc_t = function
    Some (_, t) -> Some t
  | None -> None

let rec rewrite_indirect_texcoord = function
    Plus ((Texcoord _ | Modulus _ as tc_modulus_or_not),
	  Mult (Matmul (Indmtx im, tm_bias_or_not),
		Indscale is)) ->
      let texcoord, modu = match_tc_maybe_modulus tc_modulus_or_not
      and texmap, itexcoord, bias = match_tm_maybe_bias tm_bias_or_not in
      let ind_info =
        {
	  ind_texmap = texmap;
	  ind_texcoord = itexcoord;
	  ind_tex_format = 8;
	  ind_tex_bias = bias;
	  ind_tex_matrix = matrix_of_staticmtx im;
	  ind_tex_scale = is;
	  ind_tex_wrap_s = texc_s modu;
	  ind_tex_wrap_t = texc_t modu;
	  ind_tex_addprev = false;
	  ind_tex_unmodified_lod = false;
	  ind_tex_alpha_select = None;
	  ind_tex_coordscale = None
        } in
      texcoord, ind_info
  | Plus ((Texcoord _ | Modulus _ as tc_modulus_or_not),
	  Mult (Matmul (D_indmtx (st, Texcoord from_coord), tm_bias_or_not),
		Indscale is)) ->
      let texcoord, modu = match_tc_maybe_modulus tc_modulus_or_not in
      let mixed_texcoord = mix_texcoord texcoord from_coord
      and texmap, itexcoord, bias = match_tm_maybe_bias tm_bias_or_not in
      let ind_info =
        {
	  ind_texmap = texmap;
	  ind_texcoord = itexcoord;
	  ind_tex_format = 8;
	  ind_tex_bias = bias;
	  ind_tex_matrix = matrix_of_dynmtx st;
	  ind_tex_scale = is;
	  ind_tex_wrap_s = texc_s modu;
	  ind_tex_wrap_t = texc_t modu;
	  ind_tex_addprev = false;
	  ind_tex_unmodified_lod = false;
	  ind_tex_alpha_select = None;
	  ind_tex_coordscale = None
        } in
      mixed_texcoord, ind_info
  | Mult (Matmul (Indmtx im, tm_bias_or_not), Indscale is) ->
      let texmap, itexcoord, bias = match_tm_maybe_bias tm_bias_or_not in
      let ind_info =
        {
	  ind_texmap = texmap;
	  ind_texcoord = itexcoord;
	  ind_tex_format = 8;
	  ind_tex_bias = bias;
	  ind_tex_matrix = matrix_of_staticmtx im;
	  ind_tex_scale = is;
	  (* Zero modulus -> zero for the regular texture coords.  *)
	  ind_tex_wrap_s = Some 0l;
	  ind_tex_wrap_t = Some 0l;
	  ind_tex_addprev = false;
	  ind_tex_unmodified_lod = false;
	  ind_tex_alpha_select = None;
	  ind_tex_coordscale = None
        } in
      (* We need a texcoord which is unused, since collisions mean that
         texcoords get scaled incorrectly.  We don't know which texcoord we can
	 use yet, so defer the decision until later.  *)
      -1, ind_info
  | Mult (Matmul (D_indmtx (st, Texcoord from_coord), tm_bias_or_not),
	  Indscale is) ->
      let texmap, itexcoord, bias = match_tm_maybe_bias tm_bias_or_not in
      let ind_info =
        {
	  ind_texmap = texmap;
	  ind_texcoord = itexcoord;
	  ind_tex_format = 8;
	  ind_tex_bias = bias;
	  ind_tex_matrix = matrix_of_dynmtx st;
	  ind_tex_scale = is;
	  (* Zero modulus -> zero for the regular texture coords.  *)
	  ind_tex_wrap_s = Some 0l;
	  ind_tex_wrap_t = Some 0l;
	  ind_tex_addprev = false;
	  ind_tex_unmodified_lod = false;
	  ind_tex_alpha_select = None;
	  ind_tex_coordscale = None
        } in
      from_coord, ind_info
  | Plus (x, Itexcoord) | Plus (Itexcoord, x) ->
      let tm, itc = rewrite_indirect_texcoord x in
      tm, { itc with ind_tex_addprev = true }
  | (Texcoord _ | Modulus _ as tc_modulus_or_not) ->
      let texcoord, modu = match_tc_maybe_modulus tc_modulus_or_not in
      let ind_info =
        {
	  ind_texmap = -1;
	  ind_texcoord = -1;
	  ind_tex_format = 8;
	  ind_tex_bias = [| 0.0; 0.0; 0.0 |];
	  ind_tex_matrix = T_no_matrix;
	  ind_tex_scale = -1;
	  ind_tex_wrap_s = texc_s modu;
	  ind_tex_wrap_t = texc_t modu;
	  ind_tex_addprev = false;
	  ind_tex_unmodified_lod = false;
	  ind_tex_alpha_select = None;
	  ind_tex_coordscale = None
	} in
      texcoord, ind_info
  | x -> raise (Unrecognized_indirect_texcoord_part ("indirect", x))

exception Incompatible_indirect_parts

let merge_indirect a b =
  match a, b with
    None, None -> None
  | Some a, None -> Some a
  | None, Some b -> Some b
  | Some a, Some b when a = b -> Some a
  | _, _ -> raise Incompatible_indirect_parts

exception Incompatible_texmaps
exception Non_simple_texcoord

let rewrite_texmaps expr ~alpha =
  let texmap_texcoord = ref None
  and indirect_stuff = ref None in
  let set_texmap m c =
    match !texmap_texcoord with
      None -> texmap_texcoord := Some (m, c)
    | Some (om, oc) ->
        if om <> m || oc <> c then
	  raise Incompatible_texmaps in
  let rec texmap_rewrite = function
    Select (Texmap (m, Texcoord c), [| A | R | G | B as lane |]) when alpha ->
      set_texmap m c; Protect (Select (Var_ref Texture, [| X; X; X; lane |]))
  | Select (Texmap (m, Texcoord c), [| _; _; _; lane |]) when alpha ->
      set_texmap m c; Protect (Select (Var_ref Texture, [| X; X; X; lane |]))
  | Select (Texmap (m, Texcoord c), lanes) when not alpha ->
      set_texmap m c; Protect (Select (Var_ref Texture, lanes))
  | Texmap (m, Texcoord c) ->
      set_texmap m c; Var_ref Texture
  | Texmap (m, itc) ->
      let plain_texcoord, istuff = rewrite_indirect_texcoord itc in
      indirect_stuff := Some istuff;
      map_expr texmap_rewrite (Texmap (m, Texcoord plain_texcoord))
  | x -> x in
  let expr' = map_expr texmap_rewrite expr in
  expr', !texmap_texcoord, !indirect_stuff

exception Incompatible_colour_channels

let rewrite_colchans expr ~alpha =
  let colchan = ref None in
  let set_colchan c =
    match !colchan with
      None -> colchan := Some c
    | Some oc ->
        if oc <> c then
	  raise Incompatible_colour_channels in
  let expr' = map_expr
    (function
      Select (Var_ref (Chan0 | Chan1 as chan), [| A | R | G | B as lane |])
      when alpha ->
	set_colchan chan; Protect (Select (Var_ref Raster, [| X; X; X; lane |]))
    | Select (Var_ref (Chan0 | Chan1 as chan), [| _; _; _; lane |])
      when alpha ->
	set_colchan chan; Protect (Select (Var_ref Raster, [| X; X; X; lane |]))
    | Select (Var_ref (Chan0 | Chan1 as chan), lanes) when not alpha ->
	set_colchan chan; Protect (Select (Var_ref Raster, lanes))
    | Var_ref (Chan0 | Chan1 as chan) ->
	set_colchan chan; Var_ref Raster
    | Var_ref ColourZero ->
	set_colchan ColourZero;
	if alpha then Protect (Select (Var_ref Raster, [| X; X; X; A |]))
	else Protect (Select (Var_ref Raster, [| R; G; B; X |]))
    | Var_ref AlphaBump ->
	set_colchan AlphaBump;
	Protect (Select (Var_ref Raster, [| X; X; X; A |]))
    | Var_ref AlphaBumpN ->
	set_colchan AlphaBumpN;
	Protect (Select (Var_ref Raster, [| X; X; X; A |])) (* "normalized"? *)
    | x -> x)
    expr in
  expr', !colchan

exception Unmatched_expr

let rec arith_op_of_expr expr ~alpha ac_var_of_expr =
  match expr with
    Assign (dv, _, Mult (Plus
			  (Plus
		            (d, Plus (Mult (Minus (Int 1l, c), a),
				      Mult (c2, b))),
		           tevbias),
			 tevscale)) when c = c2 ->
      Arith { a = ac_var_of_expr a;
              b = ac_var_of_expr b;
	      c = ac_var_of_expr c;
	      d = ac_var_of_expr d;
	      op = OP_add;
	      bias = bias_of_expr tevbias;
	      scale = scale_of_expr tevscale;
	      clamp = false;
	      result = dv }
  | Assign (dv, _, Mult (Plus
			  (Minus
			    (d, Plus (Mult (Minus (Int 1l, c), a),
				      Mult (c2, b))),
		           tevbias),
			 tevscale)) when c = c2 ->
      Arith { a = ac_var_of_expr a;
              b = ac_var_of_expr b;
	      c = ac_var_of_expr c;
	      d = ac_var_of_expr d;
	      op = OP_sub;
	      bias = bias_of_expr tevbias;
	      scale = scale_of_expr tevscale;
	      clamp = false;
	      result = dv }
  | Assign (dv, _, Plus (d, Ternary (Cgt ((Select (Var_ref a, [| R |])
					   | Concat (Var_ref a, [| R |])
					   | Var_ref (Extracted_const as a)),
					  (Select (Var_ref b, [| R |])
					   | Concat (Var_ref b, [| R |])
					   | Var_ref (Extracted_const as b))),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_r8_gt;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Ceq ((Select (Var_ref a, [| R |])
					   | Concat (Var_ref a, [| R |])
					   | Var_ref (Extracted_const as a)),
					  (Select (Var_ref b, [| R |])
					   | Concat (Var_ref b, [| R |])
					   | Var_ref (Extracted_const as b))),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_r8_eq;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Cgt (Concat (a, [| R; G |]),
					  Concat (b, [| R; G |])),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr a;
	     cmp_b = ac_var_of_expr b;
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_gr16_gt;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Ceq (Concat (a, [| R; G |]),
					  Concat (b, [| R; G |])),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr a;
	     cmp_b = ac_var_of_expr b;
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_gr16_eq;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Cgt (Concat (a, [| R; G; B |]),
					  Concat (b, [| R; G; B |])),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr a;
	     cmp_b = ac_var_of_expr b;
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_bgr24_gt;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Ceq (Concat (a, [| R; G; B |]),
					  Concat (b, [| R; G; B |])),
				     c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr a;
	     cmp_b = ac_var_of_expr b;
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_bgr24_eq;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Cgt ((Select (Var_ref a, [| R; G; B |])
					   | Var_ref a),
					  (Select (Var_ref b, [| R; G; B |])
					   | Var_ref b)),
				     c, Int 0l))) when not alpha ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_rgb8_gt;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary (Ceq ((Select (Var_ref a, [| R; G; B |])
					   | Var_ref a),
					  (Select (Var_ref b, [| R; G; B |])
					   | Var_ref b)),
				     c, Int 0l))) when not alpha ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_rgb8_eq;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary
			      (Cgt ((Select (Var_ref a, [| _; _; _; A |])
				     | Concat (Var_ref a, [| _; _; _; A |])
				     | Var_ref a),
				    (Select (Var_ref b, [| _; _; _; A |])
				     | Concat (Var_ref b, [| _; _; _; A |])
				     | Var_ref b)),
			       c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_a8_gt;
	     cmp_result = dv }
  | Assign (dv, _, Plus (d, Ternary
			      (Ceq ((Select (Var_ref a, [| _; _; _; A |])
				     | Concat (Var_ref a, [| _; _; _; A |])
				     | Var_ref a),
				    (Select (Var_ref b, [| _; _; _; A |])
				     | Concat (Var_ref b, [| _; _; _; A |])
				     | Var_ref b)),
			       c, Int 0l))) ->
      Comp { cmp_a = ac_var_of_expr (Var_ref a);
	     cmp_b = ac_var_of_expr (Var_ref b);
	     cmp_c = ac_var_of_expr c;
	     cmp_d = ac_var_of_expr d;
	     cmp_op = CMP_a8_eq;
	     cmp_result = dv }
  | Assign (dv, cs, Clamp expr) ->
      let inner =
        arith_op_of_expr (Assign (dv, cs, expr)) ~alpha ac_var_of_expr in
      begin match inner with
        Arith foo -> Arith { foo with clamp = true }
      | _ -> raise Unmatched_expr
      end
  | _ -> raise Unmatched_expr

let commutative_variants e =
  let rec build_list e all_variants =
    match e with
      Plus (a, b) ->
        let a_list = build_list a []
	and b_list = build_list b [] in
	List.fold_right
	  (fun a_elem a_acc ->
	    List.fold_right
	      (fun b_elem b_acc ->
	        Plus (a_elem, b_elem) :: Plus (b_elem, a_elem) :: b_acc)
	      b_list
	      a_acc)
	  a_list
	  all_variants
    | Mult (a, b) ->
        let a_list = build_list a []
	and b_list = build_list b [] in
	List.fold_right
	  (fun a_elem a_acc ->
	    List.fold_right
	      (fun b_elem b_acc ->
	        Mult (a_elem, b_elem) :: Mult (b_elem, a_elem) :: b_acc)
	      b_list
	      a_acc)
	  a_list
	  all_variants
     | Minus (a, b) ->
        let a_list = build_list a []
	and b_list = build_list b [] in
	List.fold_right
	  (fun a_elem a_acc ->
	    List.fold_right
	      (fun b_elem b_acc ->
	        Minus (a_elem, b_elem) :: b_acc)
	      b_list
	      a_acc)
	  a_list
	  all_variants
     | Divide (a, b) ->
        let a_list = build_list a []
	and b_list = build_list b [] in
	List.fold_right
	  (fun a_elem a_acc ->
	    List.fold_right
	      (fun b_elem b_acc ->
	        Divide (a_elem, b_elem) :: b_acc)
	      b_list
	      a_acc)
	  a_list
	  all_variants
     | Neg a ->
        let a_list = build_list a [] in
	List.fold_right
	  (fun a_elem a_acc -> Neg a_elem :: a_acc)
	  a_list
	  all_variants
     | Clamp a ->
        let a_list = build_list a [] in
	List.fold_right
	  (fun a_elem a_acc -> Clamp a_elem :: a_acc)
	  a_list
	  all_variants
     | Assign (dv, cs, a) ->
        let a_list = build_list a [] in
	List.fold_right
	  (fun a_elem a_acc -> Assign (dv, cs, a_elem) :: a_acc)
	  a_list
	  all_variants
     | x -> [x]
  in
    build_list e []

let default_assign = function
    Assign (dv, cs, x) as d -> d
  | x -> Assign (Tevprev, [| R; G; B; A |], x)

(* Rewrite mix instructions as "(1-c) * a + b * c" and "a < b" as "b > a".  *)

let rec rewrite_mix = function
    Plus (a, b) -> Plus (rewrite_mix a, rewrite_mix b)
  | Minus (a, b) -> Minus (rewrite_mix a, rewrite_mix b)
  | Mult (a, b) -> Mult (rewrite_mix a, rewrite_mix b)
  | Divide (a, b) -> Divide (rewrite_mix a, rewrite_mix b)
  | Neg a -> Neg (rewrite_mix a)
  | Clamp a -> Clamp (rewrite_mix a)
  | Mix (a, b, c) -> Plus (Mult (Minus (Int 1l, rewrite_mix c), rewrite_mix a),
			   Mult (rewrite_mix c, rewrite_mix b))
  | Assign (dv, cs, e) -> Assign (dv, cs, rewrite_mix e)
  | Ceq (a, b) -> Ceq (rewrite_mix a, rewrite_mix b)
  | Cgt (a, b) -> Cgt (rewrite_mix a, rewrite_mix b)
  | Clt (a, b) -> Cgt (rewrite_mix b, rewrite_mix a)
  | Ternary (a, b, c) -> Ternary (rewrite_mix a, rewrite_mix b, rewrite_mix c)
  | x -> x

let int_valued_float x =
  let frac, _ = modf x in
  frac = 0.0

(* Rewrite "tev.xxx" variables as cprev or aprev as appropriate to context.
   Also rewrite cr0, cr1, cr2 as c0/a0/c1/a1/c2/a2 similarly.  *)

let rec rewrite_tev_vars expr ~alpha =
  map_expr
    (function
      Var_ref Tev when not alpha ->
        Var_ref Cprev
    | Var_ref Tev when alpha ->
        Var_ref Aprev
    | Select (Var_ref Tev, ([| R; G; B |] | [| R; G; B; _ |])) when not alpha ->
        Var_ref Cprev
    | Select (Var_ref Tev, ([| A |] | [| A; A; A |] | [| A; A; A; _ |]))
      when not alpha ->
        Var_ref Aprev
    | Select (Var_ref Tev, ([| A |] | [| _; _; _; A |])) when alpha ->
        Var_ref Aprev
    | (Var_ref (CR n)
       | Select (Var_ref (CR n), ([| R; G; B |] | [| R; G; B; _ |])))
      when not alpha ->
        begin match n with
	  0 -> Var_ref C0
	| 1 -> Var_ref C1
	| 2 -> Var_ref C2
	| _ -> failwith "Unexpected colour register"
	end
    | Select (Var_ref (CR n), ([| A |] | [| A; A; A; _ |])) when not alpha ->
        begin match n with
	  0 -> Var_ref A0
	| 1 -> Var_ref A1
	| 2 -> Var_ref A2
	| _ -> failwith "Unexpected colour register"
	end
    | (Var_ref (CR n) | Select (Var_ref (CR n), ([| _; _; _; A |] | [| A |])))
      when alpha ->
        begin match n with
	  0 -> Var_ref A0
	| 1 -> Var_ref A1
	| 2 -> Var_ref A2
	| _ -> failwith "Unexpected colour register"
	end
    | x -> x)
    expr

(* Rewrite "/ 2" as "* 0.5", integer-valued floats as ints, and rationals as
   floats.  *)

let rewrite_rationals expr =
  let rec rewrite_fn = function
    Divide (Float a, Float b) -> Float (a /. b)
  | Divide (Int a, Int b) -> Float (Int32.to_float a /. Int32.to_float b)
  | Divide (Float a, Int b) -> Float (a /. Int32.to_float b)
  | Divide (Int a, Float b) -> Float (Int32.to_float a /. b)
  | Divide (a, (Int 2l | Float 2.0)) -> Mult (map_expr rewrite_fn a, Float 0.5)
  | Float x when int_valued_float x -> Int (Int32.of_float x)
  | x -> x in
  map_expr rewrite_fn expr

(* Things which are (probably) valid TEV inputs.  In particular not certain
   integers used for scale values, etc.  *)

let valid_tev_input = function
    Var_ref _ -> true
  | Float _ -> true
  | Int 0l | Int 1l -> true
  | Select _ -> true
  | Concat _ -> true
  | _ -> false

(* We can probably support a few more useful cases here.  *)

let rewrite_blend_expr = function
    (Var_ref _ | Int _ | Float _ as x) when valid_tev_input x ->
      Plus (Mult (Minus (Int 1l, Int 0l), x), Mult (Int 0l, Int 0l))
  | Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))
      when c = c2 && valid_tev_input a && valid_tev_input b
	   && valid_tev_input c ->
      Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))
  | Mult (a, b) when valid_tev_input a && valid_tev_input b->
      Plus (Mult (Minus (Int 1l, a), Int 0l), Mult (a, b))
  | Minus (Int 1l, a) when valid_tev_input a ->
      Plus (Mult (Minus (Int 1l, a), Int 1l), Mult (a, Int 0l))
  | e -> e  (* This is basically giving up...  *)

let rewrite_ternary_expr = function
    Ternary (a, b, c) -> Ternary (a, b, c)
  | _ -> raise Not_found

(* Rewrite expressions which accumulate (sign+10 bit) values, unaccumulate
   values, or no accumulation.  I think there's some possible ambiguity with
   the blend part of the expression, but the blend expression is only
   calculated to unsigned 8-bit precision.  *)
let rewrite_accumulate_expr acc_child = function
    Plus (S10 (Var_ref _ | Int _ | Float _ | Select _ as a), b)
      when valid_tev_input a ->
      Plus (a, acc_child b)
  | Minus (S10 (Var_ref _ | Int _ | Float _ | Select _ as a), b)
      when valid_tev_input a ->
      Minus (a, acc_child b)
  | S10 (Var_ref _ | Int _ | Float _ | Select _ as item)
    when valid_tev_input item ->
      Plus (item, acc_child (Int 0l))
  | Plus ((Var_ref _ | Int _ | Float _ as a), b) when valid_tev_input a ->
      Plus (a, acc_child b)
  | Minus ((Var_ref _ | Int _ | Float _ as a), b) when valid_tev_input a ->
      Minus (a, acc_child b)
  | (Var_ref _ | Int _ | Float _ as item) when valid_tev_input item ->
      Plus (item, acc_child (Int 0l))
  | e ->
      Plus (Int 0l, acc_child e)

(* Match expressions biasing TEV operation by -0.5/0.5, and also zero biases
   or no bias at all.  *)
let rewrite_bias_expr = function
    Plus (e, (Float 0.5 | Int 0l | Float (-0.5) as bias)) ->
      Plus (rewrite_accumulate_expr rewrite_blend_expr e, bias)
  | Minus (e, (Float (0.5 as amt) | Float (-0.5 as amt))) ->
      Plus (rewrite_accumulate_expr rewrite_blend_expr e, Float (-. amt))
  | Minus (e, Int 0l) ->
      Plus (rewrite_accumulate_expr rewrite_blend_expr e, Int 0l)
  | e ->
      Plus (rewrite_accumulate_expr rewrite_blend_expr e, Int 0l)

(* Match valid expressions for scaling the final TEV result, or add a unit
   scale if one is missing.  *)
let rewrite_scale_expr = function
    Mult (e, (Int 1l | Int 2l | Int 4l | Float 0.5 as factor)) ->
      Mult (rewrite_bias_expr e, factor)
  | e -> Mult (rewrite_bias_expr e, Int 1l)

(* Match a clamp expression, or a lack of one.  *)
let rewrite_clamp_expr = function
    Clamp e -> Clamp (rewrite_scale_expr e)
  | e -> rewrite_scale_expr e

(* FIXME: The "D" input has more significant bits than the A, B and C inputs:
   10-bit signed versus 8-bit unsigned.  This rewriting function doesn't really
   understand that, so we may lose precision.  This will be fixed by
   introducing new syntax:

     s10(tev) + ...

   where signed+10bit values are required.  *)
   
let rewrite_expr expr =
  try
    rewrite_accumulate_expr rewrite_ternary_expr expr
  with Not_found ->
    rewrite_clamp_expr expr

let string_of_var_param = function
    Tev -> "tev"
  | CR n -> "cr" ^ (string_of_int n)
  | Cprev -> "cprev"
  | Aprev -> "aprev"
  | C0 -> "c0"
  | A0 -> "a0"
  | C1 -> "c1"
  | A1 -> "a1"
  | C2 -> "c2"
  | A2 -> "a2"
  | K0 -> "k0"
  | K1 -> "k1"
  | K2 -> "k2"
  | K3 -> "k3"
  | Chan0 -> "chan0"
  | Chan1 -> "chan1"
  | Colour0 -> "colour0"
  | Alpha0 -> "alpha0"
  | Colour0A0 -> "colour0a0"
  | Colour1 -> "colour1"
  | Alpha1 -> "alpha1"
  | Colour1A1 -> "colour1a1"
  | ColourZero -> "colourzero"
  | AlphaBump -> "alphabump"
  | AlphaBumpN -> "alphabumpn"
  | Texc -> "texc"
  | Texa -> "texa"
  | Rasc -> "rasc"
  | Rasa -> "rasa"
  | Texture -> "texture"
  | Raster -> "raster"
  | Extracted_const -> "extracted_const"

let string_of_laneselect lsa ~reverse =
  Array.fold_left
    (fun acc lane -> match lane with
       R -> if reverse then "r" ^ acc else acc ^ "r"
     | G -> if reverse then "g" ^ acc else acc ^ "g"
     | B -> if reverse then "b" ^ acc else acc ^ "b"
     | A -> if reverse then "a" ^ acc else acc ^ "a"
     | LS_S -> if reverse then "s" ^ acc else acc ^ "s"
     | LS_T -> if reverse then "t" ^ acc else acc ^ "t"
     | X -> if reverse then "?" ^ acc else acc ^ "?")
    ""
    lsa

let string_of_destvar = function
    Tevprev -> "tevprev"
  | Tevreg0 -> "tevreg0"
  | Tevreg1 -> "tevreg1"
  | Tevreg2 -> "tevreg2"
  | Itexc_dst -> "itexcoord"
  | Z_dst -> "z"
  | Alpha_pass -> "alpha_pass"

let string_of_indmtx = function
    Ind_matrix i -> "indmtx" ^ string_of_int i
  | No_matrix -> "no_matrix"

let string_of_expression expr =
  let b = Buffer.create 20 in
  let rec add_binop x op y =
    Buffer.add_char b '(';
    scan x;
    Buffer.add_string b op;
    scan y;
    Buffer.add_char b ')'
  and scan = function
    Int i -> Buffer.add_string b (Int32.to_string i)
  | Float f -> Buffer.add_string b (string_of_float f)
  | Plus (a, b) -> add_binop a " + " b
  | Minus (a, b) -> add_binop a " - " b
  | Mult (a, b) -> add_binop a " * " b
  | Divide (a, b) -> add_binop a " / " b
  | Matmul (a, b) -> add_binop a " ** " b
  | Modulus (a, b) -> add_binop a " % " b
  | Var_ref r -> Buffer.add_string b (string_of_var_param r)
  | CVar c ->
      Buffer.add_char b '$';
      Buffer.add_string b c
  | Neg a -> Buffer.add_string b "-("; scan a; Buffer.add_char b ')'
  | Clamp a -> Buffer.add_string b "clamp("; scan a; Buffer.add_char b ')'
  | Mix (x, y, z) ->
      Buffer.add_string b "mix("; scan x; Buffer.add_char b ','; scan y;
      Buffer.add_char b ','; scan z; Buffer.add_char b ')'
  | Vec2 (x, y) ->
      Buffer.add_string b "vec2("; scan x; Buffer.add_char b ','; scan y;
      Buffer.add_char b ')'
  | Vec3 (x, y, z) ->
      Buffer.add_string b "vec3("; scan x; Buffer.add_char b ','; scan y;
      Buffer.add_char b ','; scan z; Buffer.add_char b ')'
  | S10 x ->
      Buffer.add_string b "s10("; scan x; Buffer.add_char b ')'
  | Assign (dv, lsa, e) ->
      Buffer.add_string b (string_of_destvar dv);
      Buffer.add_char b '.';
      Buffer.add_string b (string_of_laneselect lsa ~reverse:false);
      Buffer.add_string b "=";
      scan e
  | Ceq (a, b) -> add_binop a " == " b
  | Cne (a, b) -> add_binop a " != " b
  | Cgt (a, b) -> add_binop a " > " b
  | Clt (a, b) -> add_binop a " < " b
  | Cgte (a, b) -> add_binop a " >= " b
  | Clte (a, b) -> add_binop a " <= " b
  | And (a, b) -> add_binop a " && " b
  | Or (a, b) -> add_binop a " || " b
  | Xor (a, b) -> add_binop a " ^ " b
  | Select (e, lsa) ->
      scan e;
      Buffer.add_char b '.';
      Buffer.add_string b (string_of_laneselect lsa ~reverse:false)
  | Concat (e, lsa) ->
      scan e;
      Buffer.add_char b '{';
      Buffer.add_string b (string_of_laneselect lsa ~reverse:true);
      Buffer.add_char b '}'
  | Ternary (x, y, z) ->
      scan x;
      Buffer.add_string b " ? ";
      scan y;
      Buffer.add_string b " : ";
      scan z
  | Texmap (x, y) ->
      Buffer.add_string b (Printf.sprintf "texmap%d[" x);
      scan y;
      Buffer.add_char b ']'
  | Texcoord t -> Buffer.add_string b ("texcoord" ^ string_of_int t)
  | Indmtx i -> Buffer.add_string b (string_of_indmtx i)
  | D_indmtx (Dyn_S, e) ->
      Buffer.add_string b "s_dynmtx(";
      scan e;
      Buffer.add_char b ')'
  | D_indmtx (Dyn_T, e) ->
      Buffer.add_string b "t_dynmtx(";
      scan e;
      Buffer.add_char b ')'
  | Indscale s -> Buffer.add_string b ("indscale" ^ string_of_int s)
  | Itexcoord -> Buffer.add_string b "itexcoord"
  | Z -> Buffer.add_char b 'z'
  | Zbits (bits, e) ->
      Buffer.add_string b (Printf.sprintf "zbits(%d," bits);
      scan e;
      Buffer.add_char b ')'
  | Protect e ->
      Buffer.add_string b "protect(";
      scan e;
      Buffer.add_char b ')' in
  scan expr;
  Buffer.contents b

type ztex_fmt = Z8 | Z16 | Z24x8

type ztex_operation = Ztex_add | Ztex_replace

type int_cst_or_cvar =
    Int_cst of int
  | Int_cvar of string

type ztex_info = {
  ztex_fmt : ztex_fmt;
  ztex_offset : int_cst_or_cvar;
  ztex_operation : ztex_operation;
  ztex_texmap_texc : int * int
}

type alphatest_combine = Acomb_or | Acomb_and | Acomb_xor | Acomb_xnor

type alphatest_cmp = Acmp_never | Acmp_less | Acmp_equal | Acmp_lequal
		   | Acmp_greater | Acmp_nequal | Acmp_gequal | Acmp_always

type alphatest_comparison = {
  acmp_op : alphatest_cmp;
  acmp_val : int_cst_or_cvar
}

type alphatest_info = {
  atest_cmp1 : alphatest_comparison;
  atest_combine : alphatest_combine;
  atest_cmp2 : alphatest_comparison
}

type 'ac stage_info = {
  stage_operation : 'ac tev;
  const_usage : const_setting option;
  mutable texmap_texc : (int * int) option;
  indirect : indirect_info option;
  colchan: var_param option
}

(* Direct texmap & texcoord used by indirect "texcoord-only" operations: some
   of this (which texmap to use) is implicit, and must be filled in
   automatically by tevsl.  *)

type tex_info = {
  mutable ind_dir_texcoord : int;
  mutable ind_dir_texmap : int option;
  mutable ind_dir_nullified : bool
}

type stage_col_alpha_parts = {
  mutable ind_texc_part : indirect_info option;
  mutable ind_direct_tex_part : tex_info option;
  mutable colour_part : cvar_setting stage_info option;
  mutable alpha_part : avar_setting stage_info option;
  mutable ztex_part : ztex_info option
}

let parse_channel c =
  let sbuf = Lexing.from_channel c in
  Parser.stage_defs Lexer.token sbuf

let num_stages stage_defs =
  List.fold_right
    (fun stagetype acc ->
      match stagetype with
        Regular_stage (sn, _) -> if sn + 1 > acc then sn + 1 else acc
      | _ -> acc)
    stage_defs
    0

let print_num_stages oc ns =
  Printf.fprintf oc "GX_SetNumTevStages (%d);\n" ns

(* If there are no colour channels, at least one texture coordinate must be
   generated.  Enforce that here.  *)
let print_num_channels oc colchans texchans =
  let colchans', texchans' =
    match colchans, texchans with
      0, 0 -> 0, 1
    | c, _ when c > 2 -> failwith "Too many colour channels"
    | _, t when t > 8 -> failwith "Too many texture coordinates"
    | c, t -> c, t in
  Printf.fprintf oc "GX_SetNumChans (%d);\n" colchans';
  Printf.fprintf oc "GX_SetNumTexGens (%d);\n" texchans'

let swizzle_for_expr orig_expr ~alpha =
  let expr, _, _ = rewrite_texmaps orig_expr ~alpha in
  let expr, _ = rewrite_colchans expr ~alpha in
  let texswaps, rasswaps = find_swizzles expr ~alpha in
  { tex_swaps = texswaps; ras_swaps = rasswaps }

(* A pre-pass to gather swizzles.  We can't resolve these with purely local
   information, e.g. per-expression.  We need to do it using all the information
   from a stage at a time.  *)

let array_of_swizzles stage_defs ns =
  let arr = Array.init ns
    (fun _ -> { colour_swaps = None; alpha_swaps = None;
		merged_tex_swaps = None; merged_ras_swaps = None }) in
  List.iter
    (function
	Regular_stage (sn, stage_exprs) ->
	  List.iter
            (fun stage_expr ->
	      let stage_expr = default_assign stage_expr in
        	match stage_expr with
		  Assign (_, [| A |], _) ->
	            let swiz = swizzle_for_expr stage_expr ~alpha:true in
		    arr.(sn).alpha_swaps <- Some swiz
		| Assign (_, [| R; G; B |], _) ->
	            let swiz = swizzle_for_expr stage_expr ~alpha:false in
		    arr.(sn).colour_swaps <- Some swiz
		| Assign (_, [| R; G; B; A |], _) ->
	            let cswiz = swizzle_for_expr stage_expr ~alpha:false
		    and aswiz = swizzle_for_expr stage_expr ~alpha:true in
		    arr.(sn).alpha_swaps <- Some aswiz;
		    arr.(sn).colour_swaps <- Some cswiz
		| Assign (Itexc_dst, [| LS_S; LS_T |], e) -> ()
		| Assign (Z_dst, [||], _) -> ()
		| _ -> failwith "Bad stage expression")
	    stage_exprs
      | _ -> ())
    stage_defs;
  arr

(* Hmm... this seems a little overwrought.  Turn chan0/chan1 into COLOR0 or
   ALPHA0 or COLOR0A0, etc. hardware registers depending on swizzles.  *)

let remap_colchan swizzle colchan =
  match swizzle, colchan with
    [| _; _; _; X |], Some Chan0 -> Some Colour0
  | [| _; _; _; X |], Some Chan1 -> Some Colour1
  | [| X; X; X; A |], Some Chan0 -> Some Alpha0
  | [| X; X; X; A |], Some Chan1 -> Some Alpha1
  | _, Some Chan0 -> Some Colour0A0
  | _, Some Chan1 -> Some Colour1A1
  | _, x -> x

exception Can't_match_stage of int

let compile_expr stage orig_expr swiz ~alpha ac_var_of_expr =
  if !debug then
    Printf.fprintf stderr "stage %d, compile_expr: %s channel\n" stage
		   (if alpha then "alpha" else "colour");
  let expr = rewrite_tev_vars orig_expr ~alpha in
  let expr = rewrite_rationals expr in
  let expr = rewrite_mix expr in
  let expr, const_extr = rewrite_const expr ~alpha in
  if !debug then
    Printf.fprintf stderr "rewrite_const: %s\n" (string_of_expression expr);
  let expr, texmap_texcoord, indtex = rewrite_texmaps expr ~alpha in
  if !debug then
    Printf.fprintf stderr "rewrite_texmaps: %s\n" (string_of_expression expr);
  let expr, colchan = rewrite_colchans expr ~alpha in
  if !debug then
    Printf.fprintf stderr "rewrite_colchans: %s\n" (string_of_expression expr);
  let colchan =
    match swiz.merged_ras_swaps with
      Some ras_swaps -> remap_colchan ras_swaps colchan
    | None -> colchan in
  let expr = rewrite_swap_tables expr swiz ~alpha in
  if !debug then
    Printf.fprintf stderr "rewrite_swap_tables: %s\n"
		   (string_of_expression expr);
  let comm_variants = commutative_variants expr in
  let matched = List.fold_right
    (fun variant found ->
      match found with
        Some x as y -> y
      | None ->
          try
	    match variant with
	      Assign (dv, cs, expr) ->
	        let expr' = rewrite_expr expr in
                Some (stage,
		      arith_op_of_expr (Assign (dv, cs, expr')) ~alpha
				       ac_var_of_expr)
	    | _ -> raise Unmatched_expr
	  with Unmatched_expr ->
	    None)
    comm_variants
    None in
  match matched with
    Some (stagenum, tevop) ->
      {
	stage_operation = tevop;
	const_usage = const_extr;
	texmap_texc = texmap_texcoord;
	indirect = indtex;
	colchan = colchan
      }
  | None ->
      Printf.fprintf stderr "Attempting to match: '%s'\n"
		     (string_of_expression expr);
      Printf.fprintf stderr "Rewritten from original: '%s'\n"
		     (string_of_expression orig_expr);
      raise (Can't_match_stage stage)

let zfmt_of_bits = function
    8 -> Z8
  | 16 -> Z16
  | 24 -> Z24x8
  | _ -> failwith "Unexpected Z format"

exception Not_int_cst_or_cvar

let cv_of_expr = function
    Int x -> Int_cst (Int32.to_int x)
  | CVar c -> Int_cvar c
  | _ -> raise Not_int_cst_or_cvar

(* Match Z-texture expression of form:

   z = texmapM:fmt[texcoordN];
   z = texmapM:fmt[texcoornN] + cst;
   z = z + texmapM:fmt[texcoordN];
   z = z + texmapM:fmt[texcoordN] + cst;  *)

let compile_z_texture stage = function
    Zbits (n, Texmap (tm, Texcoord tc)) ->
      {
        ztex_fmt = zfmt_of_bits n;
        ztex_offset = Int_cst 0;
	ztex_operation = Ztex_replace;
	ztex_texmap_texc = tm, tc
      }
  | Plus (Zbits (n, Texmap (tm, Texcoord tc)), (Int _ | CVar _ as cv))
  | Plus ((Int _ | CVar _ as cv), Zbits (n, Texmap (tm, Texcoord tc))) ->
      {
        ztex_fmt = zfmt_of_bits n;
        ztex_offset = cv_of_expr cv;
	ztex_operation = Ztex_replace;
	ztex_texmap_texc = tm, tc
      }
  | Plus (Z, Zbits (n, Texmap (tm, Texcoord tc)))
  | Plus (Zbits (n, Texmap (tm, Texcoord tc)), Z) ->
      {
        ztex_fmt = zfmt_of_bits n;
        ztex_offset = Int_cst 0;
	ztex_operation = Ztex_add;
	ztex_texmap_texc = tm, tc
      }
  | Plus (Z, Plus (Zbits (n, Texmap (tm, Texcoord tc)), (Int _ | CVar _ as cv)))
  | Plus (Z, Plus ((Int _ | CVar _ as cv), Zbits (n, Texmap (tm, Texcoord tc))))
  | Plus (Plus (Z, Zbits (n, Texmap (tm, Texcoord tc))), (Int _ | CVar _ as cv))
  | Plus (Plus (Z, (Int _ | CVar _ as cv)),
	  Zbits (n, Texmap (tm, Texcoord tc))) ->
      {
        ztex_fmt = zfmt_of_bits n;
        ztex_offset = cv_of_expr cv;
	ztex_operation = Ztex_add;
	ztex_texmap_texc = tm, tc
      }
  | e ->
      Printf.fprintf stderr "Can't match Z-texture expression: '%s'\n"
		     (string_of_expression e);
      raise (Can't_match_stage stage)

exception Can't_match_alpha_test of expr

(* There are more of these available!  They can't be parsed yet though.  *)

let alpha_test_comparison = function
    Clt (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_less; acmp_val = cv_of_expr cv }
  | Cgt (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_greater; acmp_val = cv_of_expr cv }
  | Clte (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_lequal; acmp_val = cv_of_expr cv }
  | Cgte (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_gequal; acmp_val = cv_of_expr cv }
  | Ceq (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_equal; acmp_val = cv_of_expr cv }
  | Cne (Select (Var_ref Tev, [| A |]), (Int _ | CVar _ as cv)) ->
      { acmp_op = Acmp_nequal; acmp_val = cv_of_expr cv }
  | x -> raise (Can't_match_alpha_test x)

let valid_alpha_test expr =
  try
    ignore (alpha_test_comparison expr);
    true
  with Can't_match_alpha_test _ ->
    false

(* Match alpha test expression of form:

   alpha_pass = tev.a CMP val1 COMBINE_OP tev.a CMP val2;
   alpha_pass = tev.a CMP val1;
*)

let compile_alpha_test = function
    Or (cmp1, cmp2) ->
      {
        atest_cmp1 = alpha_test_comparison cmp1;
	atest_combine = Acomb_or;
	atest_cmp2 = alpha_test_comparison cmp2
      }
  | And (cmp1, cmp2) ->
      {
        atest_cmp1 = alpha_test_comparison cmp1;
	atest_combine = Acomb_and;
	atest_cmp2 = alpha_test_comparison cmp2
      }
  | Xor (cmp1, cmp2) ->
      {
        atest_cmp1 = alpha_test_comparison cmp1;
	atest_combine = Acomb_xor;
	atest_cmp2 = alpha_test_comparison cmp2
      }
  | Ceq (cmp1, cmp2) when valid_alpha_test cmp1 && valid_alpha_test cmp2 ->
      {
        atest_cmp1 = alpha_test_comparison cmp1;
	atest_combine = Acomb_xnor;
	atest_cmp2 = alpha_test_comparison cmp2
      }
  | cmp ->
      {
        atest_cmp1 = alpha_test_comparison cmp;
	atest_combine = Acomb_or;
	atest_cmp2 =
	  {
	    acmp_op = Acmp_never;
	    acmp_val = Int_cst 0
	  }
      }

let combine_tev_orders col_order alpha_order =
  let combined_colchan =
    match col_order.colchan, alpha_order.colchan with
      Some Colour0, Some Alpha0 -> Some Colour0A0
    | Some Colour1, Some Alpha1 -> Some Colour1A1
    | Some Alpha0, Some Alpha0 -> Some Alpha0
    | Some Alpha1, Some Alpha1 -> Some Alpha1
    | Some Colour0A0, Some Colour0A0 -> Some Colour0A0
    | Some Colour1A1, Some Colour1A1 -> Some Colour1A1
    | Some x, None -> Some x
    | None, Some x -> Some x
    | None, None -> None
    | _ -> failwith "Invalid colour/alpha channel combination"
  and combined_texmap =
    match col_order.texmap_texc, alpha_order.texmap_texc with
      Some (ctm, ctc), Some (atm, atc) when ctm = atm && ctc = atc ->
        Some (ctm, ctc)
    | Some x, None -> Some x
    | None, Some x -> Some x
    | None, None -> None
    | _ -> failwith "Invalid texmap/texcoord combination" in
  combined_texmap, combined_colchan

let array_of_stages stage_defs swiz_arr ns =
  let arr =
    Array.init ns
      (fun _ ->
        { ind_texc_part = None; ind_direct_tex_part = None; colour_part = None;
	  alpha_part = None; ztex_part = None }) in
  let alphatest_part = ref None in
  List.iter
    (function
	Regular_stage (sn, stage_exprs) ->
	  begin try
            List.iter
              (fun stage_expr ->
        	let stage_expr = default_assign stage_expr in
        	match stage_expr with
		  Assign (_, [| A |], _) ->
		    let comp =
		      compile_expr sn stage_expr swiz_arr.(sn) ~alpha:true
				   avar_of_expr in
		    arr.(sn).alpha_part <- Some comp
		| Assign (_, [| R; G; B |], _) ->
		    let comp =
		      compile_expr sn stage_expr swiz_arr.(sn) ~alpha:false
				   cvar_of_expr in
		    arr.(sn).colour_part <- Some comp
		| Assign (_, [| R; G; B; A |], _) ->
		    (* Not entirely sure if it's sensible to allow this.  *)
		    let ccomp = compile_expr sn stage_expr swiz_arr.(sn)
					     ~alpha:false cvar_of_expr
		    and acomp =
		      compile_expr sn stage_expr swiz_arr.(sn) ~alpha:true
				   avar_of_expr in
		    arr.(sn).alpha_part <- Some acomp;
		    arr.(sn).colour_part <- Some ccomp
		| Assign (Itexc_dst, [| LS_S; LS_T |], e) ->
	            let plain_texcoord, tcomp = rewrite_indirect_texcoord e in
	            arr.(sn).ind_texc_part <- Some tcomp;
		    arr.(sn).ind_direct_tex_part
		      <- Some { ind_dir_texcoord = plain_texcoord;
				ind_dir_texmap = None;
				ind_dir_nullified = false }
		| Assign (Z_dst, [||], e) ->
	            let ztex_info = compile_z_texture sn e in
		    arr.(sn).ztex_part <- Some ztex_info
		| _ -> failwith "Bad stage expression")
	    stage_exprs
	  with
            ((Bad_avar e) as exc) ->
              let s = string_of_expression e in
	      Printf.fprintf stderr "In '%s':\n" s;
	      raise exc
	  | ((Bad_cvar e) as exc) ->
              let s = string_of_expression e in
	      Printf.fprintf stderr "In '%s':\n" s;
	      raise exc
	  | Unrecognized_indirect_texcoord_part (fn, ex) ->
              Printf.fprintf stderr
		"Unrecognized part in indirect texcoord expression '%s', %s\n"
		fn (string_of_expression ex);
	      exit 1
	  end
      | Alpha_test_stage stage_expr ->
          begin match stage_expr with
	    Assign (Alpha_pass, [||], e) ->
	      let alphatest_info = compile_alpha_test e in
	      alphatest_part := Some alphatest_info
	  | _ -> failwith "Bad alpha test expression"
	  end)
    stage_defs;
  arr, !alphatest_part

let max_colour_and_texcoord_channels stage_arr =
  let colchans = ref 0
  and texchans = ref 0 in
  let bump_colchans = function
      Some (Colour0 | Alpha0 | Colour0A0) ->
	if !colchans < 1 then
          colchans := 1
    | Some (Colour1 | Alpha1 | Colour1A1) ->
	if !colchans < 2 then
          colchans := 2
    | _ -> ()
  and bump_texchans = function
      Some (_, tc) ->
        if tc + 1 > !texchans then
	  texchans := tc + 1
    | None -> () in
  Array.iter
    (fun stage ->
      begin match stage.colour_part with
        None -> ()
      | Some cp ->
          bump_colchans cp.colchan;
	  bump_texchans cp.texmap_texc
      end;
      begin match stage.alpha_part with
        None -> ()
      | Some ap ->
          bump_colchans ap.colchan;
	  bump_texchans ap.texmap_texc
      end;
      begin match stage.ind_texc_part with
        None -> ()
      | Some ip ->
          bump_texchans (Some (ip.ind_texmap, ip.ind_texcoord));
      end;
      begin match stage.ind_direct_tex_part with
        None -> ()
      | Some dp ->
          bump_texchans (Some (0, dp.ind_dir_texcoord))
      end;
      begin match stage.ztex_part with
        None -> ()
      | Some zp ->
          bump_texchans (Some zp.ztex_texmap_texc)
      end)
    stage_arr;
  !colchans, !texchans

let print_swaps oc snum t_or_r lsa =
  Printf.fprintf oc "stage %d: %s swaps: %s\n" snum t_or_r
		 (string_of_laneselect lsa ~reverse:false)

exception Swizzle_collision

let merge_swaps a b =
  Array.init 4
    (fun i ->
      match a.(i), b.(i) with
        (R | G | B | A as c), X -> c
      | X, (R | G | B | A as c) -> c
      | X, X -> X
      | a, b when a = b -> a
      | _, _ -> raise Swizzle_collision)

(* If we can write a swizzle using the alpha channel, do that in preference to
   using swapped versions of the colour channels.  This allows more freedom to
   write different swizzles within a single stage.  *)

let merge_swap_list swaplist =
  List.fold_right
    (fun this merged ->
      match this, merged with
	[| r1; g1; b1; X |], [| r2; g2; b2; X |] when r1 = g1 && r1 = b1 ->
	  [| r2; g2; b2; r1 |]
      | [| r1; g1; b1; X |], [| r2; g2; b2; a2 |] when r1 = g1 && r1 = b1
						       && r1 == a2 ->
	  [| r2; g2; b2; a2 |]
      | [| r1; g1; b1; X |], [| r2; g2; b2; X |] when r2 = g2 && r2 = b2 ->
	  [| r1; g1; b1; r2 |]
      | [| r1; g1; b1; a1 |], [| r2; g2; b2; X |] when r2 = g2 && r2 = b2
						       && r2 = a1 ->
	  [| r1; g1; b1; a1 |]
      | _ -> merge_swaps this merged)
    swaplist
    [| X; X; X; X |]

exception Swap_substitution_failed

(* Does this greedy algorithm lead to non-optimal results in some
   circumstances?  *)

let unique_swaps swaps unique_list =
  if swaps = [| X; X; X; X |]
     || List.exists (swap_matches swaps) unique_list then begin
    let substituted = ref false in
    List.map
      (fun existing_entry ->
        if swap_matches existing_entry swaps && not !substituted then begin
	  substituted := true;
	  merge_swaps existing_entry swaps
	end else
	  existing_entry)
      unique_list
  end else
    swaps :: unique_list

let gather_swap_tables swizzle_arr =
  let swap_tables = ref [] in
  for i = 0 to Array.length swizzle_arr - 1 do
    let cpart = swizzle_arr.(i).colour_swaps
    and apart = swizzle_arr.(i).alpha_swaps in
    let texswaps, rasswaps =
      match cpart, apart with
	Some cpart, Some apart ->
	  (* Note: merge alpha before colour, because it's more highly
	     constrained: e.g colour part can use either TEXA or TEXC, but alpha
	     can only use TEXA.  *)
          let texswaps = merge_swap_list (cpart.tex_swaps @ apart.tex_swaps)
	  and rasswaps = merge_swap_list (cpart.ras_swaps @ apart.ras_swaps) in
	  texswaps, rasswaps
      | Some cpart, None ->
          let texswaps = merge_swap_list cpart.tex_swaps
	  and rasswaps = merge_swap_list cpart.ras_swaps in
	  texswaps, rasswaps
      | None, Some apart ->
          let texswaps = merge_swap_list apart.tex_swaps
	  and rasswaps = merge_swap_list apart.ras_swaps in
	  texswaps, rasswaps
       | None, None ->
          [| X; X; X; X |], [| X; X; X; X |] in
    if !debug then begin
      print_swaps stderr i "texture" texswaps;
      print_swaps stderr i "raster" rasswaps
    end;
    swap_tables := unique_swaps texswaps !swap_tables;
    swap_tables := unique_swaps rasswaps !swap_tables;
    swizzle_arr.(i).merged_tex_swaps <- Some texswaps;
    swizzle_arr.(i).merged_ras_swaps <- Some rasswaps
  done;
  Array.of_list !swap_tables

let add_if_different l ls =
  if List.mem l ls then
    ls
  else
    l :: ls

let merge_if_same a b complaint =
  match a, b with
    Some a, Some b when a = b -> a
  | Some a, None -> a
  | None, Some b -> b
  | None, None -> raise Not_found
  | _ -> failwith complaint

let merge_if_same_opt a b complaint =
  match a, b with
    Some a, Some b when a = b -> Some a
  | Some a, None -> Some a
  | None, Some b -> Some b
  | None, None -> None
  | _ -> failwith complaint

(* Extract a "direct" texmap from the colour and/or alpha parts of a stage.
   Throw Not_found if none.  *)

let extract_texmap_from_stage stage =
  let tm_from_col =
    match stage.colour_part with
      Some cp ->
	begin match cp.texmap_texc with
          Some (tm, _) -> Some tm
	| None -> None
	end
    | None -> None
  and tm_from_alpha =
    match stage.alpha_part with
      Some ap ->
        begin match ap.texmap_texc with
	  Some (tm, _) -> Some tm
	| None -> None
	end
    | None -> None in
  merge_if_same tm_from_col tm_from_alpha "Mismatched texmaps"

(* Get indirect texmap/texcoord from colour, alpha or "indirect texcoord" stage
   parts.  *)

let get_tm_and_tc_from_indirect_info ind_info =
  if ind_info.ind_texmap == -1 || ind_info.ind_texcoord == -1 then
    None
  else
    Some (ind_info.ind_texmap, ind_info.ind_texcoord)

let put_tm_and_tc ind_info tm tc =
  if ind_info.ind_texmap == -1 || ind_info.ind_texcoord == -1 then begin
    ind_info.ind_texmap <- tm;
    ind_info.ind_texcoord <- tc
  end

let extract_indirect_tex_info_from_stage stage =
  let ipart = match stage.ind_texc_part with
    Some ind_info -> get_tm_and_tc_from_indirect_info ind_info
  | None -> None
  and apart = match stage.alpha_part with
    Some ap ->
      begin match ap.indirect with
        Some api -> get_tm_and_tc_from_indirect_info api
      | None -> None
      end
  | None -> None
  and cpart = match stage.colour_part with
    Some cp ->
      begin match cp.indirect with
        Some cpi -> get_tm_and_tc_from_indirect_info cpi
      | None -> None
      end
  | None -> None in
  let acpart = merge_if_same_opt apart cpart "Indirect texture mismatch" in
  let acipart = merge_if_same_opt acpart ipart "Indirect texture mismatch" in
  match acipart with
    None -> raise Not_found
  | Some x -> x

let fill_indirect_tex_info_in_stage stage tm tc =
  begin match stage.ind_texc_part with
    Some ind_info -> put_tm_and_tc ind_info tm tc
  | None -> ()
  end;
  begin match stage.alpha_part with
    Some ap ->
      begin match ap.indirect with
        Some api -> put_tm_and_tc api tm tc
      | None -> ()
      end
  | None -> ()
  end;
  begin match stage.colour_part with
    Some cp ->
      begin match cp.indirect with
        Some cpi -> put_tm_and_tc cpi tm tc
      | None -> ()
      end
  | None -> ()
  end

(* Indirect lookups can be written without referring to the "direct" texture
   lookup which the indirect lookup modifies.  We must still name a texture
   though, and we must also "nullify" it so the texture lookup doesn't actually
   take place.  Do a scan backwards, filling in this phantom texture info.  *)

let fill_missing_indirect_lookups stage_arr =
  let direct_ind_tex = ref None in
  for i = Array.length stage_arr - 1 downto 0 do
    begin
      try
	let tm = extract_texmap_from_stage stage_arr.(i) in
	direct_ind_tex := Some tm
      with Not_found -> ()
    end;
    match stage_arr.(i).ind_direct_tex_part with
      Some idtp ->
        begin match idtp.ind_dir_texmap with
	  Some _ -> ()
	| None ->
	    if !debug then begin
	      match !direct_ind_tex with
	        Some tm ->
		  Printf.fprintf stderr "Filling direct texmap %d at stage %d\n"
		    tm i
	      | None ->
	          Printf.fprintf stderr
		    "Not filling direct texmap at stage %d\n" i
	    end;	        
	    idtp.ind_dir_texmap <- !direct_ind_tex;
	    idtp.ind_dir_nullified <- true
	end
    | None -> ()
  done;
  (* Now do a forward pass to fill in missing "true" indirect texmap/texcoord
     indices, e.g. for indirect stages where we only add the previous indirect
     texcoord.  *)
  let last_ind_tex_info = ref None in
  for i = 0 to Array.length stage_arr - 1 do
    begin
      try
	let tm, tc = extract_indirect_tex_info_from_stage stage_arr.(i) in
	last_ind_tex_info := Some (tm, tc)
      with Not_found ->
        begin match !last_ind_tex_info with
	  Some (tm, tc) ->
	    if !debug then
	      Printf.fprintf stderr
	        "Filling indirect texmap %d and texcoord %d in stage %d\n"
		tm tc i;
	    fill_indirect_tex_info_in_stage stage_arr.(i) tm tc
	| None -> ()
	end
    end
  done

exception No_free_texcoord

(* Texture coordinates might have been omitted for the "direct" texcoord part
   of an indirect lookup.  We don't really care about which texcoord we use in
   that case, but it can't be one we're using for something else, since that
   messes up the hardware's automatic scaling.
   Choose the texcoord beyond the last one we're actually calculating.  This
   can fail if we are using all eight texcoords for something else!  *)

let fill_missing_texcoords stage_arr max_used_texc =
  let check_texc () =
    if max_used_texc == 8 then raise No_free_texcoord in
  for i = 0 to Array.length stage_arr - 1 do
    begin match stage_arr.(i).ind_direct_tex_part with
      Some idt ->
        if idt.ind_dir_texcoord == -1 then begin
	  check_texc ();
	  if !debug then
	    Printf.fprintf stderr
	      "Filling direct texcoord %d for indirect lookup at stage %d\n"
	      max_used_texc i;
	  idt.ind_dir_texcoord <- max_used_texc
	end
    | None -> ()
    end;
    begin match stage_arr.(i).colour_part with
      Some cp ->
        begin match cp.texmap_texc with
	  Some (tm, -1) ->
	    check_texc ();
	    if !debug then
	      Printf.fprintf stderr
	        "Filling direct texcoord %d for colour part at stage %d\n"
		max_used_texc i;
	    cp.texmap_texc <- Some (tm, max_used_texc)
	| _ -> ()
	end
     | None -> ()
     end;
    begin match stage_arr.(i).alpha_part with
      Some ap ->
        begin match ap.texmap_texc with
	  Some (tm, -1) ->
	    check_texc ();
	    if !debug then
	      Printf.fprintf stderr
	        "Filling direct texcoord %d for alpha part at stage %d\n"
		max_used_texc i;
	    ap.texmap_texc <- Some (tm, max_used_texc)
	| _ -> ()
	end
     | None -> ()
     end
  done

let gather_indirect_lookups stage_arr =
  let ind_luts = ref [] in
  for i = 0 to Array.length stage_arr - 1 do
    begin match stage_arr.(i).colour_part, stage_arr.(i).alpha_part with
      None, None -> ()
    | Some cp, None ->
        begin match cp.indirect with
	  None -> ()
	| Some ind ->
	    ind_luts := add_if_different (ind.ind_texmap, ind.ind_texcoord)
					 !ind_luts
	end
    | None, Some ap ->
        begin match ap.indirect with
	  None -> ()
	| Some ind ->
	    ind_luts := add_if_different (ind.ind_texmap, ind.ind_texcoord)
					 !ind_luts
	end
    | Some part1, Some part2 ->
        let ind_part = merge_indirect part1.indirect part2.indirect in
        begin match ind_part with
	  None -> ()
	| Some ind ->
	    ind_luts := add_if_different (ind.ind_texmap, ind.ind_texcoord)
					 !ind_luts
	end
    end;
    begin match stage_arr.(i).ind_texc_part with
      None -> ()
    | Some ind ->
	(*check_ind_part stage_arr.(i).colour_part ind;
	check_ind_part stage_arr.(i).alpha_part ind;*)
	ind_luts := add_if_different (ind.ind_texmap, ind.ind_texcoord)
				     !ind_luts
    end
  done;
  Array.of_list !ind_luts

let lookup_indirect ind_lut_arr ind_part =
  let found = ref None in
  Array.iteri
    (fun idx (tm, tc) ->
      if ind_part.ind_texmap = tm && ind_part.ind_texcoord = tc then
        found := Some idx)
    ind_lut_arr;
  match !found with
    None -> failwith "Can't find indirect lookup"
  | Some f -> f

let string_of_stagenum n =
  "GX_TEVSTAGE" ^ (string_of_int n)

let string_of_tev_input = function
    CC_cprev -> "GX_CC_CPREV"
  | CC_aprev -> "GX_CC_APREV"
  | CC_c0 -> "GX_CC_C0"
  | CC_a0 -> "GX_CC_A0"
  | CC_c1 -> "GX_CC_C1"
  | CC_a1 -> "GX_CC_A1"
  | CC_c2 -> "GX_CC_C2"
  | CC_a2 -> "GX_CC_A2"
  | CC_texc -> "GX_CC_TEXC"
  | CC_texa -> "GX_CC_TEXA"
  | CC_rasc -> "GX_CC_RASC"
  | CC_rasa -> "GX_CC_RASA"
  | CC_one -> "GX_CC_ONE"
  | CC_half -> "GX_CC_HALF"
  | CC_const -> "GX_CC_KONST"
  | CC_zero -> "GX_CC_ZERO"

let string_of_tev_alpha_input = function
    CA_aprev -> "GX_CA_APREV"
  | CA_a0 -> "GX_CA_A0"
  | CA_a1 -> "GX_CA_A1"
  | CA_a2 -> "GX_CA_A2"
  | CA_texa -> "GX_CA_TEXA"
  | CA_rasa -> "GX_CA_RASA"
  | CA_const -> "GX_CA_KONST"
  | CA_zero -> "GX_CA_ZERO"

let string_of_tev_op = function
    OP_add -> "GX_TEV_ADD"
  | OP_sub -> "GX_TEV_SUB"

let string_of_bias = function
    TB_zero -> "GX_TB_ZERO"
  | TB_addhalf -> "GX_TB_ADDHALF"
  | TB_subhalf -> "GX_TB_SUBHALF"

let string_of_scale = function
    CS_scale_1 -> "GX_CS_SCALE_1"
  | CS_scale_2 -> "GX_CS_SCALE_2"
  | CS_scale_4 -> "GX_CS_SCALE_4"
  | CS_divide_2 -> "GX_CS_DIVIDE_2"

let string_of_clamp = function
    true -> "GX_TRUE"
  | false -> "GX_FALSE"

let string_of_result = function
    Tevprev -> "GX_TEVPREV"
  | Tevreg0 -> "GX_TEVREG0"
  | Tevreg1 -> "GX_TEVREG1"
  | Tevreg2 -> "GX_TEVREG2"
  | Itexc_dst -> failwith "unexpected itexcoord result"
  | Z_dst -> failwith "unexpected Z result"
  | Alpha_pass -> failwith "unexpected alpha test result"

let string_of_cmp_op = function
    CMP_r8_gt -> "GX_TEV_COMP_R8_GT"
  | CMP_r8_eq -> "GX_TEV_COMP_R8_EQ"
  | CMP_gr16_gt -> "GX_TEV_COMP_GR16_GT"
  | CMP_gr16_eq -> "GX_TEV_COMP_GR16_EQ"
  | CMP_bgr24_gt -> "GX_TEV_COMP_BGR24_GT"
  | CMP_bgr24_eq -> "GX_TEV_COMP_BGR24_EQ"
  | CMP_rgb8_gt -> "GX_TEV_COMP_RGB8_GT"
  | CMP_rgb8_eq -> "GX_TEV_COMP_RGB8_EQ"
  | CMP_a8_gt -> "GX_TEV_COMP_A8_GT"
  | CMP_a8_eq -> "GX_TEV_COMP_A8_EQ"

let string_of_colour_chan = function
    Colour0 -> "GX_COLOR0"
  | Alpha0 -> "GX_ALPHA0"
  | Colour0A0 -> "GX_COLOR0A0"
  | Colour1 -> "GX_COLOR1"
  | Alpha1 -> "GX_ALPHA1"
  | Colour1A1 -> "GX_COLOR1A1"
  | ColourZero -> "GX_COLORZERO"
  | AlphaBump -> "GX_ALPHA_BUMP"
  | AlphaBumpN -> "GX_ALPHA_BUMPN"
  | c -> failwith "Bad colour channel"

(* These happen to have mostly the same choices for colours & alphas.  *)
let string_of_const cst alpha =
  let ac = if alpha then "GX_TEV_KASEL_" else "GX_TEV_KCSEL_" in
  let tail = match cst with
    KCSEL_1 -> "1"
  | KCSEL_7_8 -> "7_8"
  | KCSEL_3_4 -> "3_4"
  | KCSEL_5_8 -> "5_8"
  | KCSEL_1_2 -> "1_2"
  | KCSEL_3_8 -> "3_8"
  | KCSEL_1_4 -> "1_4"
  | KCSEL_1_8 -> "1_8"
  | KCSEL_K0 when not alpha -> "K0"
  | KCSEL_K1 when not alpha -> "K1"
  | KCSEL_K2 when not alpha -> "K2"
  | KCSEL_K3 when not alpha -> "K3"
  | KCSEL_K0_R -> "K0_R"
  | KCSEL_K1_R -> "K1_R"
  | KCSEL_K2_R -> "K2_R"
  | KCSEL_K3_R -> "K3_R"
  | KCSEL_K0_G -> "K0_G"
  | KCSEL_K1_G -> "K1_G"
  | KCSEL_K2_G -> "K2_G"
  | KCSEL_K3_G -> "K3_G"
  | KCSEL_K0_B -> "K0_B"
  | KCSEL_K1_B -> "K1_B"
  | KCSEL_K2_B -> "K2_B"
  | KCSEL_K3_B -> "K3_B"
  | KCSEL_K0_A -> "K0_A"
  | KCSEL_K1_A -> "K1_A"
  | KCSEL_K2_A -> "K2_A"
  | KCSEL_K3_A -> "K3_A"
  | _ -> failwith "Bad constant" in
  ac ^ tail

let string_of_indtexidx x =
  "GX_INDTEXSTAGE" ^ string_of_int x

let string_of_format = function
    3 -> "GX_ITF_3"
  | 4 -> "GX_ITF_4"
  | 5 -> "GX_ITF_5"
  | 8 -> "GX_ITF_8"
  | _ -> failwith "Bad format"

exception Bad_ind_bias of float * float * float

let string_of_indbias fmt bias =
  if fmt == 8 then begin
    match bias with
      [|    0.0;    0.0;    0.0 |] -> "GX_ITB_NONE"
    | [| -128.0;    0.0;    0.0 |] -> "GX_ITB_S"
    | [|    0.0; -128.0;    0.0 |] -> "GX_ITB_T"
    | [| -128.0; -128.0;    0.0 |] -> "GX_ITB_ST"
    | [|    0.0;    0.0; -128.0 |] -> "GX_ITB_U"
    | [| -128.0;    0.0; -128.0 |] -> "GX_ITB_SU"
    | [|    0.0; -128.0; -128.0 |] -> "GX_ITB_TU"
    | [| -128.0; -128.0; -128.0 |] -> "GX_ITB_STU"
    | _ -> raise (Bad_ind_bias (bias.(0), bias.(1), bias.(2)))
  end else begin
    match bias with
      [| 0.0; 0.0; 0.0 |] -> "GX_ITB_NONE"
    | [| 1.0; 0.0; 0.0 |] -> "GX_ITB_S"
    | [| 0.0; 1.0; 0.0 |] -> "GX_ITB_T"
    | [| 1.0; 1.0; 0.0 |] -> "GX_ITB_ST"
    | [| 0.0; 0.0; 1.0 |] -> "GX_ITB_U"
    | [| 1.0; 0.0; 1.0 |] -> "GX_ITB_SU"
    | [| 0.0; 1.0; 1.0 |] -> "GX_ITB_TU"
    | [| 1.0; 1.0; 1.0 |] -> "GX_ITB_STU"
    | _ -> raise (Bad_ind_bias (bias.(0), bias.(1), bias.(2)))
  end

let string_of_mtxidx mtx scale =
  match mtx, scale with
    T_ind_matrix 0, 0 -> "GX_ITM_0"
  | T_ind_matrix 1, 1 -> "GX_ITM_1"
  | T_ind_matrix 2, 2 -> "GX_ITM_2"
  | T_dyn_s, 0 -> "GX_ITM_S0"
  | T_dyn_s, 1 -> "GX_ITM_S1"
  | T_dyn_s, 2 -> "GX_ITM_S2"
  | T_dyn_t, 0 -> "GX_ITM_T0"
  | T_dyn_t, 1 -> "GX_ITM_T1"
  | T_dyn_t, 2 -> "GX_ITM_T2"
  | T_no_matrix, _ -> "GX_ITM_OFF"
  | _ -> failwith "Bad indirect matrix/scale combination"

let string_of_wrap = function
    None -> "GX_ITW_OFF"
  | Some 0l -> "GX_ITW_0"
  | Some 16l -> "GX_ITW_16"
  | Some 32l -> "GX_ITW_32"
  | Some 64l -> "GX_ITW_64"
  | Some 128l -> "GX_ITW_128"
  | Some 256l -> "GX_ITW_256"
  | _ -> failwith "Bad wrap"

let string_of_gx_bool = function
    false -> "GX_FALSE"
  | true -> "GX_TRUE"

let string_of_alpha_select = function
    None -> "GX_ITBA_OFF"
  | Some S -> "GX_ITBA_S"
  | Some T -> "GX_ITBA_T"
  | Some U -> "GX_ITBA_U"

let print_const_setup oc stage cst ~alpha =
  if alpha then
    Printf.fprintf oc "GX_SetTevKAlphaSel (%s, %s);\n"
      (string_of_stagenum stage) (string_of_const cst true)
  else
    Printf.fprintf oc "GX_SetTevKColorSel (%s, %s);\n"
      (string_of_stagenum stage) (string_of_const cst false)

(* Print a normal (direct) texture lookup order.  *)

let print_tev_order oc stage_num texmap ~nullified colchan =
  let tm, tc = match texmap with
    None -> "GX_TEXMAP_NULL", "GX_TEXCOORDNULL"
  | Some (tm, tc) ->
      "GX_TEXMAP" ^ string_of_int tm, "GX_TEXCOORD" ^ string_of_int tc
  and cc = match colchan with
    None -> "GX_COLORNULL"
  | Some c -> string_of_colour_chan c
  and nullify = if nullified then " | GX_TEXMAP_DISABLE" else "" in
  Printf.fprintf oc "GX_SetTevOrder (%s, %s, %s%s, %s);\n"
    (string_of_stagenum stage_num) tc tm nullify cc

let print_tev_setup oc stage_num stage_op string_of_ac_input ~alpha =
  let acin, acop = if alpha then
    "GX_SetTevAlphaIn", "GX_SetTevAlphaOp"
  else
    "GX_SetTevColorIn", "GX_SetTevColorOp" in
  match stage_op with
    Arith ar -> 
      Printf.fprintf oc "%s (%s, %s, %s, %s, %s);\n" acin
        (string_of_stagenum stage_num) (string_of_ac_input ar.a)
	(string_of_ac_input ar.b) (string_of_ac_input ar.c)
	(string_of_ac_input ar.d);
      Printf.fprintf oc "%s (%s, %s, %s, %s, %s, %s);\n" acop
        (string_of_stagenum stage_num) (string_of_tev_op ar.op)
	(string_of_bias ar.bias) (string_of_scale ar.scale)
	(string_of_clamp ar.clamp) (string_of_result ar.result)
  | Comp cmp ->
      Printf.fprintf oc "%s (%s, %s, %s, %s, %s);\n" acin
        (string_of_stagenum stage_num) (string_of_ac_input cmp.cmp_a)
	(string_of_ac_input cmp.cmp_b) (string_of_ac_input cmp.cmp_c)
	(string_of_ac_input cmp.cmp_d);
      Printf.fprintf oc
        "%s (%s, %s, GX_TB_ZERO, GX_CS_SCALE_1, GX_FALSE, %s);\n" acop
        (string_of_stagenum stage_num) (string_of_cmp_op cmp.cmp_op)
	(string_of_result cmp.cmp_result)

let string_of_chan = function
    R | X -> "GX_CH_RED"
  | G -> "GX_CH_GREEN"
  | B -> "GX_CH_BLUE"
  | A -> "GX_CH_ALPHA"
  | LS_S | LS_T -> failwith "unexpected texcoord selector"

let string_of_swap_table n =
  "GX_TEV_SWAP" ^ (string_of_int n)

exception Too_many_swap_tables

let print_swap_tables oc swap_tables =
  if Array.length swap_tables > 4 then
    raise Too_many_swap_tables;
  Array.iteri
    (fun i tab ->
      Printf.fprintf oc "GX_SetTevSwapModeTable (%s, %s, %s, %s, %s);\n"
        (string_of_swap_table i) (string_of_chan tab.(0))
	(string_of_chan tab.(1)) (string_of_chan tab.(2))
	(string_of_chan tab.(3)))
    swap_tables

exception Swap_table_missing

let matching_swap_table_entry swap_tables table =
  if table = [| X; X; X; X |] then
    -1
  else begin
    let found = ref None in
    for i = 0 to Array.length swap_tables - 1 do
      if swap_matches swap_tables.(i) table then
	found := Some i
    done;
    match !found with
      None -> raise Swap_table_missing
    | Some f -> f
  end

let print_swap_setup oc stagenum swap_tables tex_swaps ras_swaps =
  let tnum, rnum =
    match tex_swaps, ras_swaps with
      Some ts, Some rs ->
        matching_swap_table_entry swap_tables ts,
	matching_swap_table_entry swap_tables rs
    | Some ts, None ->
        matching_swap_table_entry swap_tables ts, -1
    | None, Some rs ->
        -1, matching_swap_table_entry swap_tables rs
    | None, None ->
        -1, -1 in
  if tnum != -1 || rnum != -1 then begin
    let tnum' = if tnum == -1 then 0 else tnum
    and rnum' = if rnum == -1 then 0 else rnum in
    Printf.fprintf oc "GX_SetTevSwapMode (%s, %s, %s);\n"
      (string_of_stagenum stagenum) (string_of_swap_table rnum')
      (string_of_swap_table tnum')
  end

let string_of_ind_tev_stage n =
  "GX_INDTEXSTAGE" ^ (string_of_int n)

let print_indirect_lookups oc lut_arr =
  Printf.fprintf oc "GX_SetNumIndStages (%d);\n" (Array.length lut_arr);
  for i = 0 to Array.length lut_arr - 1 do
    let tm, tc = lut_arr.(i) in
    Printf.fprintf oc
      "GX_SetIndTexOrder (GX_INDTEXSTAGE%d, GX_TEXCOORD%d, GX_TEXMAP%d);\n"
      i tc tm
  done

let print_indirect_setup oc stagenum ind_lookups ind_part =
  match ind_part with
    None -> Printf.fprintf oc "GX_SetTevDirect (%s);\n"
	      (string_of_stagenum stagenum)
  | Some ind ->
      Printf.fprintf oc
        "GX_SetTevIndirect (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s);\n"
	(string_of_stagenum stagenum)
	(string_of_indtexidx (lookup_indirect ind_lookups ind))
	(string_of_format ind.ind_tex_format)
	(string_of_indbias ind.ind_tex_format ind.ind_tex_bias)
	(string_of_mtxidx ind.ind_tex_matrix ind.ind_tex_scale)
	(string_of_wrap ind.ind_tex_wrap_s) (string_of_wrap ind.ind_tex_wrap_t)
	(string_of_gx_bool ind.ind_tex_addprev)
	(string_of_gx_bool ind.ind_tex_unmodified_lod)
	(string_of_alpha_select ind.ind_tex_alpha_select)

let string_of_ztex_operation = function
    Ztex_add -> "GX_ZT_ADD"
  | Ztex_replace -> "GX_ZT_REPLACE"

let string_of_ztex_format = function
    Z8 -> "GX_TF_Z8"
  | Z16 -> "GX_TF_Z16"
  | Z24x8 -> "GX_TF_Z24X8"

let string_of_cv = function
    Int_cst i -> string_of_int i
  | Int_cvar c -> c

let print_ztex_setup oc ztex =
  Printf.fprintf oc
    "GX_SetZTexture (%s, %s, %s);\n"
    (string_of_ztex_operation ztex.ztex_operation)
    (string_of_ztex_format ztex.ztex_fmt)
    (string_of_cv ztex.ztex_offset)

let print_disable_ztex oc =
  Printf.fprintf oc "GX_SetZTexture (GX_ZT_DISABLE, GX_TF_I4, 0);\n"

let string_of_alphatest_comparison = function
    Acmp_never -> "GX_NEVER"
  | Acmp_less -> "GX_LESS"
  | Acmp_equal -> "GX_EQUAL"
  | Acmp_lequal -> "GX_LEQUAL"
  | Acmp_greater -> "GX_GREATER"
  | Acmp_nequal -> "GX_NEQUAL"
  | Acmp_gequal -> "GX_GEQUAL"
  | Acmp_always -> "GX_ALWAYS"

let string_of_alphatest_combine = function
    Acomb_or -> "GX_AOP_OR"
  | Acomb_and -> "GX_AOP_AND"
  | Acomb_xor -> "GX_AOP_XOR"
  | Acomb_xnor -> "GX_AOP_XNOR"

let print_alphatest_setup oc atest =
  Printf.fprintf oc "GX_SetAlphaCompare (%s, %s, %s, %s, %s);\n"
    (string_of_alphatest_comparison atest.atest_cmp1.acmp_op)
    (string_of_cv atest.atest_cmp1.acmp_val)
    (string_of_alphatest_combine atest.atest_combine)
    (string_of_alphatest_comparison atest.atest_cmp2.acmp_op)
    (string_of_cv atest.atest_cmp2.acmp_val)

let print_disable_alphatest oc =
  Printf.fprintf oc
    "GX_SetAlphaCompare (GX_ALWAYS, 0, GX_AOP_AND, GX_ALWAYS, 0);\n"

(* From a STAGE (stage_info), AC_TEXMAP ((int * int) option, being the texture
   map and texture coord for the colour/alpha parts) and AC_INDIR_PART
   (indirect_info option), return another (int * int) option -- the "direct"
   texture map and texture coord, and another indirect_info option, representing
   merged indirect parts from colour, alpha and "indirect texcoord" parts.  *)

let get_direct_and_indirect_tex_parts stage ac_texmap ac_indir_part =
  let nullified = ref false in
  let dir_tex_parts =
    match ac_texmap, stage.ind_direct_tex_part with
      None, None -> None
    | Some _, None -> ac_texmap
    | None, Some ti ->
	if ti.ind_dir_nullified then
	  nullified := true;
        begin match ti.ind_dir_texmap with
	  Some idt -> Some (idt, ti.ind_dir_texcoord)
	| None -> failwith "Missing (maybe nullified) texmap reference"
	end
    | Some (tm, tc), Some ti ->
	if ti.ind_dir_nullified then
	  nullified := true;
        begin match ti.ind_dir_texmap with
	  Some idt when idt = tm && ti.ind_dir_texcoord = tc -> 
	    ac_texmap
	| Some _ -> failwith "Mismatched direct texcoord parts"
	| None -> failwith "Missing (maybe nullified) texmap reference"
	end in
  let indir_parts = merge_indirect ac_indir_part stage.ind_texc_part in
  dir_tex_parts, indir_parts, !nullified

let _ =
  let in_file = ref ""
  and out_file = ref "" in
  Arg.parse ["-o", Arg.Set_string out_file, "Output file";
	     "-d", Arg.Set debug, "Debugging"]
            (fun i -> in_file := i)
	    "Usage: tevsl <infile> -o <outfile>";
  if !in_file = "" then
    failwith "Missing input file";
  if !out_file = "" then
    failwith "Missing output file";
  let inchan = open_in !in_file in
  let outchan = open_out !out_file in
  try
    let parsed_stages = try
      parse_channel inchan
    with Expr.Parsing_stage (st, en) ->
      Printf.fprintf stderr "Parse error: line %d[%d] to %d[%d]\n"
	st.Lexing.pos_lnum st.Lexing.pos_bol en.Lexing.pos_lnum
	en.Lexing.pos_bol;
	exit 1 in
    close_in inchan;
    let num_stages = num_stages parsed_stages in
    print_num_stages outchan num_stages;
    let swiz_arr = array_of_swizzles parsed_stages num_stages in
    let swap_tables = gather_swap_tables swiz_arr in
    let stage_arr, alphatest_part =
      array_of_stages parsed_stages swiz_arr num_stages in
    let num_colchans, num_texchans =
      max_colour_and_texcoord_channels stage_arr in
    print_num_channels outchan num_colchans num_texchans;
    output_char outchan '\n';
    fill_missing_texcoords stage_arr num_texchans;
    fill_missing_indirect_lookups stage_arr;
    let indirect_lookups = gather_indirect_lookups stage_arr in
    print_swap_tables outchan swap_tables;
    output_char outchan '\n';
    print_indirect_lookups outchan indirect_lookups;
    output_char outchan '\n';
    let zbuf_before_texturing = ref true in
    for i = 0 to num_stages - 1 do
      let ac_texmap, colchan, ac_indir_part =
	match stage_arr.(i).colour_part, stage_arr.(i).alpha_part with
          None, Some ap -> ap.texmap_texc, ap.colchan, ap.indirect
	| Some cp, None -> cp.texmap_texc, cp.colchan, cp.indirect
	| Some cp, Some ap ->
            let a, b = combine_tev_orders cp ap in
	    a, b, merge_indirect ap.indirect cp.indirect
	| None, None -> failwith "Missing tev stage!" in
      let acz_texmap = begin match stage_arr.(i).ztex_part with
        Some zpart ->
	  begin match ac_texmap with
	    Some _ ->
	      Printf.fprintf stderr
	        "TEV expression may not use textures when Z-texturing is being used (at stage %d)\n" i;
	      exit 1
	  | None -> Some zpart.ztex_texmap_texc
	  end
      | None -> ac_texmap
      end in
      let texmap, indir_part, nullified =
	get_direct_and_indirect_tex_parts stage_arr.(i) acz_texmap
					  ac_indir_part in
      print_swap_setup outchan i swap_tables swiz_arr.(i).merged_tex_swaps
		       swiz_arr.(i).merged_ras_swaps;
      print_tev_order outchan i texmap ~nullified colchan;
      print_indirect_setup outchan i indirect_lookups indir_part;
      begin match stage_arr.(i).colour_part with
	Some cpart ->
          begin match cpart.const_usage with
	    Some cst -> print_const_setup outchan i cst ~alpha:false
	  | None -> ()
	  end;
          print_tev_setup outchan i cpart.stage_operation string_of_tev_input
			  ~alpha:false
      | None -> ()
      end;
      begin match stage_arr.(i).alpha_part with
	Some apart ->
          begin match apart.const_usage with
	    Some cst -> print_const_setup outchan i cst ~alpha:true
	  | None -> ()
	  end;
          print_tev_setup outchan i apart.stage_operation
			  string_of_tev_alpha_input ~alpha:true
      | None -> ()
      end;
      begin match stage_arr.(i).ztex_part with
        Some zpart ->
	  if i <> num_stages - 1 then begin
	    Printf.fprintf stderr
	      "Z-texture expression must be at the final stage (is at stage %d)\n" i;
	    exit 1
	  end;
	  print_ztex_setup outchan zpart;
	  (* Z-texturing means we must do texturing before Z-buffering.  *)
	  zbuf_before_texturing := false
      | None ->
          if i == num_stages - 1 then
            print_disable_ztex outchan
      end;
      output_char outchan '\n'
    done;
    (* Handle alpha test.  *)
    begin match alphatest_part with
      None ->
        print_disable_alphatest outchan
    | Some at ->
        print_alphatest_setup outchan at;
	(* Alpha test requires Z-buffer testing after texturing.  *)
	zbuf_before_texturing := false
    end;
    Printf.fprintf outchan "GX_SetZCompLoc (%s);\n"
      (string_of_gx_bool !zbuf_before_texturing);
    close_out outchan
  with e ->
    (* An error of some sort happened, clean up.  *)
    close_in_noerr inchan;
    close_out_noerr outchan;
    Sys.remove !out_file;
    raise e
