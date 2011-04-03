open Expr

exception Bad_float of float
exception Bad_int of int32
exception Bad_bias

let bias_of_expr = function
    Int 0l | Float 0.0 -> TB_zero
  | Float 0.5 -> TB_addhalf
  | Float (-0.5) -> TB_subhalf
  | Int x -> raise (Bad_int x)
  | Float x -> raise (Bad_float x)
  | _ -> raise Bad_bias

exception Bad_cvar

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
  | _ -> raise Bad_cvar

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

exception Too_many_constants

(* Find special-valued "konst" constants in expression, and separate them
   out.  *)

let rewrite_const expr ~alpha =
  let which_const = ref None in
  let set_const x =
    match !which_const with
      None -> which_const := Some x; Var_ref Extracted_const
    | Some foo ->
        if foo <> x then
          raise Too_many_constants
	else
	  Var_ref Extracted_const in
  let rec scan = function
    Plus (a, b) -> Plus (scan a, scan b)
  | Minus (a, b) -> Minus (scan a, scan b)
  | Divide (a, b) -> Divide (scan a, scan b)
  | Mult (Minus (Int 1l, a), b) ->
      (* Avoid rewriting the "1" in (1-x)*y -- hack!  *)
      Mult (Minus (Int 1l, scan a), scan b)
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, cs, e) -> Assign (dv, cs, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Float 1.0 | Int 1l when alpha -> set_const KCSEL_1
  | Float 0.875 -> set_const KCSEL_7_8
  | Float 0.75 -> set_const KCSEL_3_4
  | Float 0.625 -> set_const KCSEL_5_8
  | Float 0.5 when alpha -> set_const KCSEL_1_2
  | Float 0.375 -> set_const KCSEL_3_8
  | Float 0.25 -> set_const KCSEL_1_4
  | Float 0.125 -> set_const KCSEL_1_8
  | Var_ref K0 when not alpha -> set_const KCSEL_K0
  | Var_ref K1 when not alpha -> set_const KCSEL_K1
  | Var_ref K2 when not alpha -> set_const KCSEL_K2
  | Var_ref K3 when not alpha -> set_const KCSEL_K3
  | Select (Var_ref K0, [| R |]) -> set_const KCSEL_K0_R
  | Select (Var_ref K1, [| R |]) -> set_const KCSEL_K1_R
  | Select (Var_ref K2, [| R |]) -> set_const KCSEL_K2_R
  | Select (Var_ref K3, [| R |]) -> set_const KCSEL_K3_R
  | Select (Var_ref K0, [| G |]) -> set_const KCSEL_K0_G
  | Select (Var_ref K1, [| G |]) -> set_const KCSEL_K1_G
  | Select (Var_ref K2, [| G |]) -> set_const KCSEL_K2_G
  | Select (Var_ref K3, [| G |]) -> set_const KCSEL_K3_G
  | Select (Var_ref K0, [| B |]) -> set_const KCSEL_K0_B
  | Select (Var_ref K1, [| B |]) -> set_const KCSEL_K1_B
  | Select (Var_ref K2, [| B |]) -> set_const KCSEL_K2_B
  | Select (Var_ref K3, [| B |]) -> set_const KCSEL_K3_B
  | Select (Var_ref K0, [| A |]) -> set_const KCSEL_K0_A
  | Select (Var_ref K1, [| A |]) -> set_const KCSEL_K1_A
  | Select (Var_ref K2, [| A |]) -> set_const KCSEL_K2_A
  | Select (Var_ref K3, [| A |]) -> set_const KCSEL_K3_A
  | Concat (e, ls) -> Concat (scan e, ls)
  | Float x -> Float x
  | Int x -> Int x
  | Var_ref x -> Var_ref x
  | Texmap (m, c) -> Texmap (m, c)
  | Select (a, la) -> Select (scan a, la) in
  let expr' = scan expr in
  expr', !which_const

exception Incompatible_swaps

let rewrite_swap_tables expr ~alpha =
  let texswap = ref None
  and rasswap = ref None in
  let set_tex t =
    match !texswap with
      None -> texswap := Some t
    | Some o -> if o <> t then raise Incompatible_swaps in
  let set_ras r =
    match !rasswap with
      None -> rasswap := Some r
    | Some o -> if o <> r then raise Incompatible_swaps in
  let default_cat_swap var = function
    [| R | G | B |] -> Concat (Var_ref var, [| R |])
  | [| _; _ |] -> Concat (Var_ref var, [| R; G |])
  | [| _; _; _ |] -> Concat (Var_ref var, [| R; G; B |])
  | [| A |] -> if alpha then Var_ref var else Concat (Var_ref var, [| R |])
  | _ -> failwith "No default swap" in
  let default_swap var = function
    [| R | G | B |] -> if alpha then Var_ref var
		       else Select (Var_ref var, [| R |])
  | [| _; _; _ |] -> Var_ref var
  | [| _; _; _; _ |] -> Var_ref var
  | [| A |] -> if alpha then Var_ref var else Select (Var_ref var, [| R |])
  | _ -> failwith "No default swap" in
  let rec scan = function
    Plus (a, b) -> Plus (scan a, scan b)
  | Minus (a, b) -> Minus (scan a, scan b)
  | Divide (a, b) -> Divide (scan a, scan b)
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, cs, e) -> Assign (dv, cs, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Texmap (m, c) -> Texmap (m, c)
  | Float x -> Float x
  | Int x -> Int x
  | Concat (Var_ref Texc, lx) -> set_tex lx; default_cat_swap Texc lx
  | Concat (Var_ref Texa, lx) -> set_tex lx; default_cat_swap Texa lx
  | Concat (Var_ref Rasc, lx) -> set_ras lx; default_cat_swap Rasc lx
  | Concat (Var_ref Rasa, lx) -> set_ras lx; default_cat_swap Rasa lx
  | Select (Var_ref Texc, lx) -> set_tex lx; default_swap Texc lx
  | Select (Var_ref Texa, lx) -> set_tex lx; default_swap Texa lx
  | Select (Var_ref Rasc, lx) -> set_ras lx; default_swap Rasc lx
  | Select (Var_ref Rasa, lx) -> set_ras lx; default_swap Rasa lx
  | Var_ref Texc -> set_tex [| R; G; B; X |]; Var_ref Texc
  | Var_ref Texa -> set_tex [| X; X; X; A |]; Var_ref Texa
  | Var_ref Rasc -> set_ras [| R; G; B; X |]; Var_ref Rasc
  | Var_ref Rasa -> set_ras [| X; X; X; A |]; Var_ref Rasa
  | Var_ref x -> Var_ref x
  | Select (x, lx) -> Select (scan x, lx)
  | Concat (x, lx) -> Concat (scan x, lx) in
  let expr' = scan expr in
  expr', !texswap, !rasswap

exception Incompatible_texmaps

let rewrite_texmaps expr ~alpha =
  let texmap_texcoord = ref None in
  let set_texmap m c =
    match !texmap_texcoord with
      None -> texmap_texcoord := Some (m, c)
    | Some (om, oc) ->
        if om <> m || oc <> c then
	  raise Incompatible_texmaps in
  let rec scan = function
    Plus (a, b) -> Plus (scan a, scan b)
  | Minus (a, b) -> Minus (scan a, scan b)
  | Divide (a, b) -> Divide (scan a, scan b)
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, cs, e) -> Assign (dv, cs, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Var_ref x -> Var_ref x
  | Texmap (m, c) ->
      set_texmap m c; if alpha then Var_ref Texa else Var_ref Texc
  | Float x -> Float x
  | Int x -> Int x
  | Select (v, lx) -> Select (scan v, lx)
  | Concat (x, lx) -> Concat (scan x, lx) in
  let expr' = scan expr in
  expr', !texmap_texcoord

exception Incompatible_colour_channels

let rewrite_colchans expr ~alpha =
  let colchan = ref None in
  let set_colchan c =
    match !colchan with
      None -> colchan := Some c
    | Some oc ->
        if oc <> c then
	  raise Incompatible_colour_channels in
  let rec scan = function
    Plus (a, b) -> Plus (scan a, scan b)
  | Minus (a, b) -> Minus (scan a, scan b)
  | Divide (a, b) -> Divide (scan a, scan b)
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, cs, e) -> Assign (dv, cs, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Var_ref Colour0 -> set_colchan Colour0; Var_ref Rasc
  | Var_ref Alpha0 -> set_colchan Alpha0; Var_ref Rasa
  | Var_ref Colour0A0 ->
      set_colchan Colour0A0; if alpha then Var_ref Rasa else Var_ref Rasc
  | Var_ref Colour1 -> set_colchan Colour1; Var_ref Rasc
  | Var_ref Alpha1 -> set_colchan Alpha1; Var_ref Rasa
  | Var_ref Colour1A1 ->
      set_colchan Colour1A1; if alpha then Var_ref Rasa else Var_ref Rasc
  | Var_ref ColourZero ->
      set_colchan ColourZero; if alpha then Var_ref Rasa else Var_ref Rasc
  | Var_ref AlphaBump -> set_colchan AlphaBump; Var_ref Rasa
  | Var_ref AlphaBumpN ->
      set_colchan AlphaBumpN; Var_ref Rasa (* "normalized"? *)
  | Var_ref x -> Var_ref x
  | Texmap (m, c) -> Texmap (m, c)
  | Float x -> Float x
  | Int x -> Int x
  | Select (v, lx) -> Select (scan v, lx)
  | Concat (x, lx) -> Concat (scan x, lx) in
  let expr' = scan expr in
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

(* Rewrite "/ 2" as "* 0.5", integer-valued floats as ints, and rationals as
   floats.  *)

let rec rewrite_rationals = function
    Plus (a, b) -> Plus (rewrite_rationals a, rewrite_rationals b)
  | Minus (a, b) -> Minus (rewrite_rationals a, rewrite_rationals b)
  | Divide (Float a, Float b) -> Float (a /. b)
  | Divide (Int a, Int b) -> Float (Int32.to_float a /. Int32.to_float b)
  | Divide (Float a, Int b) -> Float (a /. Int32.to_float b)
  | Divide (Int a, Float b) -> Float (Int32.to_float a /. b)
  | Divide (a, (Int 2l | Float 2.0)) -> Mult (rewrite_rationals a, Float 0.5)
  | Divide (a, b) -> Divide (rewrite_rationals a, rewrite_rationals b)
  | Mult (a, b) -> Mult (rewrite_rationals a, rewrite_rationals b)
  | Neg a -> Neg (rewrite_rationals a)
  | Clamp a -> Clamp (rewrite_rationals a)
  | Mix (a, b, c) -> Mix (rewrite_rationals a, rewrite_rationals b,
			  rewrite_rationals c)
  | Assign (dv, cs, e) -> Assign (dv, cs, rewrite_rationals e)
  | Ceq (a, b) -> Ceq (rewrite_rationals a, rewrite_rationals b)
  | Cgt (a, b) -> Cgt (rewrite_rationals a, rewrite_rationals b)
  | Clt (a, b) -> Clt (rewrite_rationals a, rewrite_rationals b)
  | Ternary (a, b, c) -> Ternary (rewrite_rationals a, rewrite_rationals b,
				  rewrite_rationals c)
  | Float 4.0 -> Int 4l
  | Float 2.0 -> Int 2l
  | Float 1.0 -> Int 1l
  | Float 0.0 -> Int 0l
  | Float x -> Float x
  | Int x -> Int x
  | Var_ref x -> Var_ref x
  | Texmap (m, c) -> Texmap (m, c)
  | Select (x, lx) -> Select (rewrite_rationals x, lx)
  | Concat (x, lx) -> Concat (rewrite_rationals x, lx)

(* FIXME: The "D" input has more significant bits than the A, B and C inputs:
   10-bit signed versus 8-bit unsigned.  This rewriting function doesn't really
   understand that, so we may lose precision.  Maybe fix by introducing a new
   "accumulate" operator?  *)

let rec rewrite_expr = function
    Var_ref x ->
      Mult (Plus (Plus (Var_ref x,
			Plus (Mult (Minus (Int 1l, Int 0l), Int 0l),
			      Mult (Int 0l, Int 0l))),
		  Int 0l),
	    Int 1l)
  | Int x ->
      Mult (Plus (Plus (Int x,
			Plus (Mult (Minus (Int 1l, Int 0l), Int 0l),
			      Mult (Int 0l, Int 0l))),
		  Int 0l),
	    Int 1l)
  | Float x ->
      Mult (Plus (Plus (Float x,
			Plus (Mult (Minus (Int 1l, Int 0l), Int 0l),
			      Mult (Int 0l, Int 0l))),
		  Int 0l),
	    Int 1l)
  | Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b)) when c = c2 ->
      Mult (Plus (Plus (Int 0l,
			Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
		  Int 0l),
	    Int 1l)
  | Plus (Plus (d, Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
	  tevbias) when c = c2 ->
      Mult (Plus (Plus (d, Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
		  tevbias),
	    Int 1l)
  | Plus (Minus (d, Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
	  tevbias) when c = c2 ->
      Mult (Plus (Minus (d, Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
		  tevbias),
	    Int 1l)
  | Mult (Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b)),
          tevscale) when c = c2 ->
      Mult (Plus (Plus (Int 0l,
			Plus (Mult (Minus (Int 1l, c), a), Mult (c2, b))),
		  Int 0l),
	    tevscale)
  | Ternary (a, b, c) -> Plus (Int 0l, Ternary (a, b, c))
  | Clamp expr -> Clamp (rewrite_expr expr)
  | x -> x

let string_of_var_param = function
    Cprev -> "cprev"
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
  | Extracted_const -> "extracted_const"

let string_of_laneselect lsa ~reverse =
  Array.fold_left
    (fun acc lane -> match lane with
       R -> if reverse then "r" ^ acc else acc ^ "r"
     | G -> if reverse then "g" ^ acc else acc ^ "g"
     | B -> if reverse then "b" ^ acc else acc ^ "b"
     | A -> if reverse then "a" ^ acc else acc ^ "a"
     | X -> if reverse then "?" ^ acc else acc ^ "?")
    ""
    lsa

let string_of_destvar = function
    Tevprev -> "tevprev"
  | Tevreg0 -> "tevreg0"
  | Tevreg1 -> "tevreg1"
  | Tevreg2 -> "tevreg2"

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
  | Var_ref r -> Buffer.add_string b (string_of_var_param r)
  | Neg a -> Buffer.add_string b "-("; scan a; Buffer.add_char b ')'
  | Clamp a -> Buffer.add_string b "clamp("; scan a; Buffer.add_char b ')'
  | Mix (x, y, z) ->
      Buffer.add_string b "mix("; scan x; Buffer.add_char b ','; scan y;
      Buffer.add_char b ','; scan z; Buffer.add_char b ')'
  | Assign (dv, lsa, e) ->
      Buffer.add_string b (string_of_destvar dv);
      Buffer.add_char b '.';
      Buffer.add_string b (string_of_laneselect lsa ~reverse:false);
      Buffer.add_string b "=";
      scan e
  | Ceq (a, b) -> add_binop a " == " b
  | Cgt (a, b) -> add_binop a " > " b
  | Clt (a, b) -> add_binop a " < " b
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
      Buffer.add_string b (Printf.sprintf "texmap%d[texcoord%d]" x y) in
  scan expr;
  Buffer.contents b

type 'ac stage_info = {
  stage_operation : 'ac tev;
  const_usage : const_setting option;
  texmap : (int * int) option;
  colchan: var_param option;
  tex_swaps : lane_select array option;
  ras_swaps : lane_select array option
}

type stage_col_alpha_parts = {
  mutable colour_part : cvar_setting stage_info option;
  mutable alpha_part : avar_setting stage_info option;
  mutable merged_tex_swaps : lane_select array option;
  mutable merged_ras_swaps : lane_select array option
}

let parse_channel c =
  let sbuf = Lexing.from_channel c in
  Parser.stage_defs Lexer.token sbuf

let num_stages stage_defs =
  List.fold_right
    (fun (sn, _) acc -> if sn + 1 > acc then sn + 1 else acc)
    stage_defs
    0

let print_num_stages ns =
  Printf.printf "GX_SetNumTevStages (%d);\n" ns

exception Cant_match_stage of int

let compile_expr stage orig_expr ~alpha ac_var_of_expr =
  let expr = rewrite_rationals orig_expr in
  let expr = rewrite_mix expr in
  let expr, const_extr = rewrite_const expr ~alpha in
  let expr, texmap_texcoord = rewrite_texmaps expr ~alpha in
  let expr, colchan = rewrite_colchans expr ~alpha in
  let expr, texswap, rasswap = rewrite_swap_tables expr ~alpha in
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
	texmap = texmap_texcoord;
	colchan = colchan;
	tex_swaps = texswap;
	ras_swaps = rasswap
      }
  | None ->
      Printf.fprintf stderr "Attempting to match: '%s'\n"
		     (string_of_expression expr);
      Printf.fprintf stderr "Rewritten from original: '%s'\n"
		     (string_of_expression orig_expr);
      raise (Cant_match_stage stage)

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
    match col_order.texmap, alpha_order.texmap with
      Some (ctm, ctc), Some (atm, atc) when ctm = atm && ctc = atc ->
        Some (ctm, ctc)
    | Some x, None -> Some x
    | None, Some x -> Some x
    | None, None -> None
    | _ -> failwith "Invalid texmap/texcoord combination" in
  combined_texmap, combined_colchan

let array_of_stages stage_defs ns =
  let arr =
    Array.init ns
      (fun _ ->
        { colour_part = None; alpha_part = None; merged_tex_swaps = None;
	  merged_ras_swaps = None }) in
  List.iter
    (fun (sn, stage_exprs) ->
      try
        List.iter
          (fun stage_expr ->
            let stage_expr = default_assign stage_expr in
            match stage_expr with
	      Assign (_, [| A |], _) ->
		let comp =
		  compile_expr sn stage_expr ~alpha:true avar_of_expr in
		arr.(sn).alpha_part <- Some comp
	    | Assign (_, [| R; G; B |], _) ->
		let comp =
		  compile_expr sn stage_expr ~alpha:false cvar_of_expr in
		arr.(sn).colour_part <- Some comp
	    | Assign (_, [| R; G; B; A |], _) ->
		(* Not entirely sure if it's sensible to allow this.  *)
		let ccomp = compile_expr sn stage_expr ~alpha:false cvar_of_expr
		and acomp =
		  compile_expr sn stage_expr ~alpha:true avar_of_expr in
		arr.(sn).alpha_part <- Some acomp;
		arr.(sn).colour_part <- Some ccomp
	    | _ -> failwith "Bad stage expression")
	stage_exprs
      with ((Bad_avar e) as exc) ->
        let s = string_of_expression e in
	Printf.fprintf stderr "In '%s':\n" s;
	raise exc)
    stage_defs;
  arr

let print_swaps snum t_or_r lsa =
  Printf.printf "stage %d: %s swaps: %s\n" snum t_or_r
		(string_of_laneselect lsa ~reverse:false)

let set_swap_don't_cares sel ~alpha =
  match sel with
    [| a |] -> if alpha then [| X; X; X; a |] else [| a; X; X; X |]
  | [| a; b |] -> [| a; b; X; X |]
  | [| a; b; c |] -> [| a; b; c; X |]
  | [| a; b; c; d |] -> [| a; b; c; d |]
  | _ -> failwith "Unexpected swizzles"

exception Swizzle_collision

let merge_swaps a b =
  let a' = set_swap_don't_cares a ~alpha:false
  and b' = set_swap_don't_cares b ~alpha:true in
  Array.init 4
    (fun i ->
      match a'.(i), b'.(i) with
        (R | G | B | A as c), X -> c
      | X, (R | G | B | A as c) -> c
      | X, X -> X
      | a, b when a = b -> a
      | _, _ -> raise Swizzle_collision)

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

let unique_swaps swaps unique_list =
  if swaps = [| X; X; X; X |]
     || List.exists (swap_matches swaps) unique_list then
    unique_list
  else
    swaps :: unique_list

let gather_swap_tables stage_def_arr =
  let swap_tables = ref [] in
  for i = 0 to Array.length stage_def_arr - 1 do
    let cpart = stage_def_arr.(i).colour_part
    and apart = stage_def_arr.(i).alpha_part in
    let texswaps, rasswaps =
      match cpart, apart with
	Some cpart, Some apart ->
          let texswaps =
	    match cpart.tex_swaps, apart.tex_swaps with
	      Some c_texswaps, Some a_texswaps ->
		merge_swaps c_texswaps a_texswaps
	    | Some c_texswaps, None ->
	        set_swap_don't_cares c_texswaps ~alpha:false
	    | None, Some a_texswaps ->
	        set_swap_don't_cares a_texswaps ~alpha:true
	    | None, None -> [| X; X; X; X |]
	  and rasswaps =
	    match cpart.ras_swaps, apart.ras_swaps with
	      Some c_rasswaps, Some a_rasswaps ->
		merge_swaps c_rasswaps a_rasswaps
	    | Some c_rasswaps, None ->
	        set_swap_don't_cares c_rasswaps ~alpha:false
	    | None, Some a_rasswaps ->
	        set_swap_don't_cares a_rasswaps ~alpha:true
	    | None, None -> [| X; X; X; X |] in
	  texswaps, rasswaps
      | Some cpart, None ->
          let texswaps =
	    match cpart.tex_swaps with
	      Some c_texswaps -> set_swap_don't_cares c_texswaps ~alpha:false
	    | None -> [| X; X; X; X |]
          and rasswaps =
	    match cpart.ras_swaps with
	      Some c_rasswaps -> set_swap_don't_cares c_rasswaps ~alpha:false
	    | None -> [| X; X; X; X |] in
	  texswaps, rasswaps
      | None, Some apart ->
          let texswaps =
	    match apart.tex_swaps with
	      Some a_texswaps -> set_swap_don't_cares a_texswaps ~alpha:true
	    | None -> [| X; X; X; X |]
          and rasswaps =
	    match apart.ras_swaps with
	      Some a_rasswaps -> set_swap_don't_cares a_rasswaps ~alpha:true
	    | None -> [| X; X; X; X |] in
	  texswaps, rasswaps
       | None, None ->
           [| X; X; X; X |], [| X; X; X; X |] in
    swap_tables := unique_swaps texswaps !swap_tables;
    swap_tables := unique_swaps rasswaps !swap_tables;
    stage_def_arr.(i).merged_tex_swaps <- Some texswaps;
    stage_def_arr.(i).merged_ras_swaps <- Some rasswaps
  done;
  Array.of_list !swap_tables

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

let print_const_setup stage cst ~alpha =
  if alpha then
    Printf.printf "GX_SetTevKAlphaSel (%s, %s);\n" (string_of_stagenum stage)
      (string_of_const cst true)
  else
    Printf.printf "GX_SetTevKColorSel (%s, %s);\n" (string_of_stagenum stage)
      (string_of_const cst false)

(* Print a normal (direct) texture lookup order.  *)

let print_tev_order stage_num texmap colchan =
  let tm, tc = match texmap with
    None -> "GX_TEXMAP_NULL", "GX_TEXCOORDNULL"
  | Some (tm, tc) ->
      "GX_TEXMAP" ^ string_of_int tm, "GX_TEXCOORD" ^ string_of_int tc
  and cc = match colchan with
    None -> "GX_COLORNULL"
  | Some c -> string_of_colour_chan c in
  Printf.printf "GX_SetTevOrder (%s, %s, %s, %s);\n"
    (string_of_stagenum stage_num) tc tm cc

let print_tev_setup stage_num stage_op string_of_ac_input ~alpha =
  let acin, acop = if alpha then
    "GX_SetTevAlphaIn", "GX_SetTevAlphaOp"
  else
    "GX_SetTevColorIn", "GX_SetTevColorOp" in
  match stage_op with
    Arith ar -> 
      Printf.printf "%s (%s, %s, %s, %s, %s);\n" acin
        (string_of_stagenum stage_num) (string_of_ac_input ar.a)
	(string_of_ac_input ar.b) (string_of_ac_input ar.c)
	(string_of_ac_input ar.d);
      Printf.printf "%s (%s, %s, %s, %s, %s, %s);\n" acop
        (string_of_stagenum stage_num) (string_of_tev_op ar.op)
	(string_of_bias ar.bias) (string_of_scale ar.scale)
	(string_of_clamp ar.clamp) (string_of_result ar.result)
  | Comp cmp ->
      Printf.printf "%s (%s, %s, %s, %s, %s);\n" acin
        (string_of_stagenum stage_num) (string_of_ac_input cmp.cmp_a)
	(string_of_ac_input cmp.cmp_b) (string_of_ac_input cmp.cmp_c)
	(string_of_ac_input cmp.cmp_d);
      Printf.printf
        "%s (%s, %s, GX_TB_ZERO, GX_CS_SCALE_1, GX_FALSE, %s);\n" acop
        (string_of_stagenum stage_num) (string_of_cmp_op cmp.cmp_op)
	(string_of_result cmp.cmp_result)

let string_of_chan = function
    R | X -> "GX_CH_RED"
  | G -> "GX_CH_GREEN"
  | B -> "GX_CH_BLUE"
  | A -> "GX_CH_ALPHA"

let string_of_swap_table n =
  "GX_TEV_SWAP" ^ (string_of_int n)

exception Too_many_swap_tables

let print_swap_tables swap_tables =
  if Array.length swap_tables > 4 then
    raise Too_many_swap_tables;
  Array.iteri
    (fun i tab ->
      Printf.printf "GX_SetSwapModeTable (%s, %s, %s, %s, %s);\n"
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

let print_swap_setup stagenum swap_tables tex_swaps ras_swaps =
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
    Printf.printf "GX_SetTevSwapMode (%s, %s, %s);\n"
      (string_of_stagenum stagenum) (string_of_swap_table rnum')
      (string_of_swap_table tnum')
  end

let _ =
  let parsed_stages = parse_channel stdin in
  let num_stages = num_stages parsed_stages in
  print_num_stages num_stages;
  print_newline ();
  let stage_arr = array_of_stages parsed_stages num_stages in
  let swap_tables = gather_swap_tables stage_arr in
  print_swap_tables swap_tables;
  print_newline ();
  for i = 0 to num_stages - 1 do
    let texmap, colchan =
      match stage_arr.(i).colour_part, stage_arr.(i).alpha_part with
        None, Some ap -> ap.texmap, ap.colchan
      | Some cp, None -> cp.texmap, cp.colchan
      | Some cp, Some ap -> combine_tev_orders cp ap
      | None, None -> failwith "Missing tev stage!" in
    print_swap_setup i swap_tables stage_arr.(i).merged_tex_swaps
		     stage_arr.(i).merged_ras_swaps;
    print_tev_order i texmap colchan;
    begin match stage_arr.(i).colour_part with
      Some cpart ->
        begin match cpart.const_usage with
	  Some cst -> print_const_setup i cst ~alpha:false
	| None -> ()
	end;
        print_tev_setup i cpart.stage_operation string_of_tev_input
			~alpha:false
    | None -> ()
    end;
    begin match stage_arr.(i).alpha_part with
      Some apart ->
        begin match apart.const_usage with
	  Some cst -> print_const_setup i cst ~alpha:true
	| None -> ()
	end;
        print_tev_setup i apart.stage_operation string_of_tev_alpha_input
			~alpha:true
    | None -> ()
    end;
    print_newline ()
  done
