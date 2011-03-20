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

let rewrite_const expr =
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
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, e) -> Assign (dv, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Float 1.0 -> set_const KCSEL_1
  | Float 0.875 -> set_const KCSEL_7_8
  | Float 0.75 -> set_const KCSEL_3_4
  | Float 0.625 -> set_const KCSEL_5_8
  (* | Float 0.5 -> set_const KCSEL_1_2  why do we ever need this?  *)
  | Float 0.375 -> set_const KCSEL_3_8
  | Float 0.25 -> set_const KCSEL_1_4
  | Float 0.125 -> set_const KCSEL_1_8
  | Var_ref K0 -> set_const KCSEL_K0
  | Var_ref K1 -> set_const KCSEL_K1
  | Var_ref K2 -> set_const KCSEL_K2
  | Var_ref K3 -> set_const KCSEL_K3
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
  | Float x -> Float x
  | Int x -> Int x
  | Var_ref x -> Var_ref x
  | Select (a, la) -> Select (scan a, la) in
  let expr' = scan expr in
  expr', !which_const

exception Incompatible_swaps

let rewrite_swap_tables expr =
  let texswap = ref None
  and rasswap = ref None in
  let set_tex t =
    match !texswap with
      None ->
        begin match t with
	  [| R |]
	| [| G; R |]
	| [| B; G; R |]
	| [| A |] -> ()
	| _ -> texswap := Some t
	end
    | Some o -> if o <> t then raise Incompatible_swaps in
  let set_ras r =
    match !rasswap with
      None ->
        begin match r with
	  [| R |]
	| [| G; R |]
	| [| B; G; R |]
	| [| A |] -> ()
	| _ -> rasswap := Some r
	end
    | Some o -> if o <> r then raise Incompatible_swaps in
  let default_swap = function
    [| (R | G | B) |] -> [| R |]
  | [| _; _ |] -> [| G; R |]
  | [| _; _; _ |] -> [| B; G; R |]
  | [| A |] -> [| A |] in
  let rec scan = function
    Plus (a, b) -> Plus (scan a, scan b)
  | Minus (a, b) -> Minus (scan a, scan b)
  | Divide (a, b) -> Divide (scan a, scan b)
  | Mult (a, b) -> Mult (scan a, scan b)
  | Neg a -> Neg (scan a)
  | Clamp a -> Clamp (scan a)
  | Mix (a, b, c) -> Mix (scan a, scan b, scan c)
  | Assign (dv, e) -> Assign (dv, scan e)
  | Ceq (a, b) -> Ceq (scan a, scan b)
  | Cgt (a, b) -> Cgt (scan a, scan b)
  | Clt (a, b) -> Clt (scan a, scan b)
  | Ternary (a, b, c) -> Ternary (scan a, scan b, scan c)
  | Var_ref x -> Var_ref x
  | Float x -> Float x
  | Int x -> Int x
  | Select (Var_ref Texc, lx) ->
      set_tex lx; Select (Var_ref Texc, default_swap lx)
  | Select (Var_ref Texa, lx) ->
      set_tex lx; Select (Var_ref Texa, default_swap lx)
  | Select (Var_ref Rasc, lx) ->
      set_ras lx; Select (Var_ref Rasc, default_swap lx)
  | Select (Var_ref Rasa, lx) ->
      set_ras lx; Select (Var_ref Rasa, default_swap lx)
  | Select (x, lx) -> Select (scan x, lx) in
  let expr' = scan expr in
  expr', !texswap, !rasswap

exception Unmatched_expr

let rec arith_op_of_expr = function
    Assign (dv, Mult (Plus
		       (Plus
		         (d, Plus (Mult (Minus (Int 1l, c), a),
				   Mult (c2, b))),
		        tevbias),
		      tevscale)) when c = c2 ->
      Arith { a = cvar_of_expr a;
              b = cvar_of_expr b;
	      c = cvar_of_expr c;
	      d = cvar_of_expr d;
	      op = OP_add;
	      bias = bias_of_expr tevbias;
	      scale = scale_of_expr tevscale;
	      clamp = false;
	      result = dv }
  | Assign (dv, Mult (Plus
		       (Minus
			 (d, Plus (Mult (Minus (Int 1l, c), a),
				   Mult (c2, b))),
		        tevbias),
		      tevscale)) when c = c2 ->
      Arith { a = cvar_of_expr a;
              b = cvar_of_expr b;
	      c = cvar_of_expr c;
	      d = cvar_of_expr d;
	      op = OP_sub;
	      bias = bias_of_expr tevbias;
	      scale = scale_of_expr tevscale;
	      clamp = false;
	      result = dv }
  | Assign (dv, Plus (d, Ternary (Cgt (Select (a, [| R |]),
				       Select (b, [| R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_r8_gt;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Ceq (Select (a, [| R |]),
				       Select (b, [| R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_r8_eq;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Cgt (Select (a, [| G; R |]),
				       Select (b, [| G; R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_gr16_gt;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Ceq (Select (a, [| G; R |]),
				       Select (b, [| G; R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_gr16_eq;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Cgt (Select (a, [| B; G; R |]),
				       Select (b, [| B; G; R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_bgr24_gt;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Ceq (Select (a, [| B; G; R |]),
				       Select (b, [| B; G; R |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_bgr24_eq;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Cgt (Select (a, [||]),
				       Select (b, [||])), c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_rgb8_gt;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Ceq (Select (a, [||]), Select (b, [||])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_rgb8_eq;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Cgt (Select (a, [| A |]),
				       Select (b, [| A |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_rgb8_gt;
	     cmp_result = dv }
  | Assign (dv, Plus (d, Ternary (Ceq (Select (a, [| A |]),
				       Select (b, [| A |])),
				  c, Int 0l))) ->
      Comp { cmp_a = cvar_of_expr a;
	     cmp_b = cvar_of_expr b;
	     cmp_c = cvar_of_expr c;
	     cmp_d = cvar_of_expr d;
	     cmp_op = CMP_rgb8_eq;
	     cmp_result = dv }
  | Assign (dv, Clamp expr) ->
      let inner = arith_op_of_expr (Assign (dv, expr)) in
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
     | Assign (dv, a) ->
        let a_list = build_list a [] in
	List.fold_right
	  (fun a_elem a_acc -> Assign (dv, a_elem) :: a_acc)
	  a_list
	  all_variants
     | x -> [x]
  in
    build_list e []

let default_assign = function
    Assign (dv, x) as d -> d
  | x -> Assign (Tevprev, x)

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
  | Assign (dv, e) -> Assign (dv, rewrite_mix e)
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
  | Assign (dv, e) -> Assign (dv, rewrite_rationals e)
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
  | Select (x, lx) -> Select (rewrite_rationals x, lx)

let rec rewrite_expr = function
    Var_ref x ->
      Mult (Plus (Plus (Int 0l,
			Plus (Mult (Minus (Int 1l, Int 0l), Var_ref x),
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

let parseme s =
  let sbuf = Lexing.from_string s in
  let stage, expr = Parser.stage_def Lexer.token sbuf in
  let expr = default_assign expr in
  let expr = rewrite_rationals expr in
  let expr = rewrite_mix expr in
  let expr, const_extr = rewrite_const expr in
  let expr, texswap, rasswap = rewrite_swap_tables expr in
  let comm_variants = commutative_variants expr in
  let matched = List.fold_right
    (fun variant found ->
      match found with
        Some x as y -> y
      | None ->
          try
	    match variant with
	      Assign (dv, expr) ->
	        let expr' = rewrite_expr expr in
                Some (stage, arith_op_of_expr (Assign (dv, expr')))
	    | _ -> raise Unmatched_expr
	  with Unmatched_expr ->
	    None)
    comm_variants
    None in
  matched, const_extr, texswap, rasswap
