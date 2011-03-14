open Expr

exception Bad_value

let bias_of_expr = function
    Int 0l | Float 0.0 -> TB_zero
  | Float 0.5 -> TB_addhalf
  | Float (-0.5) -> TB_subhalf
  | _ -> raise Bad_value

let cvar_of_expr = function
    Var_ref Cprev -> CC_cprev
  | Var_ref Aprev -> CC_aprev
  | Var_ref C0 -> CC_c0
  | Var_ref A0 -> CC_a0
  | Var_ref C1 -> CC_c1
  | Var_ref A1 -> CC_a1
  | Var_ref C2 -> CC_c2
  | Var_ref A2 -> CC_a2
  | Var_ref Texc -> CC_texc
  | Var_ref Texa -> CC_texa
  | Var_ref Rasc -> CC_rasc
  | Var_ref Rasa -> CC_rasa
  | Int 1l | Float 1.0 -> CC_one
  | Float 0.5 -> CC_half
  | Int 0l | Float 0.0 -> CC_zero
  | _ -> raise Bad_value

let scale_of_expr = function
    Int 1l | Float 1.0 -> CS_scale_1
  | Int 2l | Float 2.0 -> CS_scale_2
  | Int 4l | Float 4.0 -> CS_scale_4
  | Float 0.5 -> CS_divide_2
  | _ -> raise Bad_value

let arith_op_of_expr = function
    Assign (dv, Mult (Plus
		       (Plus
		         (d, Plus (Mult (Minus (Int 1l, c), a),
				   Mult (c2, b))),
		        tevbias),
		      tevscale)) when c = c2 ->
      { a = cvar_of_expr a;
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
      { a = cvar_of_expr a;
        b = cvar_of_expr b;
	c = cvar_of_expr c;
	d = cvar_of_expr d;
	op = OP_sub;
	bias = bias_of_expr tevbias;
	scale = scale_of_expr tevscale;
	clamp = false;
	result = dv }

exception Unmatched_expr

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

let identity_variants e =
  let rec build_list e all_variants =
    match e with
      Plus (a, b) ->
        let a_list = build_list a []
	and b_list = build_list b [] in
	List.fold_right
	  (fun a_elem a_acc ->
	    List.fold_right
	      (fun b_elem b_acc ->
	        Plus (a_elem, b_elem) :: b_acc)
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
	        Mult (a_elem, b_elem) :: b_acc)
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
     | x ->
         Mult (x, Int 1l) :: Plus (x, Int 0l) :: x :: all_variants
  in
    build_list e []

let default_assign = function
    Assign (dv, x) as d -> d
  | x -> Assign (Tevprev, x)

let rewrite_expr = function
    Assign (dv, Var_ref x) ->
      Assign (dv, Mult (Plus
			 (Plus
			   (Int 0l,
			    Plus (Mult (Minus (Int 1l, Int 0l), Var_ref x),
				  Mult (Int 0l, Int 0l))),
			  Int 0l),
			Int 1l))
  | Assign (dv, Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
		      Mult (Var_ref c2, Var_ref b))) when c = c2 ->
      Assign (dv, Mult (Plus
			 (Plus
			   (Int 0l,
			    Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				  Mult (Var_ref c2, Var_ref b))),
			  Int 0l),
			Int 1l))
  | Assign (dv, Mult (Plus
		       (Plus
		         (Var_ref d,
			  Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				Mult (Var_ref c2, Var_ref b))),
		        tevbias),
		     tevscale)) when c = c2 ->
      Assign (dv, Mult (Plus
			 (Plus
			   (Var_ref d,
			    Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				  Mult (Var_ref c2, Var_ref b))),
		          tevbias),
			tevscale))
  | Assign (dv, Mult (Plus
		       (Minus
		         (Var_ref d,
			  Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				Mult (Var_ref c2, Var_ref b))),
		        tevbias),
		     tevscale)) when c = c2 ->
      Assign (dv, Mult (Plus
			 (Minus
			   (Var_ref d,
			    Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				  Mult (Var_ref c2, Var_ref b))),
		          tevbias),
			tevscale))
  | Assign (dv, Plus (Plus
		       (Var_ref d,
			Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
			      Mult (Var_ref c2, Var_ref b))),
		      tevbias)) when c = c2 ->
      Assign (dv, Mult (Plus
			 (Plus
			   (Var_ref d,
			    Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				  Mult (Var_ref c2, Var_ref b))),
		          tevbias),
			Int 1l))
  | Assign (dv, Plus (Minus
		       (Var_ref d,
			Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
			      Mult (Var_ref c2, Var_ref b))),
		      tevbias)) when c = c2 ->
      Assign (dv, Mult (Plus
			 (Minus
			   (Var_ref d,
			    Plus (Mult (Minus (Int 1l, Var_ref c), Var_ref a),
				  Mult (Var_ref c2, Var_ref b))),
		          tevbias),
			Int 1l))
  | _ -> raise Unmatched_expr

let parseme s =
  let sbuf = Lexing.from_string s in
  let stage, expr = Parser.stage_def Lexer.token sbuf in
  let expr = default_assign expr in
  let id_variants = identity_variants expr in
    List.fold_right
      (fun id_var solution ->
        match solution with
	  Some x as y -> y
	| None ->
	    let comm_variants = commutative_variants id_var in
	    List.fold_right
	      (fun variant found ->
		match found with
        	  Some x as y -> y
		| None ->
        	    try
        	      Some (stage, arith_op_of_expr (rewrite_expr variant))
		    with Unmatched_expr ->
		      None)
	      comm_variants
	      solution)
      id_variants
      None
