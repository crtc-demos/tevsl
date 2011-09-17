type expr =
    Int of int32
  | Float of float
  | Plus of expr * expr
  | S10 of expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Matmul of expr * expr
  | Divide of expr * expr
  | Modulus of expr * expr
  | Vec2 of expr * expr
  | Vec3 of expr * expr * expr
  | Var_ref of var_param
  | Neg of expr
  | Clamp of expr
  | Mix of expr * expr * expr
  | Assign of dest_var * lane_select array * expr
  | Ceq of expr * expr
  | Cgt of expr * expr
  | Clt of expr * expr
  | Select of expr * lane_select array
  | Concat of expr * lane_select array
  | Ternary of expr * expr * expr
  | Texmap of int * expr
  | Texcoord of int
  | Indscale of int
  | Indmtx of ind_matrix
  | D_indmtx of dyn_ind_matrix * expr
  | Itexcoord
  | Z
  | Zbits of int * expr
  | CVar of string
  | Protect of expr  (* Don't map child expr in map_expr.  *)

(* X for "don't care".  *)
and lane_select = R | G | B | A | LS_S | LS_T | X

and var_param =
    Tev
  | Cprev
  | Aprev
  | CR of int
  | C0
  | A0
  | C1
  | A1
  | C2
  | A2
  | K0
  | K1
  | K2
  | K3
  | Chan0
  | Chan1
  | Colour0
  | Alpha0
  | Colour0A0
  | Colour1
  | Alpha1
  | Colour1A1
  | ColourZero
  | AlphaBump
  | AlphaBumpN
  | Texture
  | Raster
  | Texc
  | Texa
  | Rasc
  | Rasa
  | Extracted_const

and dest_var =
    Tevprev
  | Tevreg0
  | Tevreg1
  | Tevreg2
  | Itexc_dst
  | Z_dst

and const_setting =
    KCSEL_1
  | KCSEL_7_8
  | KCSEL_3_4
  | KCSEL_5_8
  | KCSEL_1_2
  | KCSEL_3_8
  | KCSEL_1_4
  | KCSEL_1_8
  | KCSEL_K0
  | KCSEL_K1
  | KCSEL_K2
  | KCSEL_K3
  | KCSEL_K0_R
  | KCSEL_K1_R
  | KCSEL_K2_R
  | KCSEL_K3_R
  | KCSEL_K0_G
  | KCSEL_K1_G
  | KCSEL_K2_G
  | KCSEL_K3_G
  | KCSEL_K0_B
  | KCSEL_K1_B
  | KCSEL_K2_B
  | KCSEL_K3_B
  | KCSEL_K0_A
  | KCSEL_K1_A
  | KCSEL_K2_A
  | KCSEL_K3_A

and ind_matrix =
    Ind_matrix of int
  | No_matrix

and dyn_ind_matrix =
    Dyn_S
  | Dyn_T

(* 
    TevColorIn: a b c d
    TevColorOp: tevop tevbias tevscale clamp tevregid

    regular operation:

    tevregid = (d [+/-] ((1-c)*a + c*b) + tevbias) * tevscale
*)

type 'ac_var_setting arith_op =
  {
    a : 'ac_var_setting;
    b : 'ac_var_setting;
    c : 'ac_var_setting;
    d : 'ac_var_setting;
    op : tev_op;
    bias : bias_values;
    scale : scale_values;
    clamp : bool;
    result : dest_var
  }

(*
    tevregid = d + ((a OP b) ? c : 0)
*)

and 'ac_var_setting compare_op =
  {
    cmp_a : 'ac_var_setting;
    cmp_b : 'ac_var_setting;
    cmp_c : 'ac_var_setting;
    cmp_d : 'ac_var_setting;
    cmp_op : tev_cmp_op;
    cmp_result : dest_var
  }

and cvar_setting =
    CC_cprev
  | CC_aprev
  | CC_c0
  | CC_a0
  | CC_c1
  | CC_a1
  | CC_c2
  | CC_a2
  | CC_texc
  | CC_texa
  | CC_rasc
  | CC_rasa
  | CC_one
  | CC_half
  | CC_const
  | CC_zero

and avar_setting =
    CA_aprev
  | CA_a0
  | CA_a1
  | CA_a2
  | CA_texa
  | CA_rasa
  | CA_const
  | CA_zero

and tev_op =
    OP_add
  | OP_sub

and tev_cmp_op =
    CMP_r8_gt
  | CMP_r8_eq
  | CMP_gr16_gt
  | CMP_gr16_eq
  | CMP_bgr24_gt
  | CMP_bgr24_eq
  | CMP_rgb8_gt
  | CMP_rgb8_eq
  | CMP_a8_gt  (* For alpha channel, same encoding as rgb8.  *)
  | CMP_a8_eq

and bias_values =
    TB_zero
  | TB_addhalf
  | TB_subhalf

and scale_values =
    CS_scale_1
  | CS_scale_2
  | CS_scale_4
  | CS_divide_2

and 'av_tev tev =
    Arith of 'av_tev arith_op
  | Comp of 'av_tev compare_op

exception Parsing_stage of Lexing.position * Lexing.position

exception Bad_dest_var

let destvar_of_var = function
    Tev -> Tevprev
  | CR 0 -> Tevreg0
  | CR 1 -> Tevreg1
  | CR 2 -> Tevreg2
  | _ -> raise Bad_dest_var
